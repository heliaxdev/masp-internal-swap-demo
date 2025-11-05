use std::collections::BTreeMap;
use std::path::Path;

use group::GroupEncoding;
use masp_note_encryption::ENC_CIPHERTEXT_SIZE;
use masp_note_encryption::EphemeralKeyBytes;
use masp_note_encryption::ExtractedCommitmentBytes;
use masp_note_encryption::ShieldedOutput as NoteEncShieldedOutput;
use masp_primitives::asset_type::AssetType;
use masp_primitives::consensus::MainNetwork;
use masp_primitives::memo::MemoBytes;
use masp_primitives::merkle_tree::CommitmentTree;
use masp_primitives::merkle_tree::IncrementalWitness;
use masp_primitives::sapling::Diversifier;
use masp_primitives::sapling::Node;
use masp_primitives::sapling::Note;
use masp_primitives::sapling::NullifierDerivingKey;
use masp_primitives::sapling::PaymentAddress;
use masp_primitives::sapling::Rseed;
use masp_primitives::sapling::ViewingKey;
use masp_primitives::sapling::keys::ExpandedSpendingKey;
use masp_primitives::sapling::keys::FullViewingKey;
use masp_primitives::sapling::keys::OutgoingViewingKey;
use masp_primitives::sapling::note_encryption::SaplingDomain;
use masp_primitives::sapling::note_encryption::sapling_note_encryption;
use masp_primitives::sapling::note_encryption::{
    PreparedIncomingViewingKey, try_sapling_note_decryption,
};
use masp_primitives::transaction::builder::Builder;
use masp_primitives::transaction::components::TxOut;
use masp_primitives::transaction::components::amount::ValueSum;
use masp_primitives::transaction::components::sapling::builder::RngBuildParams;
use masp_primitives::transaction::components::transparent::builder::TransparentBuilder;
use masp_primitives::transaction::fees::fixed::FeeRule;
use masp_primitives::transaction::sighash;
use masp_primitives::transaction::txid::TxIdDigester;
use masp_primitives::transaction::{Authorization, Authorized, TransactionData, Unauthorized};
use masp_primitives::zip32::sapling::ExtendedSpendingKey;
use masp_proofs::prover::LocalTxProver;
use masp_proofs::sapling::BatchValidator;

fn main() {
    const DIVERSIFIER: Diversifier = Diversifier([0xa; 11]);

    // alice's keys
    let sk_a = ExpandedSpendingKey::from_spending_key(b"alice");
    let vk_a = FullViewingKey::from_expanded_spending_key(&sk_a).vk;
    let a_sk = ExpandedSpendingKey::from_spending_key(b"alice ephemeral a");
    let x_sk = ExpandedSpendingKey::from_spending_key(b"alice ephemeral x");
    let a_vk = FullViewingKey::from_expanded_spending_key(&a_sk).vk;
    let x_vk = FullViewingKey::from_expanded_spending_key(&x_sk).vk;

    // bob's keys
    let _sk_b = ExpandedSpendingKey::from_spending_key(b"bob");
    let _vk_b = FullViewingKey::from_expanded_spending_key(&_sk_b).vk;
    let b_sk = ExpandedSpendingKey::from_spending_key(b"bob ephemeral b");
    let y_sk = ExpandedSpendingKey::from_spending_key(b"bob ephemeral y");
    let b_vk = FullViewingKey::from_expanded_spending_key(&b_sk).vk;
    let y_vk = FullViewingKey::from_expanded_spending_key(&y_sk).vk;

    // alice's receiving vk
    let vk_ay = ViewingKey {
        ak: a_vk.ak + y_vk.ak,
        nk: NullifierDerivingKey(a_vk.nk.0 + &y_vk.nk.0),
    };
    // bob's receiving vk
    let vk_bx = ViewingKey {
        ak: b_vk.ak + x_vk.ak,
        nk: NullifierDerivingKey(b_vk.nk.0 + &x_vk.nk.0),
    };

    println!(
        "pk_ay = {:#?}",
        vk_ay.to_payment_address(DIVERSIFIER).unwrap().pk_d()
    );
    println!(
        "pk_bx = {:#?}",
        vk_bx.to_payment_address(DIVERSIFIER).unwrap().pk_d()
    );

    // recover alice's spending key
    let sk_ay = recover_spending_key(&a_sk, &y_sk);
    // recover bob's spending key
    let sk_bx = recover_spending_key(&b_sk, &x_sk);

    println!("sk_ay = {:#?}", (&sk_ay.expsk.ask, &sk_ay.expsk.nsk));
    println!("sk_bx = {:#?}", (&sk_bx.expsk.ask, &sk_bx.expsk.nsk));

    // ==================================================

    // start with an empty tree
    let mut tree = CommitmentTree::<Node>::empty();

    // simulate bob depositing some tokens to ay
    let asset_y = AssetType::new(b"Asset Y").unwrap();
    let note_y = vk_ay
        .to_payment_address(DIVERSIFIER)
        .unwrap()
        .create_note(asset_y, 100, rseed(1))
        .unwrap();
    tree.append(note_y.commitment()).unwrap();

    // make sure alice can see the tokens locked by bob
    {
        let note_encryption = sapling_note_encryption::<MainNetwork>(
            None,
            note_y,
            vk_ay.to_payment_address(DIVERSIFIER).unwrap(),
            MemoBytes::empty(),
        );

        let out = ShieldedOutput {
            epk: EphemeralKeyBytes(note_encryption.epk().to_bytes()),
            cmu: note_y.commitment().into_repr(),
            ciphertext: note_encryption.encrypt_note_plaintext(),
        };

        let mut decrypted = trial_decrypt(&vk_ay, std::iter::once(&out));
        assert_eq!(decrypted.len(), 1);

        let (decrypted_note, _, _) = decrypted.remove(&0).unwrap();
        assert_eq!(decrypted_note, note_y);
    }

    // spend note in ay -- send it to alice
    let bundle = {
        let mut params = RngBuildParams::new(rand_core::OsRng);

        let prover = LocalTxProver::new(
            &masp_params_path().join("masp-spend.params"),
            &masp_params_path().join("masp-output.params"),
            &masp_params_path().join("masp-convert.params"),
        );

        let fee = FeeRule::non_standard(ValueSum::zero());
        let wit = IncrementalWitness::from_tree(&tree);

        let mut builder = Builder::new(MainNetwork, 1u32.into());
        builder
            .add_sapling_spend(sk_ay, DIVERSIFIER, note_y, wit.path().unwrap())
            .unwrap();
        builder
            .add_sapling_output(
                None,
                vk_a.to_payment_address(DIVERSIFIER).unwrap(),
                asset_y,
                100,
                MemoBytes::empty(),
            )
            .unwrap();

        builder
            .build(&prover, &fee, &mut rand_core::OsRng, &mut params)
            .unwrap()
            .0
    };

    // verify bundle
    {
        let sighash: [u8; 32] = {
            let unauth = partial_deauthorize(&bundle).unwrap();
            let parts = bundle.digest(TxIdDigester);
            *sighash::signature_hash(&unauth, &sighash::SignableInput::Shielded, &parts).as_ref()
        };
        let params = masp_proofs::load_parameters(
            &masp_params_path().join("masp-spend.params"),
            &masp_params_path().join("masp-output.params"),
            &masp_params_path().join("masp-convert.params"),
        );
        let mut verifier = BatchValidator::new();
        assert!(verifier.check_bundle(bundle.sapling_bundle().unwrap().clone(), sighash));
        assert!(verifier.validate(
            &params.spend_params.vk,
            &params.convert_params.vk,
            &params.output_params.vk,
            rand_core::OsRng
        ));
    }

    // add outputs to tree
    for so in bundle
        .sapling_bundle()
        .map_or(&vec![], |b| &b.shielded_outputs)
    {
        tree.append(Node::from_scalar(so.cmu)).unwrap();
    }

    // trial decrypt bundle
    let decrypted = trial_decrypt(
        &vk_a,
        bundle
            .sapling_bundle()
            .map_or(&vec![], |x| &x.shielded_outputs),
    );
    println!("trial decrypted => {decrypted:#?}");
}

fn rseed(x: u64) -> Rseed {
    let mut buf = [0u8; 32];
    buf[..8].copy_from_slice(&x.to_be_bytes());
    Rseed::AfterZip212(buf)
}

fn recover_spending_key(
    fst: &ExpandedSpendingKey,
    snd: &ExpandedSpendingKey,
) -> ExtendedSpendingKey {
    let mut buf = [0u8; 169];
    let sk = ExpandedSpendingKey {
        ask: fst.ask + snd.ask,
        nsk: fst.nsk + snd.nsk,
        ovk: OutgoingViewingKey([0u8; 32]),
    };
    buf[41..137].copy_from_slice(&sk.to_bytes());
    let Ok(sk) = ExtendedSpendingKey::from_bytes(&buf) else {
        unreachable!()
    };
    sk
}

struct PartialAuthorized;

impl Authorization for PartialAuthorized {
    type SaplingAuth = <Authorized as Authorization>::SaplingAuth;
    type TransparentAuth = <Unauthorized<ExtendedSpendingKey> as Authorization>::TransparentAuth;
}

fn partial_deauthorize(
    tx_data: &TransactionData<Authorized>,
) -> Option<TransactionData<PartialAuthorized>> {
    let transp = tx_data.transparent_bundle().and_then(|x| {
        let mut tb = TransparentBuilder::empty();
        for vin in &x.vin {
            tb.add_input(TxOut {
                asset_type: vin.asset_type,
                value: vin.value,
                address: vin.address,
            })
            .ok()?;
        }
        for vout in &x.vout {
            tb.add_output(&vout.address, vout.asset_type, vout.value)
                .ok()?;
        }
        tb.build()
    });
    if tx_data.transparent_bundle().is_some() != transp.is_some() {
        return None;
    }
    Some(TransactionData::from_parts(
        tx_data.version(),
        tx_data.consensus_branch_id(),
        tx_data.lock_time(),
        tx_data.expiry_height(),
        transp,
        tx_data.sapling_bundle().cloned(),
    ))
}

fn trial_decrypt<'so, I, O>(
    vk: &ViewingKey,
    shielded_outputs: I,
) -> BTreeMap<usize, (Note, PaymentAddress, MemoBytes)>
where
    I: IntoIterator<Item = &'so O>,
    O: NoteEncShieldedOutput<SaplingDomain<MainNetwork>, ENC_CIPHERTEXT_SIZE> + 'so,
{
    let prepared = PreparedIncomingViewingKey::new(&vk.ivk());

    shielded_outputs.into_iter().enumerate().fold(
        BTreeMap::new(),
        |mut accum, (note_pos_offset, so)| {
            // Let's try to see if this viewing key can decrypt latest
            // note
            if let Some(decrypted) =
                try_sapling_note_decryption(&MainNetwork, 1.into(), &prepared, so)
            {
                accum.insert(note_pos_offset, decrypted);
            }
            accum
        },
    )
}

fn masp_params_path() -> &'static Path {
    // osx: /Users/$USER/Library/Application Support/MASPParams
    // linux: $HOME/.masp-params
    env!("MASP_PARAMS_PATH").as_ref()
}

struct ShieldedOutput {
    epk: EphemeralKeyBytes,
    cmu: ExtractedCommitmentBytes,
    ciphertext: [u8; ENC_CIPHERTEXT_SIZE],
}

impl NoteEncShieldedOutput<SaplingDomain<MainNetwork>, ENC_CIPHERTEXT_SIZE> for ShieldedOutput {
    fn ephemeral_key(&self) -> EphemeralKeyBytes {
        EphemeralKeyBytes(self.epk.0)
    }

    fn cmstar_bytes(&self) -> ExtractedCommitmentBytes {
        self.cmu
    }

    fn enc_ciphertext(&self) -> &[u8; ENC_CIPHERTEXT_SIZE] {
        &self.ciphertext
    }
}
