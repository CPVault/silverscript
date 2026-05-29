//! Conformance spike: in-covenant SMT inclusion verification.
//!
//! Builds a real Kaspa SMT (SeqCommitActiveNode hasher), generates a real
//! (collapsed) inclusion proof, then generates a SilverScript verifier that
//! recomputes the Merkle root using `blake3WithKey` and checks it equals kaspa's
//! root. Proves Gap B: the keyed-BLAKE3 SMT path can be reproduced on-chain.
//!
//! Scope (spike): inclusion only; the verifier is generated for the proof's
//! actual terminal depth with per-level constants (byte index, empty-subtree
//! hash, child ordering) inlined. Generalising to a single depth-agnostic
//! covenant (runtime depth + mask lookup tables) is a documented follow-up.

use kaspa_consensus_core::hashing::sighash::SigHashReusedValuesUnsync;
use kaspa_consensus_core::mass::units::SigopCount;
use kaspa_consensus_core::tx::{
    PopulatedTransaction, ScriptPublicKey, Transaction, TransactionId, TransactionInput, TransactionOutpoint, TransactionOutput,
    UtxoEntry,
};
use kaspa_hashes::Hash;
use kaspa_smt::proof::ProofTerminal;
use kaspa_smt::tree::SparseMerkleTree;
use kaspa_txscript::caches::Cache;
use kaspa_txscript::{EngineCtx, EngineFlags, TxScriptEngine};
use kaspa_txscript_errors::TxScriptError;
use silverscript_lang::compiler::{CompileOptions, compile_contract};

type Smt = SparseMerkleTree<kaspa_hashes::SeqCommitActiveNode>;

const DEPTH: usize = 256;

fn h(seed: u8) -> Hash {
    Hash::from_bytes([seed; 32])
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Domain key, zero-padded to 32 bytes (matches Kaspa's blake3 keyed hashers).
fn pad32(domain: &[u8]) -> [u8; 32] {
    let mut k = [0u8; 32];
    k[..domain.len()].copy_from_slice(domain);
    k
}

/// EMPTY_HASHES[0..=256], mirroring crypto/smt/build.rs compute_empty_hashes
/// for the SeqCommitActiveNode (internal node) domain.
fn empty_hashes(node_key: &[u8; 32]) -> Vec<[u8; 32]> {
    let mut e = vec![[0u8; 32]; DEPTH + 1];
    for i in 1..=DEPTH {
        let mut hasher = blake3::Hasher::new_keyed(node_key);
        hasher.update(&e[i - 1]);
        hasher.update(&e[i - 1]);
        e[i] = *hasher.finalize().as_bytes();
    }
    e
}

fn is_empty_at_depth(bitmap: &[u8; 32], d: usize) -> bool {
    bitmap[d / 8] & (1 << (d % 8)) != 0
}

fn bit_at(key: &[u8; 32], d: usize) -> bool {
    key[d / 8] & (0x80 >> (d % 8)) != 0
}

/// Execute a standalone redeem script with covenants enabled (so 0xda is available).
fn run(script: Vec<u8>) -> Result<(), TxScriptError> {
    let reused_values = SigHashReusedValuesUnsync::new();
    let sig_cache = Cache::new(10_000);
    let input = TransactionInput {
        previous_outpoint: TransactionOutpoint { transaction_id: TransactionId::from_bytes([0u8; 32]), index: 0 },
        signature_script: vec![],
        sequence: 0,
        mass: SigopCount(0).into(),
    };
    let output = TransactionOutput { value: 1000, script_public_key: ScriptPublicKey::new(0, script.clone().into()), covenant: None };
    let tx = Transaction::new(1, vec![input.clone()], vec![output.clone()], 0, Default::default(), 0, vec![]);
    let utxo = UtxoEntry::new(output.value, output.script_public_key.clone(), 0, tx.is_coinbase(), None);
    let populated = PopulatedTransaction::new(&tx, vec![utxo.clone()]);
    let mut vm = TxScriptEngine::from_transaction_input(
        &populated,
        &input,
        0,
        &utxo,
        EngineCtx::new(&sig_cache).with_reused(&reused_values),
        EngineFlags { covenants_enabled: true, ..Default::default() },
    );
    vm.execute()
}

/// Build a verifier .sil that recomputes the root for an inclusion proof and
/// requires it to equal `root`. All crypto values inlined as literals; the
/// hashing chain (seed + per-level blake3WithKey) is what proves conformance.
fn gen_verifier(
    key: &[u8; 32],
    leaf: &[u8; 32],
    bitmap: &[u8; 32],
    siblings: &[[u8; 32]],
    depth: usize,
    empties: &[[u8; 32]],
    root: &[u8; 32],
) -> String {
    let node_key = pad32(b"SeqCommitActiveNode");
    let collapsed_key = pad32(b"SeqCommitActiveCollapsedNode");

    let mut body = String::new();
    body.push_str(&format!(
        "        byte[32] current = blake3WithKey(0x{} + 0x{}, 0x{});\n",
        hex(key),
        hex(leaf),
        hex(&collapsed_key)
    ));

    // Consume siblings in reverse (matches compute_root_inner sib_idx countdown).
    let mut sib_idx = siblings.len();
    for d in (0..depth).rev() {
        let sibling = if is_empty_at_depth(bitmap, d) {
            empties[DEPTH - 1 - d]
        } else {
            sib_idx -= 1;
            siblings[sib_idx]
        };
        // (left, right) = bit_at(key,d) ? (sibling, current) : (current, sibling)
        if bit_at(key, d) {
            body.push_str(&format!("        current = blake3WithKey(0x{} + current, 0x{});\n", hex(&sibling), hex(&node_key)));
        } else {
            body.push_str(&format!("        current = blake3WithKey(current + 0x{}, 0x{});\n", hex(&sibling), hex(&node_key)));
        }
    }
    body.push_str(&format!("        require(current == 0x{});\n", hex(root)));

    format!("contract SmtVerify() {{\n    entrypoint function main() {{\n{body}    }}\n}}\n")
}

#[test]
fn smt_inclusion_conformance() {
    let node_key = pad32(b"SeqCommitActiveNode");
    let empties = empty_hashes(&node_key);

    let mut tree = Smt::new();
    for i in 1u8..=8 {
        tree.insert(h(i), h(100 + i));
    }
    let key = [3u8; 32];
    let leaf = [103u8; 32];
    let proof = tree.prove(&Hash::from_bytes(key)).expect("prove");
    let root = tree.root();

    // Confirm kaspa agrees this is a valid inclusion before we mirror it.
    let kaspa_root =
        proof.compute_root::<kaspa_hashes::SeqCommitActiveNode>(&Hash::from_bytes(key), Some(Hash::from_bytes(leaf))).unwrap();
    assert_eq!(kaspa_root, root, "kaspa compute_root must match tree root");

    let depth = match proof.terminal {
        ProofTerminal::Full => DEPTH,
        ProofTerminal::Collapsed { depth } => depth as usize,
        ProofTerminal::CollapsedOther { depth, .. } => depth as usize,
    };
    let siblings: Vec<[u8; 32]> = proof.siblings.iter().map(|s| s.as_bytes()).collect();
    let root_bytes = root.as_bytes();

    // Positive: generated verifier reproduces the root.
    let src = gen_verifier(&key, &leaf, &proof.bitmap, &siblings, depth, &empties, &root_bytes);
    let compiled = compile_contract(&src, &[], CompileOptions::default()).expect("verifier compiles");
    assert!(run(compiled.script).is_ok(), "silverscript verifier must reproduce kaspa SMT root (depth {depth})");

    // Negative: corrupt the expected root by one byte → must fail.
    let mut bad_root = root_bytes;
    bad_root[0] ^= 0xff;
    let bad_src = gen_verifier(&key, &leaf, &proof.bitmap, &siblings, depth, &empties, &bad_root);
    let bad_compiled = compile_contract(&bad_src, &[], CompileOptions::default()).expect("compiles");
    assert!(run(bad_compiled.script).is_err(), "corrupted root must fail verification");
}
