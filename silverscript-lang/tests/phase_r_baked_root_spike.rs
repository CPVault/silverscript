//! Phase R "baked-root" covenant-logic SPIKE (infra-free, DEPTH=3, N=8).
//!
//! Proves the KDMT Phase R mechanism from
//! `KNS/vault/40-PROJECTS/dmt-on-covenant/phase-r-baked-root-design-2026-06-16.md`
//! is expressible + executable in silverscript at a small FIXED depth:
//!
//!   1. inclusion        : fold(leaf,        incl_path,    i) == historicalRoot
//!   2. nullifier non-mem: fold(EMPTY,       claimed_path, i) == claimedRoot_before
//!   3. insert           : fold(CLAIMED,     claimed_path, i) == claimedRoot_after
//!
//! Steps 2+3 deliberately reuse the SAME claimed_path: the empty-leaf fold proves
//! "slot i not yet claimed", the CLAIMED-leaf fold (same siblings) yields the new
//! root. One path = non-membership proof + state transition.
//!
//! This is a fixed BINARY Merkle / SMT over leaf index 0..N-1 (NOT the 256-bit-key
//! Kaspa SMT used in smt_verify_tests.rs). The design doc specifies exactly this:
//! "fixed binary Merkle over index 0..N-1". We mirror that harness's keyed-blake3
//! node hashing convention (`blake3WithKey(left + right, node_key)` per level).
//!
//! Verification is TWO-PRONG:
//!   (a) the generated verifier .sil COMPILES, and
//!   (b) it EXECUTES to success on a TxScriptEngine (covenants enabled),
//! plus a Rust mirror that recomputes all three roots independently. Negatives
//! (forged leaf / wrong sibling / double-claim) make the corresponding require
//! FAIL at execution.
//!
//! SPIKE ONLY. New file. Does not touch any real .sil covenant.

use kaspa_consensus_core::hashing::sighash::SigHashReusedValuesUnsync;
use kaspa_consensus_core::mass::units::SigopCount;
use kaspa_consensus_core::tx::{
    PopulatedTransaction, ScriptPublicKey, Transaction, TransactionId, TransactionInput, TransactionOutpoint,
    TransactionOutput, UtxoEntry,
};
use kaspa_txscript::caches::Cache;
use kaspa_txscript::{EngineCtx, EngineFlags, TxScriptEngine};
use kaspa_txscript_errors::TxScriptError;
use silverscript_lang::compiler::{compile_contract, CompileOptions};

const DEPTH: usize = 3; // N = 2^DEPTH = 8 leaves
const N: usize = 1 << DEPTH;

// ---- Encoding conventions (the real covenant + indexer MUST match these) -----
//
// leaf_key   : keyed-blake3 domain for the leaf hash       = "KdmtPhaseRLeaf" padded to 32
// node_key   : keyed-blake3 domain for internal nodes      = "KdmtPhaseRNode" padded to 32
// leaf_i     : blake3WithKey(block_hash(32) + daa(8 LE) + delta(8 LE), leaf_key)
// EMPTY leaf : 32 zero bytes (the unclaimed nullifier slot value)
// CLAIMED    : a fixed nonzero 32-byte marker (0x01 repeated) — the claimed value
// node(l,r)  : blake3WithKey(l(32) + r(32), node_key)
// index bit  : level d (0 = leaf level) uses bit (i >> d) & 1; bit==0 => current
//              is LEFT child, sibling RIGHT; bit==1 => sibling LEFT, current RIGHT.

fn pad32(domain: &[u8]) -> [u8; 32] {
    let mut k = [0u8; 32];
    k[..domain.len()].copy_from_slice(domain);
    k
}

fn leaf_key() -> [u8; 32] {
    pad32(b"KdmtPhaseRLeaf")
}
fn node_key() -> [u8; 32] {
    pad32(b"KdmtPhaseRNode")
}

const EMPTY: [u8; 32] = [0u8; 32];
const CLAIMED: [u8; 32] = [1u8; 32];

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn blake3_keyed(key: &[u8; 32], data: &[u8]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_keyed(key);
    h.update(data);
    *h.finalize().as_bytes()
}

/// node(left, right) = blake3WithKey(left + right, node_key)
fn node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut buf = Vec::with_capacity(64);
    buf.extend_from_slice(left);
    buf.extend_from_slice(right);
    blake3_keyed(&node_key(), &buf)
}

/// leaf_i = blake3WithKey(block_hash + daa_le8 + delta_le8, leaf_key)
fn make_leaf(block_hash: &[u8; 32], daa: u64, delta: u64) -> [u8; 32] {
    let mut buf = Vec::with_capacity(48);
    buf.extend_from_slice(block_hash);
    buf.extend_from_slice(&daa.to_le_bytes());
    buf.extend_from_slice(&delta.to_le_bytes());
    blake3_keyed(&leaf_key(), &buf)
}

/// Full binary Merkle root over exactly N=2^DEPTH leaves.
fn merkle_root(leaves: &[[u8; 32]]) -> [u8; 32] {
    assert_eq!(leaves.len(), N);
    let mut level: Vec<[u8; 32]> = leaves.to_vec();
    while level.len() > 1 {
        level = level.chunks(2).map(|pair| node(&pair[0], &pair[1])).collect();
    }
    level[0]
}

/// Sibling path for leaf `index`: siblings[d] is the sibling at level d
/// (d=0 = leaf level). Returned bottom-up.
fn merkle_path(leaves: &[[u8; 32]], index: usize) -> Vec<[u8; 32]> {
    assert_eq!(leaves.len(), N);
    let mut sibs = Vec::with_capacity(DEPTH);
    let mut level: Vec<[u8; 32]> = leaves.to_vec();
    let mut idx = index;
    while level.len() > 1 {
        let sib = idx ^ 1;
        sibs.push(level[sib]);
        level = level.chunks(2).map(|pair| node(&pair[0], &pair[1])).collect();
        idx /= 2;
    }
    sibs
}

/// Rust mirror of the EXACT fold the .sil performs: fold a leaf up through the
/// sibling path at `index`, returning the recomputed root.
fn fold(leaf: &[u8; 32], path: &[[u8; 32]], index: usize) -> [u8; 32] {
    let mut current = *leaf;
    let mut idx = index;
    for sib in path.iter() {
        current = if idx & 1 == 0 { node(&current, sib) } else { node(sib, &current) };
        idx >>= 1;
    }
    current
}

/// claimedRoot for an array of N slot-values (EMPTY or CLAIMED).
fn smt_root(slots: &[[u8; 32]; N]) -> [u8; 32] {
    merkle_root(slots)
}

// --------------------------- .sil generation ----------------------------------

/// Generate a verifier .sil that performs all three folds with the leaf params +
/// both paths inlined as literals, and `require`s each computed root.
///
/// `leaf` is computed inside the script from block_hash/daa/delta so the leaf
/// encoding itself is exercised on-chain (not just passed in pre-hashed).
/// General form: inclusion fold uses `incl_index`, nullifier folds use `null_index`.
/// In an HONEST claim these are equal (see `gen_verifier`). They are allowed to
/// DIFFER here purely to model the S2 "unbound index" attack
/// (`phase_r_negative_s2_unbound_index_double_mint`): proving inclusion of block
/// `incl_index` while nullifying a different empty slot `null_index`.
#[allow(clippy::too_many_arguments)]
fn gen_verifier_indices(
    block_hash: &[u8; 32],
    daa: u64,
    delta: u64,
    incl_index: usize,
    incl_path: &[[u8; 32]],
    null_index: usize,
    claimed_path: &[[u8; 32]],
    historical_root: &[u8; 32],
    claimed_before: &[u8; 32],
    claimed_after: &[u8; 32],
) -> String {
    let lk = hex(&leaf_key());
    let nk = hex(&node_key());
    let daa_le = hex(&daa.to_le_bytes());
    let delta_le = hex(&delta.to_le_bytes());

    let mut body = String::new();

    // --- leaf = blake3WithKey(block_hash + daa_le8 + delta_le8, leaf_key) ---
    body.push_str(&format!(
        "        byte[32] leaf = blake3WithKey(0x{} + 0x{} + 0x{}, 0x{});\n",
        hex(block_hash),
        daa_le,
        delta_le,
        lk
    ));

    // helper to emit a fold over a given path into a named var, driven by `fold_index`.
    let emit_fold = |body: &mut String, var: &str, start_expr: &str, path: &[[u8; 32]], fold_index: usize| {
        body.push_str(&format!("        byte[32] {var} = {start_expr};\n"));
        let mut idx = fold_index;
        for sib in path.iter() {
            if idx & 1 == 0 {
                body.push_str(&format!("        {var} = blake3WithKey({var} + 0x{}, 0x{});\n", hex(sib), nk));
            } else {
                body.push_str(&format!("        {var} = blake3WithKey(0x{} + {var}, 0x{});\n", hex(sib), nk));
            }
            idx >>= 1;
        }
    };

    // 1. inclusion (at incl_index)
    emit_fold(&mut body, "incl", "leaf", incl_path, incl_index);
    body.push_str(&format!("        require(incl == 0x{});\n", hex(historical_root)));

    // 2. nullifier non-membership (EMPTY leaf, claimed_path at null_index)
    emit_fold(&mut body, "nonmem", &format!("0x{}", hex(&EMPTY)), claimed_path, null_index);
    body.push_str(&format!("        require(nonmem == 0x{});\n", hex(claimed_before)));

    // 3. insert (CLAIMED leaf, SAME claimed_path at null_index)
    emit_fold(&mut body, "inserted", &format!("0x{}", hex(&CLAIMED)), claimed_path, null_index);
    body.push_str(&format!("        require(inserted == 0x{});\n", hex(claimed_after)));

    format!("contract PhaseR() {{\n    entrypoint function main() {{\n{body}    }}\n}}\n")
}

/// HONEST claim: inclusion and nullifier share ONE index (incl_index == null_index).
/// This is what the real covenant MUST enforce on-chain (see S2 fix note).
#[allow(clippy::too_many_arguments)]
fn gen_verifier(
    block_hash: &[u8; 32],
    daa: u64,
    delta: u64,
    index: usize,
    incl_path: &[[u8; 32]],
    claimed_path: &[[u8; 32]],
    historical_root: &[u8; 32],
    claimed_before: &[u8; 32],
    claimed_after: &[u8; 32],
) -> String {
    gen_verifier_indices(
        block_hash,
        daa,
        delta,
        index,
        incl_path,
        index,
        claimed_path,
        historical_root,
        claimed_before,
        claimed_after,
    )
}

// --------------------------- execution harness --------------------------------

fn run(script: Vec<u8>) -> Result<(), TxScriptError> {
    let reused_values = SigHashReusedValuesUnsync::new();
    let sig_cache = Cache::new(10_000);
    let input = TransactionInput {
        previous_outpoint: TransactionOutpoint { transaction_id: TransactionId::from_bytes([0u8; 32]), index: 0 },
        signature_script: vec![],
        sequence: 0,
        mass: SigopCount(0).into(),
    };
    let output =
        TransactionOutput { value: 1000, script_public_key: ScriptPublicKey::new(0, script.clone().into()), covenant: None };
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

// ------------------------------- fixtures -------------------------------------

struct Fixtures {
    block_hashes: Vec<[u8; 32]>,
    daas: Vec<u64>,
    deltas: Vec<u64>,
    leaves: Vec<[u8; 32]>,
    historical_root: [u8; 32],
    claimed_before_slots: [[u8; 32]; N],
    claimed_before: [u8; 32],
    claimed_after: [u8; 32],
    incl_path: Vec<[u8; 32]>,
    claimed_path: Vec<[u8; 32]>,
}

/// Deterministic 8-leaf fixtures with claim at `index`.
fn build_fixtures(index: usize) -> Fixtures {
    let mut block_hashes = Vec::with_capacity(N);
    let mut daas = Vec::with_capacity(N);
    let mut deltas = Vec::with_capacity(N);
    let mut leaves = [[0u8; 32]; N];
    for i in 0..N {
        let bh = [0xB0 + i as u8; 32];
        let daa = 478_000_000u64 + (i as u64) * 1000;
        let delta = 10_000u64 + (i as u64) * 7;
        leaves[i] = make_leaf(&bh, daa, delta);
        block_hashes.push(bh);
        daas.push(daa);
        deltas.push(delta);
    }
    let historical_root = merkle_root(&leaves);

    let claimed_before_slots = [EMPTY; N]; // all unclaimed
    let claimed_before = smt_root(&claimed_before_slots);

    let mut after_slots = claimed_before_slots;
    after_slots[index] = CLAIMED;
    let claimed_after = smt_root(&after_slots);

    let incl_path = merkle_path(&leaves, index);
    let claimed_path = merkle_path(&claimed_before_slots, index);

    Fixtures {
        block_hashes,
        daas,
        deltas,
        leaves: leaves.to_vec(),
        historical_root,
        claimed_before_slots,
        claimed_before,
        claimed_after,
        incl_path,
        claimed_path,
    }
}

// =============================== TESTS =======================================

/// POSITIVE: with correct leaf/paths the 3-fold verifier compiles AND executes,
/// and the Rust mirror reproduces all three roots.
#[test]
fn phase_r_positive_compiles_executes_and_mirror_agrees() {
    let index = 5usize;
    let f = build_fixtures(index);

    // (b) Rust mirror reproduces all three roots (so the require conditions hold).
    let leaf = make_leaf(&f.block_hashes[index], f.daas[index], f.deltas[index]);
    assert_eq!(f.leaves[index], leaf, "leaf encoding mirror");
    assert_eq!(fold(&leaf, &f.incl_path, index), f.historical_root, "inclusion fold mirror");
    assert_eq!(fold(&EMPTY, &f.claimed_path, index), f.claimed_before, "non-membership fold mirror");
    assert_eq!(fold(&CLAIMED, &f.claimed_path, index), f.claimed_after, "insert fold mirror");

    // (a) generated verifier compiles AND executes.
    let src = gen_verifier(
        &f.block_hashes[index],
        f.daas[index],
        f.deltas[index],
        index,
        &f.incl_path,
        &f.claimed_path,
        &f.historical_root,
        &f.claimed_before,
        &f.claimed_after,
    );
    let compiled = compile_contract(&src, &[], CompileOptions::default()).expect("verifier must compile");
    assert!(!compiled.script.is_empty());
    assert!(run(compiled.script.clone()).is_ok(), "positive verifier must execute to success");

    eprintln!("[phase-r spike] DEPTH={DEPTH} positive script bytes = {}", compiled.script.len());
}

/// NEGATIVE 1 — FORGED LEAF: wrong delta_work → inclusion fold diverges →
/// require(incl == historicalRoot) must FAIL at execution.
#[test]
fn phase_r_negative_forged_leaf_rejected() {
    let index = 2usize;
    let f = build_fixtures(index);

    // forge: claim a different delta than baked into historicalRoot.
    let forged_delta = f.deltas[index] + 999;
    let forged_leaf = make_leaf(&f.block_hashes[index], f.daas[index], forged_delta);
    assert_ne!(
        fold(&forged_leaf, &f.incl_path, index),
        f.historical_root,
        "mirror: forged leaf must NOT reproduce historicalRoot"
    );

    let src = gen_verifier(
        &f.block_hashes[index],
        f.daas[index],
        forged_delta, // forged
        index,
        &f.incl_path,
        &f.claimed_path,
        &f.historical_root,
        &f.claimed_before,
        &f.claimed_after,
    );
    let compiled = compile_contract(&src, &[], CompileOptions::default()).expect("compiles (logic, not data, fails)");
    assert!(run(compiled.script).is_err(), "forged leaf must fail inclusion require");
}

/// NEGATIVE 2 — WRONG SIBLING: corrupt one inclusion sibling → inclusion fold
/// diverges → require must FAIL.
#[test]
fn phase_r_negative_wrong_sibling_rejected() {
    let index = 4usize;
    let f = build_fixtures(index);

    let mut bad_incl = f.incl_path.clone();
    bad_incl[1][0] ^= 0xff; // flip one byte of a sibling
    assert_ne!(fold(&f.leaves[index], &bad_incl, index), f.historical_root, "mirror: wrong sibling diverges");

    let src = gen_verifier(
        &f.block_hashes[index],
        f.daas[index],
        f.deltas[index],
        index,
        &bad_incl, // corrupted
        &f.claimed_path,
        &f.historical_root,
        &f.claimed_before,
        &f.claimed_after,
    );
    let compiled = compile_contract(&src, &[], CompileOptions::default()).expect("compiles");
    assert!(run(compiled.script).is_err(), "wrong sibling must fail inclusion require");
}

/// NEGATIVE 3 — DOUBLE-CLAIM: slot i is ALREADY claimed in claimedRoot_before.
/// The non-membership fold of EMPTY must NOT equal that root → require FAILS.
/// This is the core anti-double-mint guarantee.
#[test]
fn phase_r_negative_double_claim_rejected() {
    let index = 5usize;
    let f = build_fixtures(index);

    // claimedRoot_before where slot i is ALREADY CLAIMED.
    let mut already = f.claimed_before_slots;
    already[index] = CLAIMED;
    let claimed_before_dirty = smt_root(&already);
    // path is over the (now dirty) tree; sibling values at level>0 may change but
    // the sibling at leaf level (its pair) is unchanged here, and crucially the
    // EMPTY-leaf fold can no longer reproduce a root that already has slot i set.
    let claimed_path_dirty = merkle_path(&already, index);

    // mirror: folding EMPTY up must NOT equal the dirty root (slot i is occupied).
    assert_ne!(
        fold(&EMPTY, &claimed_path_dirty, index),
        claimed_before_dirty,
        "mirror: EMPTY non-membership must fail when slot already claimed"
    );

    // after-root if we (wrongly) tried to insert again — provide a consistent
    // value so ONLY the non-membership require is the thing that fails.
    let mut after2 = already;
    after2[index] = CLAIMED;
    let claimed_after_dirty = smt_root(&after2);

    let src = gen_verifier(
        &f.block_hashes[index],
        f.daas[index],
        f.deltas[index],
        index,
        &f.incl_path,
        &claimed_path_dirty,
        &f.historical_root,
        &claimed_before_dirty, // slot already set
        &claimed_after_dirty,
    );
    let compiled = compile_contract(&src, &[], CompileOptions::default()).expect("compiles");
    assert!(run(compiled.script).is_err(), "double-claim must fail non-membership require");
}

/// NEGATIVE 4 — **S2: UNBOUND INDEX DOUBLE-MINT** (the bug the review flagged;
/// missing until now). In a real singleton covenant the leaf index is a WITNESS.
/// If the inclusion fold and the nullifier fold derive their position
/// INDEPENDENTLY (nothing binds them), an attacker can prove inclusion of block
/// `i` (→ covenant mints delta_i) while nullifying a DIFFERENT empty slot `j ≠ i`
/// (→ claimedRoot marks j, NOT i). Slot i stays EMPTY → block i is re-mintable
/// with a fresh empty `j'` each time = unbounded double-mint.
///
/// This test CONSTRUCTS that mismatched claim and shows the engine ACCEPTS it —
/// concretely proving S2 in executable form. The original "double-claim" negative
/// (NEGATIVE 3) only ever used one index for both folds, so it could not see this.
///
/// FIX (feasibility confirmed in silverscript: has `&`,`%`,`/`,`if`,`?:`): the real
/// covenant must take ONE authenticated witness index `i` and derive BOTH folds'
/// per-level direction on-chain from it — `bit = (i / 2^d) % 2` per fixed-unrolled
/// level d — so inclusion and nullifier are STRUCTURALLY the same position. With
/// that binding, `incl_index == null_index` always, and this exact script becomes
/// impossible to construct. When the bound covenant exists, this test must FLIP to
/// `is_err()`.
#[test]
fn phase_r_negative_s2_unbound_index_double_mint() {
    let i = 5usize; // block whose delta we mint
    let j = 2usize; // a DIFFERENT empty slot we nullify instead
    assert_ne!(i, j, "S2 attack requires inclusion index != nullifier index");
    let f = build_fixtures(i); // all claimed slots empty

    // Inclusion proof for block i (authentic → reproduces historicalRoot).
    let incl_path_i = merkle_path(&f.leaves, i);
    // Nullifier path for the OTHER empty slot j (authentic over the all-empty tree).
    let claimed_path_j = merkle_path(&f.claimed_before_slots, j);
    let mut after_j = f.claimed_before_slots;
    after_j[j] = CLAIMED; // we mark j, NOT i
    let claimed_after_j = smt_root(&after_j);

    // Mirror: BOTH folds are independently valid for i != j — that is the danger.
    assert_eq!(fold(&f.leaves[i], &incl_path_i, i), f.historical_root, "inclusion(i) valid");
    assert_eq!(fold(&EMPTY, &claimed_path_j, j), f.claimed_before, "non-membership(j) valid");
    assert_eq!(fold(&CLAIMED, &claimed_path_j, j), claimed_after_j, "insert(j) valid");

    // The mismatched claim: mint block i, but nullify slot j.
    let src = gen_verifier_indices(
        &f.block_hashes[i],
        f.daas[i],
        f.deltas[i],
        i,
        &incl_path_i, // inclusion at i
        j,
        &claimed_path_j, // nullifier at j != i
        &f.historical_root,
        &f.claimed_before,
        &claimed_after_j,
    );
    let compiled = compile_contract(&src, &[], CompileOptions::default()).expect("compiles");
    // S2: an UNBOUND covenant ACCEPTS this → block i minted but slot i left empty.
    assert!(
        run(compiled.script).is_ok(),
        "S2 demonstrated: unbound index lets inclusion(i={i}) pair with nullifier(j={j}) → \
         block i minted while slot i stays EMPTY → re-mintable. FIX: bind one on-chain index."
    );
}

/// SIZE / COST report: print compiled byte size and blake3-op count so we can
/// extrapolate to DEPTH=18 (real N~263k). Not an assertion of magic numbers —
/// emits measured facts for the report.
#[test]
fn phase_r_size_and_cost_report() {
    let index = 5usize;
    let f = build_fixtures(index);
    let src = gen_verifier(
        &f.block_hashes[index],
        f.daas[index],
        f.deltas[index],
        index,
        &f.incl_path,
        &f.claimed_path,
        &f.historical_root,
        &f.claimed_before,
        &f.claimed_after,
    );
    let compiled = compile_contract(&src, &[], CompileOptions::default()).expect("compiles");
    let n_blake3 = compiled.script.iter().filter(|&&b| b == 0xda).count(); // OpBlake3WithKey
    let bytes = compiled.script.len();
    eprintln!("=== PHASE-R SPIKE COST REPORT (DEPTH={DEPTH}, N={N}) ===");
    eprintln!("compiled script bytes        : {bytes}");
    eprintln!("OpBlake3WithKey (0xda) count : {n_blake3}  (expect 1 leaf + 3*DEPTH folds = {})", 1 + 3 * DEPTH);
    eprintln!("source .sil bytes            : {}", src.len());
    // expected: 1 leaf hash + DEPTH (incl) + DEPTH (nonmem) + DEPTH (insert)
    assert_eq!(n_blake3, 1 + 3 * DEPTH, "blake3-op count must equal 1 + 3*DEPTH");
}
