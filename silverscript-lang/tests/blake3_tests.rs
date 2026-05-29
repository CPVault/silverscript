//! Tests for the `blake3` and `blake3WithKey` builtins.
//!
//! These cover both code generation (correct opcode emitted) and runtime
//! behaviour (the compiled script produces the same digest as the `blake3`
//! reference crate). The keyed test in particular pins the argument/stack
//! order: silverscript `blake3WithKey(data, key)` must equal
//! `blake3::keyed_hash(key, data)`.

use kaspa_consensus_core::hashing::sighash::SigHashReusedValuesUnsync;
use kaspa_consensus_core::mass::units::SigopCount;
use kaspa_consensus_core::tx::{
    PopulatedTransaction, ScriptPublicKey, Transaction, TransactionId, TransactionInput, TransactionOutpoint, TransactionOutput,
    UtxoEntry,
};
use kaspa_txscript::caches::Cache;
use kaspa_txscript::opcodes::codes::{OpBlake3, OpBlake3WithKey};
use kaspa_txscript::{EngineCtx, EngineFlags, TxScriptEngine};
use kaspa_txscript_errors::TxScriptError;
use silverscript_lang::compiler::{CompileOptions, compile_contract};

/// Execute a standalone redeem script (no covenant context, no selector) with
/// covenants enabled so the 0xd9/0xda hash opcodes are available.
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

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn blake3_emits_opcode_0xd9() {
    let source = r#"
        contract B3() {
            entrypoint function main(byte[] data) {
                require(blake3(data).length == 32);
            }
        }
    "#;
    let compiled = compile_contract(source, &[], CompileOptions::default()).expect("blake3 should compile");
    assert!(compiled.script.iter().copied().any(|op| op == OpBlake3), "blake3 must emit OpBlake3 (0xd9)");
}

#[test]
fn blake3_with_key_emits_opcode_0xda() {
    let source = r#"
        contract B3() {
            entrypoint function main(byte[] data, byte[32] key) {
                require(blake3WithKey(data, key).length == 32);
            }
        }
    "#;
    let compiled = compile_contract(source, &[], CompileOptions::default()).expect("blake3WithKey should compile");
    assert!(compiled.script.iter().copied().any(|op| op == OpBlake3WithKey), "blake3WithKey must emit OpBlake3WithKey (0xda)");
}

#[test]
fn blake3_matches_reference_digest() {
    let data: &[u8] = &[0xde, 0xad, 0xbe, 0xef, 0x01, 0x02, 0x03];
    let expected = blake3::hash(data);
    let source = format!(
        r#"
        contract B3() {{
            entrypoint function main() {{
                require(blake3(0x{}) == 0x{});
            }}
        }}
    "#,
        hex(data),
        expected.to_hex()
    );
    let compiled = compile_contract(&source, &[], CompileOptions::default()).expect("compile succeeds");
    assert!(run(compiled.script).is_ok(), "blake3(data) must equal blake3::hash(data)");
}

#[test]
fn blake3_with_key_matches_reference_keyed_digest_and_arg_order() {
    // Pins the stack order: silverscript blake3WithKey(data, key) pushes data
    // first then key; the engine pops [data, key] and computes keyed_hash(key, data).
    let data: &[u8] = &[0x11, 0x22, 0x33, 0x44, 0x55];
    let key: [u8; 32] = *b"SeqCommitMergesetContext\0\0\0\0\0\0\0\0";
    let expected = blake3::keyed_hash(&key, data);
    let source = format!(
        r#"
        contract B3() {{
            entrypoint function main() {{
                require(blake3WithKey(0x{}, 0x{}) == 0x{});
            }}
        }}
    "#,
        hex(data),
        hex(&key),
        expected.to_hex()
    );
    let compiled = compile_contract(&source, &[], CompileOptions::default()).expect("compile succeeds");
    assert!(run(compiled.script).is_ok(), "blake3WithKey(data, key) must equal blake3::keyed_hash(key, data)");
}

#[test]
fn blake3_with_key_wrong_expected_fails() {
    // Negative control: a mismatched expected digest must fail at runtime,
    // proving the previous test is not vacuously passing.
    let data: &[u8] = &[0x11, 0x22, 0x33, 0x44, 0x55];
    let key: [u8; 32] = [0x42; 32];
    let wrong = [0u8; 32];
    let source = format!(
        r#"
        contract B3() {{
            entrypoint function main() {{
                require(blake3WithKey(0x{}, 0x{}) == 0x{});
            }}
        }}
    "#,
        hex(data),
        hex(&key),
        hex(&wrong)
    );
    let compiled = compile_contract(&source, &[], CompileOptions::default()).expect("compile succeeds");
    assert!(run(compiled.script).is_err(), "mismatched keyed digest must fail");
}

#[test]
fn blake3_arity_errors() {
    let zero = r#"contract B() { entrypoint function m() { require(blake3() == 0x00); } }"#;
    assert!(compile_contract(zero, &[], CompileOptions::default()).is_err(), "blake3() with 0 args must fail");

    let two = r#"contract B() { entrypoint function m(byte[] a, byte[] b) { require(blake3(a, b) == 0x00); } }"#;
    assert!(compile_contract(two, &[], CompileOptions::default()).is_err(), "blake3() with 2 args must fail");

    let one = r#"contract B() { entrypoint function m(byte[] a) { require(blake3WithKey(a).length == 32); } }"#;
    assert!(compile_contract(one, &[], CompileOptions::default()).is_err(), "blake3WithKey() with 1 arg must fail");
}
