//! C1 regression: singleton continuation-output value conservation.
//!
//! A `#[covenant.singleton]` covenant recreates itself on each spend (a
//! "continuation output"). The compiler's auto-injected `validateOutputState`
//! binds only the continuation output's scriptPubKey, NOT its carried value.
//! Without an explicit principal-conservation check, an attacker can recreate
//! the singleton at the correct P2SH (spk matches, lineage continues) but with
//! a DUST value, skimming the carried principal. This is "C1".
//!
//! The fix (deployed at contracts/kdmt-minter-tier1-phaser.sil:179-180) adds, at
//! the end of the function body:
//!     int continuationIdx = OpAuthOutputIdx(this.activeInputIndex, 0);
//!     require(tx.outputs[continuationIdx].value == tx.inputs[this.activeInputIndex].value);
//!
//! These tests reproduce C1 with a minimal singleton: a CONSERVING_SINGLETON
//! carrying the conservation require, and a VULNERABLE_SINGLETON without it.

use kaspa_consensus_core::Hash;
use kaspa_consensus_core::tx::{CovenantBinding, ScriptPublicKey, Transaction, TransactionOutput, UtxoEntry};
use kaspa_txscript::opcodes::codes::OpTrue;
use kaspa_txscript::pay_to_script_hash_script;
use silverscript_lang::ast::Expr;
use silverscript_lang::compiler::{CompileOptions, CompiledContract, compile_contract, struct_object};

mod common;

use common::{assert_verify_like_error, covenant_decl_sigscript, execute_input_with_covenants, tx_input};

const COV_A: Hash = Hash::from_bytes(*b"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA");

/// The real COVENANT_AMOUNT_SOMPI principal carried by the deployed minter.
const INPUT_VALUE: u64 = 30_000_000;
/// Dust value an attacker would recreate the continuation with to skim principal.
const DUST: u64 = 1_000;

/// Minimal singleton WITH the C1 conservation fix: the recreated continuation
/// output must carry forward EXACTLY the value of the spent singleton input.
const CONSERVING_SINGLETON: &str = r#"
    contract Vault(int init_value) {
        int value = init_value;

        #[covenant.singleton]
        function step(State prev_state, State new_state) {
            require(new_state.value == prev_state.value);
            int contIdx = OpAuthOutputIdx(this.activeInputIndex, 0);
            require(tx.outputs[contIdx].value == tx.inputs[this.activeInputIndex].value);
        }
    }
"#;

/// Same singleton WITHOUT the conservation require — the pre-fix vulnerable shape.
const VULNERABLE_SINGLETON: &str = r#"
    contract Vault(int init_value) {
        int value = init_value;

        #[covenant.singleton]
        function step(State prev_state, State new_state) {
            require(new_state.value == prev_state.value);
        }
    }
"#;

fn compile_vault(source: &'static str, init_value: i64) -> CompiledContract<'static> {
    compile_contract(source, &[Expr::int(init_value)], CompileOptions::default()).expect("compile succeeds")
}

fn state_arg(value: i64) -> Expr<'static> {
    struct_object(vec![("value", Expr::int(value))])
}

/// Build the spent singleton UTXO with a custom carried value.
fn vault_utxo(compiled: &CompiledContract<'_>, value: u64) -> UtxoEntry {
    UtxoEntry::new(value, pay_to_script_hash_script(&compiled.script), 0, false, Some(COV_A))
}

/// Build the recreated continuation output with a custom carried value.
fn continuation_output(compiled: &CompiledContract<'_>, value: u64) -> TransactionOutput {
    TransactionOutput {
        value,
        script_public_key: pay_to_script_hash_script(&compiled.script),
        covenant: Some(CovenantBinding { authorizing_input: 0, covenant_id: COV_A }),
    }
}

/// Construct the one-input/one-output singleton-spend tx with given input and
/// continuation-output values and run input 0 through the script engine.
fn run_singleton_spend(
    source: &'static str,
    input_value: u64,
    output_value: u64,
) -> Result<(), kaspa_txscript_errors::TxScriptError> {
    // State carried unchanged (10 -> 10) so the continuation spk matches.
    let active = compile_vault(source, 10);
    let out = compile_vault(source, 10);

    let input0 = tx_input(0, covenant_decl_sigscript(&active, "step", vec![state_arg(10)], false));
    let outputs = vec![continuation_output(&out, output_value)];
    let tx = Transaction::new(1, vec![input0], outputs, 0, Default::default(), 0, vec![]);
    let entries = vec![vault_utxo(&active, input_value)];

    execute_input_with_covenants(tx, entries, 0)
}

/// Headline test: with the fix in place, the continuation output value must be
/// conserved. A drain (dust continuation) is rejected; the honest carry-forward
/// is accepted.
#[test]
fn singleton_continuation_value_must_be_conserved() {
    // NEGATIVE: drain attempt — recreate singleton at dust, skimming principal.
    let drain = run_singleton_spend(CONSERVING_SINGLETON, INPUT_VALUE, DUST)
        .expect_err("conservation fix must reject a dust continuation that skims the principal");
    assert_verify_like_error(drain);

    // POSITIVE: honest carry-forward — full principal preserved.
    let honest = run_singleton_spend(CONSERVING_SINGLETON, INPUT_VALUE, INPUT_VALUE);
    assert!(honest.is_ok(), "conservation fix must accept an honest full-value continuation: {:?}", honest.err());
}

/// Proves the vulnerability is real: WITHOUT the conservation require the engine
/// happily accepts a continuation that skims the principal down to dust. This is
/// the "before" evidence that the negative case above exercises the new require,
/// not some unrelated check.
#[test]
fn vulnerable_singleton_drain_succeeds_without_fix() {
    let result = run_singleton_spend(VULNERABLE_SINGLETON, INPUT_VALUE, DUST);
    assert!(
        result.is_ok(),
        "without the conservation fix, the engine must accept a principal-skimming dust continuation (this is C1): {:?}",
        result.err()
    );
}

/// The fix uses `==`, so an over-funded continuation is also rejected.
#[test]
fn conserving_singleton_rejects_overfunded_continuation() {
    let overfunded = run_singleton_spend(CONSERVING_SINGLETON, INPUT_VALUE, INPUT_VALUE + 1)
        .expect_err("conservation fix uses == and must reject an over-funded continuation");
    assert_verify_like_error(overfunded);
}

// ============================================================================
// PHASE F SHAPE — minter at input[1] (coinbase at input[0]), continuation at
// output[1] (mint at output[0]).
//
// The minimal-singleton tests above run the covenant at input[0]/output[0]
// (activeInputIndex == 0). Phase F (claim.rs) spends the minter at input[1]
// with a coinbase at input[0], and recreates the minter at output[1] with the
// mint at output[0]. The C1 require uses
//     OpAuthOutputIdx(this.activeInputIndex, 0)
// which is NOT a static index — it resolves the 0th output AUTHORIZED BY the
// active input's CovenantBinding. These tests prove that with activeInputIndex
// dynamically == 1, and a non-covenant mint output sitting at output[0], the
// require still binds the CONTINUATION (output[1]) and not the mint — so a
// dust-drain of the recreated minter is rejected with the fix and accepted
// without it. This is the Phase-F-specific property the minimal tests do not
// cover (dynamic activeInputIndex + a sibling non-covenant output).
// ============================================================================

/// A non-covenant input/UTXO that stands in for the Phase F coinbase at input[0].
/// Its script is never executed by `execute_input_with_covenants` (which only
/// runs the selected input, index 1 = the minter); it only needs a valid UTXO
/// entry with no covenant_id so it does not participate in the covenant context.
fn coinbase_like_utxo(value: u64) -> UtxoEntry {
    UtxoEntry::new(value, ScriptPublicKey::new(0, vec![OpTrue].into()), 0, false, None)
}

/// A non-covenant "mint" output that stands in for Phase F's output[0]. No
/// covenant binding, so OpAuthOutputIdx(active, 0) must never resolve to it.
fn mint_like_output(value: u64) -> TransactionOutput {
    TransactionOutput { value, script_public_key: ScriptPublicKey::new(0, vec![OpTrue].into()), covenant: None }
}

/// Build the Phase F-shaped spend and run the MINTER input (index 1) through the
/// engine. Layout mirrors claim.rs exactly:
///   inputs:  [0] = coinbase-like (non-covenant), [1] = minter (covenant unlock)
///   outputs: [0] = mint (non-covenant), [1] = continuation (authorizing_input=1)
fn run_phase_f_spend(
    source: &'static str,
    minter_input_value: u64,
    continuation_value: u64,
) -> Result<(), kaspa_txscript_errors::TxScriptError> {
    let active = compile_vault(source, 10);
    let out = compile_vault(source, 10);

    // input[0] = coinbase-like (empty sig, non-covenant); input[1] = minter.
    let input0 = tx_input(0, vec![]);
    let input1 = tx_input(1, covenant_decl_sigscript(&active, "step", vec![state_arg(10)], false));

    // output[0] = mint (non-covenant); output[1] = continuation bound to input 1.
    let mint_out = mint_like_output(12_345);
    let continuation = TransactionOutput {
        value: continuation_value,
        script_public_key: pay_to_script_hash_script(&out.script),
        covenant: Some(CovenantBinding { authorizing_input: 1, covenant_id: COV_A }),
    };

    let tx = Transaction::new(1, vec![input0, input1], vec![mint_out, continuation], 0, Default::default(), 0, vec![]);
    let entries = vec![coinbase_like_utxo(50_000), vault_utxo(&active, minter_input_value)];

    // Execute the MINTER input (index 1) → activeInputIndex == 1 at runtime.
    execute_input_with_covenants(tx, entries, 1)
}

/// Phase F headline: with the fix, the continuation (output[1]) value must equal
/// the spent minter (input[1]) value, EVEN with a sibling non-covenant mint at
/// output[0] and the covenant running at the non-zero input index 1.
#[test]
fn phase_f_continuation_value_must_be_conserved() {
    // NEGATIVE: drain — recreate the minter (output[1]) at dust, skim principal.
    let drain = run_phase_f_spend(CONSERVING_SINGLETON, INPUT_VALUE, DUST)
        .expect_err("Phase F: conservation fix must reject a dust continuation that skims the principal");
    assert_verify_like_error(drain);

    // POSITIVE: honest carry-forward — full principal preserved on output[1].
    let honest = run_phase_f_spend(CONSERVING_SINGLETON, INPUT_VALUE, INPUT_VALUE);
    assert!(honest.is_ok(), "Phase F: conservation fix must accept an honest full-value continuation: {:?}", honest.err());
}

/// Phase F "before" evidence: WITHOUT the conservation require, the engine
/// accepts a dust continuation even in the Phase F shape — confirming the
/// negative case above exercises the new require, not the singleton spk check
/// (the continuation spk still matches; only its value is drained).
#[test]
fn phase_f_vulnerable_drain_succeeds_without_fix() {
    let result = run_phase_f_spend(VULNERABLE_SINGLETON, INPUT_VALUE, DUST);
    assert!(
        result.is_ok(),
        "Phase F: without the conservation fix, the engine must accept a principal-skimming dust continuation (C1): {:?}",
        result.err()
    );
}
