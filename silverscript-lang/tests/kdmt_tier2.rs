//! KDMT Tier-2 covenant compile test — proves the new `OpZkPrecompile` builtin
//! works inside a real covenant (ZK-verify + sha256 journal binding +
//! OpChainblockSeqCommit anchor). Local derisk; mirrors kdmt-mint/contracts/
//! kdmt-tier2-verify.sil.

use silverscript_lang::ast::Expr;
use silverscript_lang::compiler::{compile_contract, CompileOptions};

const SRC: &str = r#"
pragma silverscript ^0.1.0;

contract KdmtTier2Verify(byte[32] imageId, byte[32] controlId, byte[1] hashFn) {

    byte[1] constant TAG_R0_SUCCINCT = 0x21;

    entrypoint function claim(
        byte[32] claimDigest,
        byte[4]  controlIndex,
        byte[]   controlDigests,
        byte[]   seal,
        byte[32] seqCommit,
        int      daaScore,
        int      timestamp,
        int      blueScore,
        byte[32] blockHash
    ) {
        byte[32] journal = sha256(
            seqCommit + bytes(daaScore, 8) + bytes(timestamp, 8) + bytes(blueScore, 8)
        );

        require(OpZkPrecompile(
            claimDigest, controlIndex, controlDigests, seal, journal,
            imageId, controlId, hashFn, TAG_R0_SUCCINCT
        ));

        require(seqCommit == OpChainblockSeqCommit(blockHash));

        require(daaScore > 0);
    }
}
"#;

#[test]
fn kdmt_tier2_verify_compiles_with_opzkprecompile() {
    let args: Vec<Expr<'static>> = vec![
        [0xABu8; 32].to_vec().into(), // imageId
        [0xCDu8; 32].to_vec().into(), // controlId
        vec![1u8].into(),             // hashFn (Poseidon2)
    ];
    let compiled = compile_contract(SRC, &args, CompileOptions::default())
        .expect("KDMT Tier-2 covenant must compile");
    assert!(!compiled.script.is_empty(), "compiled script empty");
    // OpZkPrecompile opcode (0xa6) must be emitted by the new builtin.
    assert!(
        compiled.script.iter().any(|&b| b == 0xa6),
        "OpZkPrecompile (0xa6) must appear in the compiled covenant"
    );
    println!(
        "KDMT Tier-2 covenant compiled: {} bytes, OpZkPrecompile(0xa6) present",
        compiled.script.len()
    );
}
