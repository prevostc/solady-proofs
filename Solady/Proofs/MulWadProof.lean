import Mathlib

import EvmYul.EVM.Semantics
import EvmYul.EVM.State
import EvmYul.State.ExecutionEnv
import EvmYul.State.BlockHeader
import EvmYul.UInt256

import Solady.EvmUtils
import Solady.Specs.MulWadSpec
import Solady.Code.MulWadCode

namespace Solady

open EvmYul
open EvmYul.EVM

/-- Calldata for `mulWad(uint256,uint256)` = selector ++ x ++ y. -/
def mulWadCalldata (x y : UInt256) : ByteArray :=
  (selectorBytes mulWadSelector) ++ (abiWord x) ++ (abiWord y)

/-- Run your compiled mulWad runtime with ABI calldata. -/
def runMulWad (fuel : Nat) (x y : UInt256) :
    Except EVM.ExecutionException (EVM.ExecutionResult EVM.State) :=
  runCode fuel mulWadBytecode (mulWadCalldata x y)

/-- Convenience: execute and map to `Outcome`. -/
def runMulWadOutcome (fuel : Nat) (x y : UInt256) : Except EVM.ExecutionException Outcome := do
  let r ← runMulWad fuel x y
  return observedOutcome r


theorem selectorBytes_size (s : UInt32) : (selectorBytes s).size = 4 := by
  -- natToBytesBE always emits exactly `len` bytes
  simp [selectorBytes, natToBytesBE]
  sorry

theorem abiWord_size (x : UInt256) : (abiWord x).size = 32 := by
  simp [abiWord, natToBytesBE]
  sorry

theorem mulWadCalldata_size (x y : UInt256) : (mulWadCalldata x y).size = 68 := by
  -- 4 + 32 + 32
  --simp [mulWadCalldata, selectorBytes_size, abiWord_size, ByteArray.size_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  sorry

/-! ## Main theorem you ultimately want -/

/--
**Goal:** For sufficient fuel, executing the solc-generated runtime bytecode
matches the functional spec `mulWadSpec`.

This is the “bytecode-level correctness” statement.
-/
theorem mulWad_bytecode_correct (fuel : Nat) (x y : UInt256) :
    runMulWadOutcome fuel x y = .ok (mulWadSpec x y) := by
  simp [runMulWadOutcome, runMulWad]
  sorry

end Solady
