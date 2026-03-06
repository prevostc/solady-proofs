import Mathlib

import EvmYul.EVM.Semantics
import EvmYul.EVM.State
import EvmYul.State.ExecutionEnv
import EvmYul.State.BlockHeader
import EvmYul.UInt256

import Solady.Bytes
import Solady.EvmUtils
import Solady.Specs.MulWadSpec
import Solady.Code.MulWadCode

namespace Solady.Proofs

open EvmYul
open EvmYul.EVM

open Solady.Bytes
open Solady.EvmUtils
open Solady.Code
open Solady.Specs

/-- Calldata for `mulWad(uint256,uint256)` = selector ++ x ++ y. -/
def mulWad_calldata (x y : UInt256) : ByteArray :=
  (selector_bytes mulWad_selector) ++ (abi_word x) ++ (abi_word y)

/-- Run your compiled mulWad runtime with ABI calldata. -/
def run_mulWad (fuel : Nat) (x y : UInt256) :
    Except EVM.ExecutionException (EVM.ExecutionResult EVM.State) :=
  execute_transaction_calldata fuel mulWad_bytecode (mulWad_calldata x y)

/-- Convenience: execute and map to `Outcome`. -/
def run_mulWad_outcome (fuel : Nat) (x y : UInt256) : Outcome :=
  match (run_mulWad fuel x y) with
    | .ok r => observed_outcome r
    | .error _ => .revert


theorem run_mulWad_correct
    (fuel : Nat) (x y : UInt256) :
    (match run_mulWad fuel x y with
     | Except.ok r => observed_outcome r
     | Except.error _ => Outcome.revert) = mulWad_spec x y := by
  simp [run_mulWad, execute_transaction_calldata]
  sorry

/--
**Goal:** For sufficient fuel, executing the solc-generated runtime bytecode
matches the functional spec `mulWad_spec`.

This is the “bytecode-level correctness” statement.
-/
theorem mulWad_bytecode_correct (fuel : Nat) (x y : UInt256) :
    run_mulWad_outcome fuel x y = mulWad_spec x y := by
  simp [run_mulWad_outcome, run_mulWad, execute_transaction_calldata]
  set code := mulWad_bytecode
  set cd := mulWad_calldata x y
  set env := make_execution_env code cd
  set jumps := D_J env.code ⟨0⟩
  set s0 : EVM.State :=
    { (default : EVM.State) with
      executionEnv := env
      gasAvailable := UInt256.ofNat (10 ^ 9) }

  cases hX : X fuel jumps s0 with
  | error e =>
      simp
      sorry
  | ok r =>
      simp
      sorry



end Solady.Proofs
