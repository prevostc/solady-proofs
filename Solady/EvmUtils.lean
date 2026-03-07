import Mathlib

import EvmYul.EVM.Semantics
import EvmYul.EVM.State
import EvmYul.State.ExecutionEnv
import EvmYul.State.BlockHeader
import EvmYul.UInt256

import Solady.Bytes

namespace Solady.EvmUtils

open EvmYul
open EvmYul.EVM

open Solady.Bytes

/-- 10^18 (WAD). -/
def WAD : Nat := 10 ^ 18

/-- max uint256 as a Nat. -/
def U256_MAX : Nat := (2 ^ 256) - 1

/-- Encode a 4-byte function selector (UInt32) big-endian. -/
def selector_bytes (s : UInt32) : ByteArray :=
  nat_to_bytes_be_to_byte_array s.toNat 4

theorem selector_bytes_size (s : UInt32) :
    (selector_bytes s).size = 4 := by
  simp [selector_bytes, nat_to_bytes_be_to_byte_array_size]

/-- ABI-encode uint256 as a 32-byte big-endian word. -/
def abi_word (x : UInt256) : ByteArray :=
  nat_to_bytes_be_to_byte_array x.toNat 32

theorem abi_word_size (x : UInt256) :
    (abi_word x).size = 32 := by
  simp [abi_word, nat_to_bytes_be_to_byte_array_size]

/--
Decode a uint256 ABI return value (expects exactly 32 bytes).
If length mismatches, returns 0 (you can tighten this later).
-/
def decode_return_U256 (ret : ByteArray) : UInt256 :=
  if ret.size = 32 then
    UInt256.ofNat (bytes_to_nat_be ret)
  else
    UInt256.ofNat 0


/-! ## EVM execution harness -/

/-- A minimal block header; sufficient for pure arithmetic code. -/
def dummy_block_header : BlockHeader := default

/-- Construct an execution environment for a single message call. -/
def make_execution_env (code calldata : ByteArray) : ExecutionEnv .EVM :=
  { codeOwner := default
    sender := default
    source := default
    weiValue := UInt256.ofNat 0
    calldata := calldata
    code := code
    gasPrice := 0
    header := dummy_block_header
    depth := 0
    perm := true
    blobVersionedHashes := [] }

/--
Run code using `EVM.X` for a fixed fuel amount.

Returns either an `ExecutionException` or an `ExecutionResult`.
-/
def execute_transaction_calldata (fuel : Nat) (code calldata : ByteArray) :
    Except EVM.ExecutionException (EVM.ExecutionResult EVM.State) := do
  let env := make_execution_env code calldata
  let s0 : EVM.State :=
    { (default : EVM.State) with
      executionEnv := env
      gasAvailable := UInt256.ofNat (10 ^ 9) }
  let validJumps := D_J env.code ⟨0⟩
  X fuel validJumps s0


/--
Spec-level outcome: either returns a uint256, or reverts.
(We don’t model the exact revert data here yet — just “it reverts”.)
-/
inductive Outcome where
  | ok (z : UInt256) : Outcome
  | revert : Outcome
  deriving Repr, BEq, DecidableEq


/--
Map an EVM execution result to your spec `Outcome`.

- success ⇒ ok(decoded return)
- revert  ⇒ revert
- anything else ⇒ revert (conservative; you can refine later)
-/
def observed_outcome (r : EVM.ExecutionResult EVM.State) : Outcome :=
  match r with
  | .success _ ret => .ok (decode_return_U256 ret)
  | .revert _ _    => .revert
  -- | _              => .revert


end Solady.EvmUtils
