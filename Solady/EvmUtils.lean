import Mathlib

import EvmYul.EVM.Semantics
import EvmYul.EVM.State
import EvmYul.State.ExecutionEnv
import EvmYul.State.BlockHeader
import EvmYul.UInt256

namespace Solady

open EvmYul
open EvmYul.EVM

/-! ## ABI encoding helpers (big-endian) -/

/-- Big-endian fixed-length encoding of a Nat into `len` bytes. -/
def natToBytesBE (len : Nat) (n : Nat) : ByteArray :=
  Id.run do
    let mut out : Array UInt8 := Array.mkEmpty len
    let mut v := n
    for _i in [:len] do
      out := out.push (UInt8.ofNat (v % 256))
      v := v / 256
    return ByteArray.mk out.reverse

/-- Decode a big-endian byte array into Nat. -/
def bytesToNatBE (b : ByteArray) : Nat :=
  Id.run do
    let mut acc : Nat := 0
    for byte in b.data do
      acc := acc * 256 + byte.toNat
    return acc

/-- Encode a 4-byte function selector (UInt32) big-endian. -/
def selectorBytes (s : UInt32) : ByteArray :=
  natToBytesBE 4 s.toNat

/-- ABI-encode uint256 as a 32-byte big-endian word. -/
def abiWord (x : UInt256) : ByteArray :=
  natToBytesBE 32 x.toNat

/--
Decode a uint256 ABI return value (expects exactly 32 bytes).
If length mismatches, returns 0 (you can tighten this later).
-/
def decodeReturnU256 (ret : ByteArray) : UInt256 :=
  if ret.size = 32 then
    UInt256.ofNat (bytesToNatBE ret)
  else
    UInt256.ofNat 0


/-! ## EVM execution harness -/

/-- A minimal block header; sufficient for pure arithmetic code. -/
def dummyHeader : BlockHeader := default

/-- Construct an execution environment for a single message call. -/
def mkEnv (code calldata : ByteArray) : ExecutionEnv .EVM :=
  { codeOwner := default
    sender := default
    source := default
    weiValue := UInt256.ofNat 0
    calldata := calldata
    code := code
    gasPrice := 0
    header := dummyHeader
    depth := 0
    perm := true
    blobVersionedHashes := [] }

/--
Run code using `EVM.X` for a fixed fuel amount.

Returns either an `ExecutionException` or an `ExecutionResult`.
-/
def runCode (fuel : Nat) (code calldata : ByteArray) :
    Except EVM.ExecutionException (EVM.ExecutionResult EVM.State) := do
  let env := mkEnv code calldata
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
  deriving Repr, BEq


/--
Map an EVM execution result to your spec `Outcome`.

- success ⇒ ok(decoded return)
- revert  ⇒ revert
- anything else ⇒ revert (conservative; you can refine later)
-/
def observedOutcome (r : EVM.ExecutionResult EVM.State) : Outcome :=
  match r with
  | .success _ ret => .ok (decodeReturnU256 ret)
  | .revert _ _    => .revert
  -- | _              => .revert


end Solady
