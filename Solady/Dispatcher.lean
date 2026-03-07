import Mathlib

import EvmYul.EVM.Semantics
import EvmYul.EVM.State
import EvmYul.State.ExecutionEnv
import EvmYul.State.BlockHeader
import EvmYul.UInt256

import Solady.Bytes
import Solady.EvmUtils

namespace Solady.Dispatcher

open EvmYul
open EvmYul.EVM
open Solady.Bytes
open Solady.EvmUtils

/-! ## Standardized harness layout

All harness contracts use `function run(uint256 x, uint256 y) external pure returns (uint256)`.
The solc output has a fixed structure:

| Region        | Byte range            | Description                                      |
|---------------|-----------------------|--------------------------------------------------|
| Dispatcher    | `0  ..< 91`          | callvalue/calldatasize/selector, wrapper, encoder |
| Body          | `91 ..< 91 + N`      | Core function logic (varies per function)         |
| ABI decoder   | `91 + N ..< end`      | Decode two uint256 from calldata + metadata       |

The dispatcher region (bytes 0–90) and ABI decoder structure are identical across
all standardized harnesses. Only the body and the one-byte offset that jumps into
the decoder change between functions.

We extract each region dynamically from the full trusted bytecode using
`ByteArray.extract`, so there is no duplication.
-/

/-- Selector for `run(uint256,uint256)`. Shared across all standardized harnesses. -/
def std_selector : UInt32 := 0x7357f5d2

/-- Start offset of the function body in all standardized harnesses. -/
def body_start : Nat := 91

/-- Extract the dispatcher region (bytes 0..91) from a full bytecode. -/
def dispatcher_of (code : ByteArray) : ByteArray := code.extract 0 body_start

/-- Extract the function body (bytes 91..91+body_size) from a full bytecode. -/
def body_of (code : ByteArray) (body_size : Nat) : ByteArray :=
  code.extract body_start (body_start + body_size)

/-- Extract the ABI decoder + metadata (bytes 91+body_size..end) from a full bytecode. -/
def decoder_of (code : ByteArray) (body_size : Nat) : ByteArray :=
  code.extract (body_start + body_size) code.size

lemma extract_transitivity (code : ByteArray) (a b c : Nat) (h : a ≤ b) (h' : b ≤ c) :
  code.extract a b ++ code.extract b c = code.extract a c := by
  simp [ByteArray.extract, ByteArray.copySlice, HAppend.hAppend]
  -- ⊢ Append.append { data := Append.append (Append.append #[] (code.data.extract a (a + (b - a)))) #[] }
  --     { data := Append.append (Append.append #[] (code.data.extract b (b + (c - b)))) #[] } =
  --   { data := Append.append (Append.append #[] (code.data.extract a (a + (c - a)))) #[] }
  sorry


/-- A full bytecode decomposes into dispatcher ++ body ++ decoder. -/
theorem bytecode_split (code : ByteArray) (body_size : Nat)
    (h : body_start + body_size ≤ code.size) :
    code = dispatcher_of code ++ body_of code body_size ++ decoder_of code body_size := by
  simp [dispatcher_of, body_of, decoder_of]
  sorry



/-- Standard calldata: std_selector ++ x ++ y (same for all standardized harnesses). -/
def std_calldata (x y : UInt256) : ByteArray :=
  (selector_bytes std_selector) ++ (abi_word x) ++ (abi_word y)

/-- Run a standardized harness bytecode with ABI calldata and map to `Outcome`. -/
def run_harness (code : ByteArray) (fuel : Nat) (x y : UInt256) : Outcome :=
  match execute_transaction_calldata fuel code (std_calldata x y) with
    | .ok r => observed_outcome r
    | .error _ => .revert

/--
**Dispatcher correctness (to be proven once):**
For sufficient fuel and calldata = std_selector ++ x ++ y, executing any standardized
bytecode yields the same outcome as running just the body with (y, x) on stack and
then ABI-encoding the result.

The exact formulation will be refined as we make progress on the symbolic execution.
-/
theorem std_harness_correct (code : ByteArray) (body_size : Nat) (fuel : Nat) (x y : UInt256)
    (result : UInt256) (hfuel : fuel ≥ 200) :
    run_harness code fuel x y = Outcome.ok result ↔ True := by
  sorry

end Solady.Dispatcher
