import Mathlib
import EvmYul.UInt256
import Solady.EvmUtils
import Solady.Code.MulWadCode
import Solady.Proofs.MulWadProof

open Solady
open EvmYul

def main : IO Unit := do
  let fuel := 200000
  let WAD := (10^18)
  let x := UInt256.ofNat (3 * WAD)
  let y := UInt256.ofNat (7 * WAD)
  let expected := UInt256.ofNat (21 * WAD)
  let result: Except EVM.ExecutionException Outcome := runMulWadOutcome fuel x y
  IO.println s!"runMulWadOutcome {fuel} {x} {y} "
  match result with
  | .ok (Outcome.ok e) => if e = expected
    then IO.println s!"Success: {e}" else IO.println s!"Failed: {e}"
  | .ok (Outcome.revert) => IO.println s!"Reverted"
  | _ => IO.println s!"Error"
