import Mathlib
import EvmYul.UInt256
import Solady.EvmUtils
import Solady.Code.MulWadCode
import Solady.Dispatcher
import Solady.Proofs.MulWadProof

open Solady
open EvmYul

def main : IO Unit := do
  let fuel := 200000
  let WAD := (10^18)
  let x := UInt256.ofNat (3 * WAD)
  let y := UInt256.ofNat (7 * WAD)
  let expected := UInt256.ofNat (21 * WAD)
  let result := Dispatcher.run_harness Code.mulWad_bytecode fuel x y
  IO.println s!"run_harness mulWad_bytecode {fuel} {x} {y}"
  match result with
  | .ok e => if e = expected
    then IO.println s!"Success: {e}" else IO.println s!"Failed: {e}"
  | .revert => IO.println s!"Reverted"
