import EvmYul.UInt256
import Solady.Proofs.UInt256

namespace Solady
open EvmYul
open Solady.Proofs.UInt256


inductive MulWadResult where
  | ok (z : UInt256)
  | revert
  deriving Repr, BEq, DecidableEq

/--
Pure Lean mirror of Solady's `mulWad` assembly.
Each UInt256 op (`>`, `*`, `/`, `!=`) matches the corresponding
Yul primitive (`gt`, `mul`, `div`, `iszero`).
-/
def mulWad (x y : UInt256) : MulWadResult :=
  if y ≠ ⟨0⟩ ∧ x > U256_MAX / y then .revert
  else .ok ((x * y) / WAD)

end Solady
