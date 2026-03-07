import EvmYul.UInt256

namespace Solady
open EvmYul

def U256_MAX : UInt256 := UInt256.ofNat (2 ^ 256 - 1)
def WAD : UInt256 := UInt256.ofNat (10 ^ 18)

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
