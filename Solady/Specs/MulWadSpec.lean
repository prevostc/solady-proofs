import Mathlib
import EvmYul.UInt256
import Solady.EvmUtils

namespace Solady

open EvmYul

/-- 10^18 (WAD). -/
def WAD : Nat := 10 ^ 18

/-- max uint256 as a Nat. -/
def U256_MAX : Nat := (2 ^ 256) - 1

/--
Functional spec:

- if overflow condition triggers: revert
- else: return floor((x*y)/WAD)
-/
def mulWadSpec (xu yu : UInt256) : Outcome :=
  let x := xu.toNat
  let y := yu.toNat
  -- require(y == 0 || x <= type(uint256).max / y)
  if y = 0 ∨ x <= (U256_MAX / y) then
    .ok (UInt256.ofNat ((x * y) / WAD))
  else
    .revert

end Solady
