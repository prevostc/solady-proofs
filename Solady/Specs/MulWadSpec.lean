import Mathlib
import EvmYul.UInt256
import Solady.EvmUtils

namespace Solady.Specs

open EvmYul
open Solady.EvmUtils

/--
Functional spec:

- if overflow condition triggers: revert
- else: return floor((x*y)/WAD)
-/
def mulWad_spec (xu yu : UInt256) : Outcome :=
  let x := xu.toNat
  let y := yu.toNat
  -- require(y == 0 || x <= type(uint256).max / y)
  if y = 0 ∨ x <= (U256_MAX / y) then
    .ok (UInt256.ofNat ((x * y) / WAD))
  else
    .revert

end Solady.Specs
