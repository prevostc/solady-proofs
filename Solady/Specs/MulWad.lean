import EvmYul.UInt256
import Solady.Proofs.UInt256

namespace Solady
open EvmYul
open Solady.Proofs.UInt256

def U256_MAX : ℕ := 2 ^ 256 - 1
def WAD : ℕ := 10 ^ 18

def mulWad (x y : ℕ) : Option ℕ :=
  if x * y > U256_MAX then none
  else some (x * y / WAD)

end Solady
