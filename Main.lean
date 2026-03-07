import Solady.MulWad
import Solady.Code.MulWadYul

open Solady
open EvmYul


#eval mulWad (⟨3 * 10 ^ 18⟩) (⟨7 * 10 ^ 18⟩)
-- expected: .ok 21000000000000000000

#eval mulWad (⟨0⟩) (⟨7 * 10 ^ 18⟩)
-- expected: .ok 0

#eval mulWad (⟨10 ^ 18⟩) (⟨10 ^ 18⟩)
-- expected: .ok 1000000000000000000 (= 10^18, i.e. 1.0 * 1.0 = 1.0)

#eval mulWad (⟨2 ^ 256 - 1⟩) (⟨2 * 10 ^ 18⟩)
-- expected: .revert (overflow)

#eval mulWad (⟨42⟩) (⟨0⟩)
-- expected: .ok 0 (y=0 → no overflow, result is 0)
