import EvmYul.Yul.Ast
import EvmYul.Yul.YulNotation

namespace Solady.Code
open EvmYul.Yul.Ast
open EvmYul.Yul.Notation

/--
Solady `FixedPointMathLib.mulWad` assembly, transcribed verbatim:

```solidity
function mulWad(uint256 x, uint256 y) internal pure returns (uint256 z) {
    assembly {
        if gt(x, div(not(0), y)) {
            if y {
                mstore(0x00, 0xbac65e5b) // MulWadFailed()
                revert(0x1c, 0x04)
            }
        }
        z := div(mul(x, y), WAD)
    }
}
```
-/
def mulWad_yul : FunctionDefinition := <f
  function mulWad(x, y) -> z {
    if gt(x, div(not(0), y)) {
      if y {
        mstore(0, 0xbac65e5b)
        revert(28, 4)
      }
    }
    z := div(mul(x, y), 1000000000000000000)
  }
>

end Solady.Code
