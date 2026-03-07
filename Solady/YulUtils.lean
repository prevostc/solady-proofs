import Mathlib
import EvmYul.UInt256

/-!
# Generic Yul ↔ Lean bridge lemmas

Reusable lemmas connecting `EvmYul.UInt256` EVM-style operations
(which return `UInt256` 0/1) with Lean `Prop`-returning comparisons.
-/

namespace EvmYul.UInt256.YulBridge
open EvmYul

/-- `UInt256.gt a b ≠ 0` iff `a > b` in the Lean sense. -/
theorem gt_ne_zero_iff (a b : UInt256) :
    (UInt256.gt a b ≠ ⟨0⟩) ↔ a > b := by
  simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256]
  split
  · constructor
    · intro _; assumption
    · intro _
      simp [UInt256.ofNat, Id.run, Fin.ofNat]
      decide
  · constructor
    · intro h; exact absurd rfl h
    · intro h; exact absurd h (by assumption)

/-- `UInt256.lnot 0 = 2^256 − 1`. -/
theorem lnot_zero :
    UInt256.lnot ⟨0⟩ = UInt256.ofNat (2 ^ 256 - 1) := by
  simp [UInt256.lnot, UInt256.ofNat, Id.run, Fin.ofNat, UInt256.size]
  rfl

end EvmYul.UInt256.YulBridge
