import Mathlib
import EvmYul.UInt256
import Solady.MulWad
import Solady.Proofs.UInt256

namespace Solady.Proofs
open EvmYul
open Solady.Proofs.UInt256

/-! ## Guard condition bridge -/

/-- The product is bounded by `UInt256.size` under the no-overflow condition. -/
theorem mul_lt_size (x y : UInt256)
    (h : y.toNat = 0 ∨ x.toNat ≤ (2 ^ 256 - 1) / y.toNat) :
    x.toNat * y.toNat < UInt256.size := by
  cases h with
  | inl h₀ =>
    rw [h₀, Nat.mul_zero]
    exact Nat.pos_of_ne_zero (by unfold UInt256.size; omega)
  | inr h₁ =>
    by_cases h₀ : y.toNat = 0
    · rw [h₀, Nat.mul_zero]
      exact Nat.pos_of_ne_zero (by unfold UInt256.size; omega)
    · calc x.toNat * y.toNat
          ≤ ((2 ^ 256 - 1) / y.toNat) * y.toNat := Nat.mul_le_mul_right _ h₁
        _ ≤ 2 ^ 256 - 1 := Nat.div_mul_le_self _ _
        _ < 2 ^ 256 := by omega

private theorem guard_iff (x y : UInt256) :
    (y ≠ ⟨0⟩ ∧ x > U256_MAX / y) ↔
    (y.toNat ≠ 0 ∧ x.toNat > (2 ^ 256 - 1) / y.toNat) := by
  simp only [ne_eq, zero_iff, gt_iff, toNat_div]
  sorry

private theorem guard_false_iff (x y : UInt256) :
    ¬(y ≠ ⟨0⟩ ∧ x > U256_MAX / y) ↔
    (y.toNat = 0 ∨ x.toNat ≤ (2 ^ 256 - 1) / y.toNat) := by
  rw [guard_iff]; push_neg
  constructor
  · intro h₁
    by_cases h₂ : y.toNat = 0
    · exact Or.inl h₂
    · exact Or.inr (h₁ h₂)
  · intro h₁ h₂
    cases h₁ with
    | inl h₃ => exact absurd h₃ h₂
    | inr h₃ => exact h₃

/-! ## Main theorems -/

/--
**Success case:** when the overflow guard does NOT trigger, `mulWad` returns
the mathematically correct fixed-point product `(x * y) / WAD`.
-/
theorem mulWad_ok (x y : UInt256)
    (h : y.toNat = 0 ∨ x.toNat ≤ (2 ^ 256 - 1) / y.toNat) :
    mulWad x y = .ok (UInt256.ofNat ((x.toNat * y.toNat) / (10 ^ 18))) := by
  unfold mulWad
  have h₁ : ¬(y ≠ ⟨0⟩ ∧ x > U256_MAX / y) := (guard_false_iff x y).mpr h
  have hlt := mul_lt_size x y h
  split
  · exact absurd ‹_› h₁
  · congr 1; apply ext_toNat
    sorry
    --simp [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt)]

/--
**Revert case:** when `y ≠ 0` and `x` exceeds the overflow bound, `mulWad` reverts.
-/
theorem mulWad_reverts (x y : UInt256)
    (h₁ : y.toNat ≠ 0) (h₂ : x.toNat > (2 ^ 256 - 1) / y.toNat) :
    mulWad x y = .revert := by
  unfold mulWad
  have h₃ : y ≠ ⟨0⟩ ∧ x > U256_MAX / y := (guard_iff x y).mpr ⟨h₁, h₂⟩
  split
  · rfl
  · exact absurd h₃ ‹_›

end Solady.Proofs
