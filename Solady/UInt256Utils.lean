import Mathlib
import EvmYul.UInt256

/-!
# Generic UInt256 lemmas

Reusable facts about `EvmYul.UInt256` arithmetic that are not
specific to any particular Solidity function.
-/

namespace EvmYul.UInt256.Utils
open EvmYul

theorem toNat_eq_ofNat (n : Nat) (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  simp [UInt256.ofNat, UInt256.toNat, Id.run, Fin.ofNat]
  exact Nat.mod_eq_of_lt h

theorem ofNat_eq_toNat (n : Nat) :
    UInt256.ofNat n = UInt256.ofNat (n % UInt256.size) := by
  simp [UInt256.ofNat, Id.run, Fin.ofNat]


theorem div_toNat (a b : UInt256) :
    (a / b).toNat = a.toNat / b.toNat := rfl

theorem gt_iff (a b : UInt256) :
    a > b ↔ a.toNat > b.toNat := Iff.rfl

theorem eq_zero_iff (a : UInt256) :
    a = ⟨0⟩ ↔ a.toNat = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h
    cases a with | mk v =>
    have hv : v.val = 0 := h
    exact congrArg UInt256.mk (Fin.ext hv)

theorem ext (a b : UInt256) (h : a.toNat = b.toNat) : a = b := by
  cases a with | mk aval => cases b with | mk bval =>
  exact congrArg UInt256.mk (Fin.ext h)

theorem ofNat_toNat_of_lt (n : Nat) (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  simp [UInt256.ofNat, UInt256.toNat, Id.run, Fin.ofNat]
  exact Nat.mod_eq_of_lt h

/--
When the product `x * y` does not overflow modulo `2^256`,
`UInt256` multiplication agrees with `Nat` multiplication.
-/
theorem mul_toNat_of_le (x y : UInt256)
    (h : y.toNat = 0 ∨ x.toNat ≤ (2 ^ 256 - 1) / y.toNat) :
    (x * y).toNat = x.toNat * y.toNat := by
  have hlt : x.toNat * y.toNat < UInt256.size := by
    cases h with
    | inl hy =>
      rw [hy, Nat.mul_zero]
      exact Nat.pos_of_ne_zero (by unfold UInt256.size; omega)
    | inr hle =>
      by_cases hy0 : y.toNat = 0
      · rw [hy0, Nat.mul_zero]
        exact Nat.pos_of_ne_zero (by unfold UInt256.size; omega)
      · calc x.toNat * y.toNat
            ≤ ((2 ^ 256 - 1) / y.toNat) * y.toNat := Nat.mul_le_mul_right _ hle
          _ ≤ 2 ^ 256 - 1 := Nat.div_mul_le_self _ _
          _ < 2 ^ 256 := by omega
  change (⟨x.val * y.val⟩ : UInt256).toNat = x.toNat * y.toNat
  simp only [UInt256.toNat]
  show (x.val * y.val).val = x.val.val * y.val.val
  rw [Fin.val_mul]
  exact Nat.mod_eq_of_lt hlt

/-- The product is bounded by `UInt256.size` under the no-overflow condition. -/
theorem mul_lt_size (x y : UInt256)
    (h : y.toNat = 0 ∨ x.toNat ≤ (2 ^ 256 - 1) / y.toNat) :
    x.toNat * y.toNat < UInt256.size := by
  cases h with
  | inl hy =>
    rw [hy, Nat.mul_zero]
    exact Nat.pos_of_ne_zero (by unfold UInt256.size; omega)
  | inr hle =>
    by_cases hy0 : y.toNat = 0
    · rw [hy0, Nat.mul_zero]
      exact Nat.pos_of_ne_zero (by unfold UInt256.size; omega)
    · calc x.toNat * y.toNat
          ≤ ((2 ^ 256 - 1) / y.toNat) * y.toNat := Nat.mul_le_mul_right _ hle
        _ ≤ 2 ^ 256 - 1 := Nat.div_mul_le_self _ _
        _ < 2 ^ 256 := by omega

end EvmYul.UInt256.Utils
