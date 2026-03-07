import Mathlib
import EvmYul.UInt256
import Solady.MulWad

namespace Solady.Proofs
open EvmYul

/-! ## Helper lemmas about UInt256 arithmetic -/

set_option linter.style.nativeDecide false in
theorem U256_MAX_toNat : U256_MAX.toNat = 2 ^ 256 - 1 := by native_decide

set_option linter.style.nativeDecide false in
theorem WAD_toNat : WAD.toNat = 10 ^ 18 := by native_decide

private theorem div_toNat (a b : UInt256) :
    (a / b).toNat = a.toNat / b.toNat := rfl

private theorem U256_MAX_div_toNat (y : UInt256) :
    (U256_MAX / y).toNat = (2 ^ 256 - 1) / y.toNat := by
  rw [div_toNat, U256_MAX_toNat]

private theorem gt_iff (a b : UInt256) :
    a > b ↔ a.toNat > b.toNat := Iff.rfl

private theorem UInt256_eq_zero_iff (a : UInt256) :
    a = ⟨0⟩ ↔ a.toNat = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h
    cases a with | mk v =>
    have hv : v.val = 0 := h
    exact congrArg UInt256.mk (Fin.ext hv)

/-! ## Guard condition bridge -/

private theorem guard_iff (x y : UInt256) :
    (y ≠ ⟨0⟩ ∧ x > U256_MAX / y) ↔
    (y.toNat ≠ 0 ∧ x.toNat > (2 ^ 256 - 1) / y.toNat) := by
  constructor
  · intro ⟨hne, hgt⟩
    exact ⟨(UInt256_eq_zero_iff y).not.mp hne, by rwa [gt_iff, U256_MAX_div_toNat] at hgt⟩
  · intro ⟨hne, hgt⟩
    exact ⟨(UInt256_eq_zero_iff y).not.mpr hne, by rwa [gt_iff, U256_MAX_div_toNat]⟩

private theorem guard_false_iff (x y : UInt256) :
    ¬(y ≠ ⟨0⟩ ∧ x > U256_MAX / y) ↔
    (y.toNat = 0 ∨ x.toNat ≤ (2 ^ 256 - 1) / y.toNat) := by
  rw [guard_iff]
  push_neg
  constructor
  · intro h
    by_cases hy : y.toNat = 0
    · exact Or.inl hy
    · exact Or.inr (h hy)
  · intro h hne
    cases h with
    | inl hy => exact absurd hy hne
    | inr hle => exact hle

/-! ## No-overflow multiplication -/

theorem mul_no_overflow (x y : UInt256)
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

private theorem ofNat_toNat_of_lt (n : Nat) (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  simp [UInt256.ofNat, UInt256.toNat, Id.run, Fin.ofNat]
  exact Nat.mod_eq_of_lt h

private theorem UInt256_ext (a b : UInt256) (h : a.toNat = b.toNat) : a = b := by
  cases a with | mk aval => cases b with | mk bval =>
  exact congrArg UInt256.mk (Fin.ext h)

/-! ## Main theorems -/

/--
**Success case:** when the overflow guard does NOT trigger, `mulWad` returns
the mathematically correct fixed-point product `(x * y) / WAD`.
-/
theorem mulWad_ok (x y : UInt256)
    (h : y.toNat = 0 ∨ x.toNat ≤ (2 ^ 256 - 1) / y.toNat) :
    mulWad x y = .ok (UInt256.ofNat ((x.toNat * y.toNat) / (10 ^ 18))) := by
  unfold mulWad
  have hguard : ¬(y ≠ ⟨0⟩ ∧ x > U256_MAX / y) :=
    (guard_false_iff x y).mpr h
  split
  · exact absurd ‹_› hguard
  · congr 1
    apply UInt256_ext
    rw [div_toNat, mul_no_overflow x y h]
    have hprod_lt : x.toNat * y.toNat < UInt256.size := by
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
    have hdiv_lt : (x.toNat * y.toNat) / (10 ^ 18) < UInt256.size :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hprod_lt
    rw [WAD_toNat, ofNat_toNat_of_lt _ hdiv_lt]

/--
**Revert case:** when `y ≠ 0` and `x` exceeds the overflow bound, `mulWad` reverts.
-/
theorem mulWad_reverts (x y : UInt256)
    (hyne : y.toNat ≠ 0) (hgt : x.toNat > (2 ^ 256 - 1) / y.toNat) :
    mulWad x y = .revert := by
  unfold mulWad
  have hguard : y ≠ ⟨0⟩ ∧ x > U256_MAX / y :=
    (guard_iff x y).mpr ⟨hyne, hgt⟩
  split
  · rfl
  · exact absurd hguard ‹_›

end Solady.Proofs
