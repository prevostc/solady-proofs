import Mathlib
import EvmYul.UInt256
import Solady.MulWad
import Solady.UInt256Utils

namespace Solady.Proofs
open EvmYul
open EvmYul.UInt256.Utils

/-! ## mulWad-specific constants -/

theorem U256_MAX_toNat : U256_MAX.toNat = 2 ^ 256 - 1 :=
  toNat_eq_ofNat _ (by unfold UInt256.size; omega)

theorem WAD_toNat : WAD.toNat = 10 ^ 18 :=
  toNat_eq_ofNat _ (by unfold UInt256.size; omega)

private theorem U256_MAX_div_toNat (y : UInt256) :
    (U256_MAX / y).toNat = (2 ^ 256 - 1) / y.toNat := by
  rw [div_toNat, U256_MAX_toNat]

/-! ## Guard condition bridge -/

private theorem guard_iff (x y : UInt256) :
    (y ≠ ⟨0⟩ ∧ x > U256_MAX / y) ↔
    (y.toNat ≠ 0 ∧ x.toNat > (2 ^ 256 - 1) / y.toNat) := by
  constructor
  · intro ⟨hne, hgt⟩
    exact ⟨(eq_zero_iff y).not.mp hne, by rwa [gt_iff, U256_MAX_div_toNat] at hgt⟩
  · intro ⟨hne, hgt⟩
    exact ⟨(eq_zero_iff y).not.mpr hne, by rwa [gt_iff, U256_MAX_div_toNat]⟩

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
    apply UInt256.Utils.ext
    rw [div_toNat, mul_toNat_of_le x y h]
    have hdiv_lt : (x.toNat * y.toNat) / (10 ^ 18) < UInt256.size :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (mul_lt_size x y h)
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
