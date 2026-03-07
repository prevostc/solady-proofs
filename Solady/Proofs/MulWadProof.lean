import Mathlib

import EvmYul.EVM.Semantics
import EvmYul.EVM.State
import EvmYul.State.ExecutionEnv
import EvmYul.State.BlockHeader
import EvmYul.UInt256

import Solady.Bytes
import Solady.EvmUtils
import Solady.Specs.MulWadSpec
import Solady.Code.MulWadCode
import Solady.Dispatcher

namespace Solady.Proofs

open EvmYul
open EvmYul.EVM

open Solady.Bytes
open Solady.EvmUtils
open Solady.Code
open Solady.Specs
open Solady.Dispatcher

/-! ## mulWad bytecode decomposition

The body lives at bytes 91–135 of `mulWad_bytecode` (45 bytes).
All regions are extracted dynamically from the single trusted bytecode array.
-/

/-- Size of the mulWad function body in the compiled bytecode. -/
def mulWad_body_size : Nat := 45

set_option linter.style.nativeDecide false in
/--
The full mulWad bytecode decomposes into dispatcher ++ body ++ decoder.
Each piece is extracted from the same trusted bytecode via `ByteArray.extract`.
-/
theorem mulWad_bytecode_split :
    mulWad_bytecode =
      dispatcher_of mulWad_bytecode
        ++ body_of mulWad_bytecode mulWad_body_size
        ++ decoder_of mulWad_bytecode mulWad_body_size :=
  bytecode_split mulWad_bytecode mulWad_body_size (by native_decide)

/--
The valid jump destinations for `mulWad_bytecode`.
`D_J` is `partial` and therefore opaque to the Lean kernel.
-/
axiom mulWad_valid_jumps :
    D_J mulWad_bytecode ⟨0⟩ =
      #[⟨14⟩, ⟨38⟩, ⟨42⟩, ⟨53⟩, ⟨57⟩, ⟨75⟩, ⟨84⟩, ⟨91⟩, ⟨120⟩, ⟨136⟩, ⟨152⟩]

/-! ## Layer 2: Arithmetic correspondence -/

/--
When the no-overflow condition holds, `x * y` does not exceed `2^256 - 1`,
so UInt256 (mod 2^256) multiplication agrees with natural multiplication.
-/
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

private theorem ofNat_toNat (n : Nat) :
    (UInt256.ofNat n).toNat = n % UInt256.size := by
  simp [UInt256.ofNat, UInt256.toNat, Id.run, Fin.ofNat]

private theorem ofNat_toNat_of_lt (n : Nat) (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  rw [ofNat_toNat, Nat.mod_eq_of_lt h]

private theorem div_toNat (a b : UInt256) :
    (UInt256.div a b).toNat = a.toNat / b.toNat := by
  simp [UInt256.div, UInt256.toNat]

private theorem UInt256_ext (a b : UInt256) (h : a.toNat = b.toNat) : a = b := by
  cases a with | mk aval => cases b with | mk bval =>
  simp [UInt256.toNat] at h
  exact congrArg UInt256.mk (Fin.ext h)

/--
The core arithmetic identity: under the no-overflow condition,
`UInt256.ofNat ((x * y) / WAD)` equals the EVM computation
`(x * y) / UInt256.ofNat WAD` (where `*` and `/` are UInt256 ops).
-/
theorem mulWad_arith (x y : UInt256)
    (h : y.toNat = 0 ∨ x.toNat ≤ (2 ^ 256 - 1) / y.toNat) :
    Outcome.ok (UInt256.ofNat ((x.toNat * y.toNat) / WAD)) =
    Outcome.ok ((x * y) / UInt256.ofNat WAD) := by
  congr 1
  have hmul := mul_no_overflow x y h
  symm
  apply UInt256_ext
  change (UInt256.div (x * y) (UInt256.ofNat WAD)).toNat =
    (UInt256.ofNat ((x.toNat * y.toNat) / WAD)).toNat
  rw [div_toNat, hmul]
  have hWAD_lt : WAD < UInt256.size := by unfold WAD UInt256.size; omega
  rw [ofNat_toNat_of_lt WAD hWAD_lt]
  have hprod_lt : x.toNat * y.toNat < UInt256.size := by
    rw [← hmul]; exact (x * y).val.isLt
  have hdiv_lt : (x.toNat * y.toNat) / WAD < UInt256.size :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hprod_lt
  rw [ofNat_toNat_of_lt _ hdiv_lt]

#print mulWad_arith
/-! ## Layer 3: Spec equivalence of overflow conditions -/

/--
The EVM overflow check `!(x > (NOT 0) / y) || y == 0` is equivalent
to the spec condition `y = 0 ∨ x ≤ U256_MAX / y`.
-/
theorem overflow_check_equiv (x y : UInt256) :
    (y.toNat = 0 ∨ x.toNat ≤ U256_MAX / y.toNat) ↔
    (y.toNat = 0 ∨ x.toNat ≤ (2 ^ 256 - 1) / y.toNat) := by
  simp [U256_MAX]

/-! ## Layer 4: Main bytecode correctness theorem -/

/--
**EVM execution lemma (success case):**
For sufficient fuel and inputs satisfying the no-overflow condition,
executing mulWad bytecode produces `.success` with the correct return data.
-/
theorem mulWad_exec_ok (fuel : Nat) (x y : UInt256)
    (hfuel : fuel ≥ 200)
    (hno_overflow : y.toNat = 0 ∨ x.toNat ≤ U256_MAX / y.toNat) :
    run_harness mulWad_bytecode fuel x y =
      Outcome.ok ((x * y) / UInt256.ofNat WAD) := by
  sorry

/--
**EVM execution lemma (revert case):**
For sufficient fuel and inputs that DO overflow,
executing mulWad bytecode produces a revert.
-/
theorem mulWad_exec_revert (fuel : Nat) (x y : UInt256)
    (hfuel : fuel ≥ 200)
    (hoverflow : ¬(y.toNat = 0 ∨ x.toNat ≤ U256_MAX / y.toNat)) :
    run_harness mulWad_bytecode fuel x y = Outcome.revert := by
  sorry

/--
**Goal:** For sufficient fuel, executing the solc-generated runtime bytecode
matches the functional spec `mulWad_spec`.
-/
theorem mulWad_bytecode_correct (fuel : Nat) (x y : UInt256)
    (hfuel : fuel ≥ 200) :
    run_harness mulWad_bytecode fuel x y = mulWad_spec x y := by
  simp only [mulWad_spec]
  by_cases hcond : y.toNat = 0 ∨ x.toNat ≤ U256_MAX / y.toNat
  · rw [if_pos hcond]
    rw [mulWad_exec_ok fuel x y hfuel hcond]
    exact (mulWad_arith x y ((overflow_check_equiv x y).mp hcond)).symm
  · rw [if_neg hcond]
    exact mulWad_exec_revert fuel x y hfuel hcond

#print mulWad_bytecode_correct

end Solady.Proofs
