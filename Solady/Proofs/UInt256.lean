import Mathlib
import EvmYul.UInt256

/-!
# Generic UInt256 lemmas

Reusable facts about `EvmYul.UInt256` arithmetic that are not
specific to any particular Solidity function.

## Strategy

`UInt256` is a thin wrapper around `Fin UInt256.size`.  We provide two
layers of `@[simp]` lemmas so that goals about `UInt256` reduce first
to `Fin` (Layer 1) and then to `ℕ` modular arithmetic (Layer 2, from
Mathlib).  An `@[ext]` lemma lets us go back.

```
UInt256  ──simp──▸  Fin UInt256.size  ──simp──▸  ℕ (mod 2^256)
         ◂──ext──                     ◂──Fin.ext──
```
-/

namespace Solady.Proofs.UInt256
open EvmYul

/-! ### Constants -/

def U256_MAX : UInt256 := UInt256.ofNat (2 ^ 256 - 1)
def WAD : UInt256 := UInt256.ofNat (10 ^ 18)

/-! ### Layer 1 – UInt256 ↔ Fin bridge -/

@[ext] theorem ext (a b : UInt256) (h : a.val = b.val) : a = b :=
  congrArg UInt256.mk h

theorem ext_toNat (a b : UInt256) (h : a.toNat = b.toNat) : a = b :=
  ext a b (Fin.ext h)

@[simp] theorem val_mk (v : Fin UInt256.size) : (UInt256.mk v).val = v := rfl
@[simp] theorem toNat_mk (v : Fin UInt256.size) : (UInt256.mk v).toNat = v.val := rfl

@[simp] theorem val_add (a b : UInt256) : (a + b).val = a.val + b.val := rfl
@[simp] theorem val_sub (a b : UInt256) : (a - b).val = a.val - b.val := rfl
@[simp] theorem val_mul (a b : UInt256) : (a * b).val = a.val * b.val := rfl
@[simp] theorem val_div (a b : UInt256) : (a / b).val = a.val / b.val := rfl

@[simp] theorem val_zero : (⟨0⟩ : UInt256).val = 0 := rfl

@[simp] theorem val_ofNat (n : Nat) :
    (UInt256.ofNat n).val = Fin.ofNat _ n := rfl

@[simp] theorem lt_iff (a b : UInt256) : a < b ↔ a.val < b.val := Iff.rfl
@[simp] theorem le_iff (a b : UInt256) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

/-! ### Layer 2 – UInt256 → ℕ shortcuts

These compose both layers so `simp` lands directly in `ℕ`. -/

@[simp] theorem toNat_add (a b : UInt256) :
    (a + b).toNat = (a.toNat + b.toNat) % UInt256.size :=
  Fin.val_add a.val b.val

@[simp] theorem toNat_mul (a b : UInt256) :
    (a * b).toNat = (a.toNat * b.toNat) % UInt256.size :=
  Fin.val_mul a.val b.val

@[simp] theorem toNat_div (a b : UInt256) :
    (a / b).toNat = a.toNat / b.toNat := rfl

@[simp] theorem toNat_ofNat (n : ℕ) :
    (UInt256.ofNat n).toNat = n % UInt256.size := by
  simp [UInt256.ofNat, UInt256.toNat, Id.run, Fin.ofNat]

@[simp] theorem toNat_lt (a : UInt256) : a.toNat < UInt256.size := a.val.isLt

@[simp] theorem gt_iff (a b : UInt256) : a > b ↔ a.toNat > b.toNat := Iff.rfl

@[simp] theorem zero_iff (a : UInt256) : a = ⟨0⟩ ↔ a.toNat = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact ext_toNat a ⟨0⟩ h

@[simp] theorem U256_MAX_toNat : U256_MAX.toNat = 2 ^ 256 - 1 := rfl
@[simp] theorem WAD_toNat : WAD.toNat = 10 ^ 18 := rfl

/-! ### Using `ring` on UInt256

`Fin n` has a scoped `CommRing` instance in Mathlib (`Fin.CommRing`).
To use `ring` on goals involving `.val : Fin UInt256.size`:

1. `simp` with the Layer-1 lemmas to reduce to `Fin`,
2. `open Fin.CommRing in ring` to close the goal.

```
example (a b : UInt256) : a + b = b + a := by
  ext; simp only [val_add]; open Fin.CommRing in ring
```

For `toNat` (ℕ) goals, `simp` + `Nat` lemmas + `omega` usually suffice.
-/

example (a b : UInt256) : a + b = b + a := by
  ext; simp only [val_add]; open Fin.CommRing in ring

example (a b : UInt256) : a * b = b * a := by
  ext; simp only [val_mul]; open Fin.CommRing in ring

end Solady.Proofs.UInt256
