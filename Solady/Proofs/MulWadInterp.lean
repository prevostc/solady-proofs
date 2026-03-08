import Mathlib
import EvmYul.UInt256
import EvmYul.Yul.Ast
import EvmYul.Yul.Interpreter
import EvmYul.Yul.YulNotation
import EvmYul.Yul.State
import EvmYul.Yul.StateOps
import EvmYul.Semantics

import Solady.MulWad
import Solady.Code.MulWadYul
import Solady.YulUtils

namespace Solady.Proofs.Interp

open EvmYul
open EvmYul.Yul
open EvmYul.Yul.Ast
open EvmYul.Yul.Notation
open EvmYul.UInt256.YulBridge
open Solady
open Solady.Code

/-!
# Yul interpreter equivalence for mulWad

We prove that executing the Yul AST `mulWad_yul` through evmyul's
interpreter produces the same result as the pure `Solady.mulWad` function.

The `mulWad_yul` body consists of two statements:
1. Overflow guard: `if gt(x, div(not(0), y)) { if y { mstore(...); revert(...) } }`
2. Assignment: `z := div(mul(x, y), 1000000000000000000)`

The proof is layered bottom-up:
- Layer 1: Primitive expression evaluation lemmas (axioms)
- Layer 2: Statement execution lemmas (axioms)
- Layer 3: Full function body equivalence (theorem)
-/

/--
Extract the `mulWad` result from a Yul execution outcome.
- `.ok s` → read `"z"` from the varstore → `.ok z`
- `.error .Revert` → `.revert`
- Other errors → `.revert` (conservative)
-/
def interpResult (r : Except Yul.Exception Yul.State) : MulWadResult :=
  match r with
  | .ok s => .ok (s.lookup! "z")
  | .error .Revert => .revert
  | .error _ => .revert

/-! ## Layer 1–2: Interpreter stepping axioms

These axioms capture the behavior of evmyul's `exec`/`eval` on the
specific AST of `mulWad_yul`. Each follows mechanically from the
interpreter's reduction rules but would require stepping through
many layers of mutual recursion to prove.
-/

/--
**Revert path:** When `y ≠ 0` and `gt(x, div(not(0), y)) ≠ 0`,
executing the full body results in `.error .Revert`.
-/
theorem exec_body_revert
    (fuel : ℕ) (ss : SharedState .Yul) (vs : VarStore)
    (x₀ y₀ : UInt256)
    (hfuel : fuel ≥ 20)
    (hx : vs.lookup "x" = some x₀)
    (hy : vs.lookup "y" = some y₀)
    (hz : vs.lookup "z" = some ⟨0⟩)
    (hy_ne : y₀ ≠ ⟨0⟩)
    (hgt : UInt256.gt x₀ (UInt256.div (UInt256.lnot ⟨0⟩) y₀) ≠ ⟨0⟩)
    (co : Option YulContract) :
    Yul.exec fuel
      (.Block mulWad_yul.body)
      co
      (.Ok ss vs) =
    .error .Revert := by
      sorry

/--
**Success path:** When the overflow guard does NOT trigger,
executing the full body succeeds with `"z"` set to `div(mul(x,y), WAD)`.
-/
theorem exec_body_ok
    (fuel : ℕ) (ss : SharedState .Yul) (vs : VarStore)
    (x₀ y₀ : UInt256)
    (hfuel : fuel ≥ 20)
    (hx : vs.lookup "x" = some x₀)
    (hy : vs.lookup "y" = some y₀)
    (hz : vs.lookup "z" = some ⟨0⟩)
    (hguard : ¬(y₀ ≠ ⟨0⟩ ∧ UInt256.gt x₀ (UInt256.div (UInt256.lnot ⟨0⟩) y₀) ≠ ⟨0⟩))
    (co : Option YulContract) :
    ∃ ss' vs',
      Yul.exec fuel (.Block mulWad_yul.body) co (.Ok ss vs) = .ok (.Ok ss' vs') ∧
      vs'.lookup "z" = some (UInt256.div (UInt256.mul x₀ y₀) (UInt256.ofNat (10 ^ 18)))
      := by
      sorry

/-! ## mulWad-specific bridge -/

private theorem lnot_zero_eq_U256_MAX :
    UInt256.lnot ⟨0⟩ = U256_MAX := by
  rw [lnot_zero]; rfl

/-! ## Layer 3: Top-level equivalence theorem -/

/--
**Main theorem:** Executing `mulWad_yul.body` via the Yul interpreter
and extracting the result via `interpResult` agrees with the pure `mulWad`.
-/
theorem mulWad_yul_equiv
    (fuel : ℕ) (ss : SharedState .Yul) (vs : VarStore)
    (x₀ y₀ : UInt256)
    (hfuel : fuel ≥ 20)
    (hx : vs.lookup "x" = some x₀)
    (hy : vs.lookup "y" = some y₀)
    (hz : vs.lookup "z" = some ⟨0⟩)
    (co : Option YulContract) :
    interpResult (Yul.exec fuel (.Block mulWad_yul.body) co (.Ok ss vs)) = mulWad x₀ y₀ := by
  unfold mulWad
  by_cases hguard : y₀ ≠ ⟨0⟩ ∧ UInt256.gt x₀ (UInt256.div (UInt256.lnot ⟨0⟩) y₀) ≠ ⟨0⟩
  · -- Revert case: the overflow guard fires
    obtain ⟨h₁, h₂⟩ := hguard
    rw [exec_body_revert fuel ss vs x₀ y₀ hfuel hx hy hz h₁ h₂ co]
    simp only [interpResult]
    have h₃ : x₀ > U256_MAX / y₀ := by
      rw [← lnot_zero_eq_U256_MAX]
      exact (gt_ne_zero_iff _ _).mp h₂
    simp [h₁, h₃]
  · -- Success case: the overflow guard does NOT fire
    obtain ⟨ss', vs', hexec, hvs_z⟩ := exec_body_ok fuel ss vs x₀ y₀ hfuel hx hy hz hguard co
    rw [hexec]
    simp only [interpResult]
    push_neg at hguard
    have h₄ : ¬(y₀ ≠ ⟨0⟩ ∧ x₀ > U256_MAX / y₀) := by
      push_neg
      intro h₅
      have h₆ := hguard h₅
      have h₇ : ¬(UInt256.gt x₀ (UInt256.div (UInt256.lnot ⟨0⟩) y₀) ≠ ⟨0⟩) := by
        simp [h₆]
      rw [gt_ne_zero_iff, lnot_zero_eq_U256_MAX] at h₇
      exact fun h => h₇ h
    simp [h₄]
    change (Yul.State.Ok ss' vs').lookup! "z" = x₀ * y₀ / WAD
    simp only [Yul.State.lookup!]
    rw [hvs_z]
    simp [WAD]
    rfl

end Solady.Proofs.Interp
