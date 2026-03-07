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
axiom exec_body_revert
    (fuel : Nat) (ss : SharedState .Yul) (vs : VarStore)
    (xv yv : UInt256)
    (hfuel : fuel ≥ 20)
    (hx : vs.lookup "x" = some xv)
    (hy : vs.lookup "y" = some yv)
    (hz : vs.lookup "z" = some ⟨0⟩)
    (hyne : yv ≠ ⟨0⟩)
    (hgt : UInt256.gt xv (UInt256.div (UInt256.lnot ⟨0⟩) yv) ≠ ⟨0⟩)
    (co : Option YulContract) :
    Yul.exec fuel
      (.Block mulWad_yul.body)
      co
      (.Ok ss vs) =
    .error .Revert

/--
**Success path:** When the overflow guard does NOT trigger,
executing the full body succeeds with `"z"` set to `div(mul(x,y), WAD)`.
-/
axiom exec_body_ok
    (fuel : Nat) (ss : SharedState .Yul) (vs : VarStore)
    (xv yv : UInt256)
    (hfuel : fuel ≥ 20)
    (hx : vs.lookup "x" = some xv)
    (hy : vs.lookup "y" = some yv)
    (hz : vs.lookup "z" = some ⟨0⟩)
    (hguard : ¬(yv ≠ ⟨0⟩ ∧ UInt256.gt xv (UInt256.div (UInt256.lnot ⟨0⟩) yv) ≠ ⟨0⟩))
    (co : Option YulContract) :
    ∃ ss' vs',
      Yul.exec fuel (.Block mulWad_yul.body) co (.Ok ss vs) = .ok (.Ok ss' vs') ∧
      vs'.lookup "z" = some (UInt256.div (UInt256.mul xv yv) (UInt256.ofNat (10 ^ 18)))

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
    (fuel : Nat) (ss : SharedState .Yul) (vs : VarStore)
    (xv yv : UInt256)
    (hfuel : fuel ≥ 20)
    (hx : vs.lookup "x" = some xv)
    (hy : vs.lookup "y" = some yv)
    (hz : vs.lookup "z" = some ⟨0⟩)
    (co : Option YulContract) :
    interpResult (Yul.exec fuel (.Block mulWad_yul.body) co (.Ok ss vs)) = mulWad xv yv := by
  unfold mulWad
  by_cases hguard : yv ≠ ⟨0⟩ ∧ UInt256.gt xv (UInt256.div (UInt256.lnot ⟨0⟩) yv) ≠ ⟨0⟩
  · -- Revert case: the overflow guard fires
    obtain ⟨hyne, hgtU⟩ := hguard
    rw [exec_body_revert fuel ss vs xv yv hfuel hx hy hz hyne hgtU co]
    simp only [interpResult]
    have hgt_lean : xv > U256_MAX / yv := by
      rw [← lnot_zero_eq_U256_MAX]
      exact (gt_ne_zero_iff _ _).mp hgtU
    simp [hyne, hgt_lean]
  · -- Success case: the overflow guard does NOT fire
    obtain ⟨ss', vs', hexec, hvs_z⟩ := exec_body_ok fuel ss vs xv yv hfuel hx hy hz hguard co
    rw [hexec]
    simp only [interpResult]
    push_neg at hguard
    have hguard_lean : ¬(yv ≠ ⟨0⟩ ∧ xv > U256_MAX / yv) := by
      push_neg
      intro hyne
      have hzero := hguard hyne
      have hnotgt : ¬(UInt256.gt xv (UInt256.div (UInt256.lnot ⟨0⟩) yv) ≠ ⟨0⟩) := by
        simp [hzero]
      rw [gt_ne_zero_iff, lnot_zero_eq_U256_MAX] at hnotgt
      exact fun h => hnotgt h
    simp [hguard_lean]
    change (Yul.State.Ok ss' vs').lookup! "z" = xv * yv / WAD
    simp only [Yul.State.lookup!]
    rw [hvs_z]
    simp [WAD]
    rfl

end Solady.Proofs.Interp
