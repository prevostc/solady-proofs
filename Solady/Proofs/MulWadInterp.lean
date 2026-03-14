import Mathlib
import EvmYul.UInt256
import EvmYul.Yul.Ast
import EvmYul.Yul.Interpreter
import EvmYul.Yul.YulNotation
import EvmYul.Yul.State
import EvmYul.Yul.StateOps
import EvmYul.Semantics

import Solady.Specs.MulWad
import Solady.Code.MulWadYul
import Solady.YulUtils
import Solady.Proofs.UInt256
import Solady.Proofs.YulBase

namespace Solady.Proofs.Interp


open EvmYul
open EvmYul.Yul
open EvmYul.Yul.Ast
open EvmYul.Yul.Notation
-- open EvmYul.Yul.Semantics
open EvmYul.UInt256.YulBridge
open Solady
open Solady.Code
open Solady.Proofs.UInt256
open Solady.Proofs.YulBase

-- re-define private defs we rely on
private abbrev Transformer : EvmYul.OperationType → Type
  | .EVM => EVM.Transformer
  | .Yul => Yul.Transformer
private def dispatchBinaryMachineStateOp
 (τ : EvmYul.OperationType) (op : EvmYul.MachineState → UInt256 → UInt256 → EvmYul.MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryMachineStateOp op
    | .Yul => Yul.binaryMachineStateOp op


def interpret_mulWad_result (r : Except Yul.Exception Yul.State) : Option ℕ :=
  match r with
  | .ok s => some (s.lookup! "z").toNat
  | .error .Revert => .none
  | .error _ => none

def mulWad_implem_is_correct : Prop :=
  ∀ x y fuel: ℕ,
  ∀ vs : VarStore,
  ∀ ss : SharedState .Yul,
  ∀ co : Option YulContract,
    x < U256_MAX →
    y < U256_MAX →
    fuel ≥ 20 →
    vs.lookup "x" = some (UInt256.ofNat x) →
    vs.lookup "y" = some (UInt256.ofNat y) →
    interpret_mulWad_result (Yul.exec fuel (.Block mulWad_yul.body) co (.Ok ss vs)) = mulWad x y


theorem mulWad_implem_is_correct_proof : mulWad_implem_is_correct := by
  intros x y fuel vs ss co hx hy hfuel hx_vs hy_vs
  have pf : fuel ≠ 0 := by omega
  obtain ⟨fuel₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pf
  unfold interpret_mulWad_result
  unfold Yul.exec -- exec one instruction
  unfold mulWad_yul
  unfold FunctionDefinition.body
  simp
  unfold Yul.exec
  have pf₁ : fuel₁ ≠ 0 := by omega
  obtain ⟨fuel₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pf₁
  simp
  unfold Yul.eval
  have pf₂ : fuel₂ ≠ 0 := by omega
  obtain ⟨fuel₃, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pf₂
  simp
  unfold Yul.evalPrimCall
  unfold reverse'
  unfold Yul.evalArgs
  have pf₃ : fuel₃ ≠ 0 := by omega
  obtain ⟨fuel₄, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pf₃
  simp
  unfold Yul.evalTail
  unfold Yul.eval
  have pf₄ : fuel₄ ≠ 0 := by omega
  obtain ⟨fuel₅, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pf₄
  simp
  unfold Yul.evalPrimCall
  unfold reverse'
  unfold Yul.evalArgs
  have pf₅ : fuel₅ ≠ 0 := by omega
  obtain ⟨fuel₆, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pf₅
  simp
  unfold Yul.evalTail
  unfold Yul.eval
  have pf₆ : fuel₆ ≠ 0 := by omega
  obtain ⟨fuel₇, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pf₆
  simp
  unfold cons'
  unfold Yul.evalArgs
  have pf₇ : fuel₇ ≠ 0 := by omega
  obtain ⟨fuel₈, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pf₇
  simp
  unfold Yul.evalTail
  unfold Yul.eval
  have pf₈ : fuel₈ ≠ 0 := by omega
  obtain ⟨fuel₉, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pf₈
  simp
  unfold Yul.evalPrimCall
  unfold reverse'
  unfold Yul.evalArgs
  have pf₉ : fuel₉ ≠ 0 := by omega
  obtain ⟨fuel₁₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pf₉
  simp
  unfold Yul.evalTail
  unfold Yul.eval
  have pf₁₀ : fuel₁₀ ≠ 0 := by omega
  obtain ⟨fuel₁₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pf₁₀
  simp
  unfold cons'
  unfold Yul.evalArgs
  have pf₁₁ : fuel₁₁ ≠ 0 := by omega
  obtain ⟨fuel₁₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero pf₁₁
  simp
  unfold head'
  simp
  unfold Yul.exec
  simp
  unfold Yul.exec
  simp
  unfold Yul.exec
  unfold Yul.eval
  unfold Yul.evalPrimCall
  unfold Yul.reverse'
  unfold Yul.head'
  unfold Yul.evalArgs
  simp
  unfold Yul.exec
  unfold Yul.exec
  simp
  unfold Yul.execPrimCall
  unfold Yul.reverse'
  unfold Yul.evalArgs
  unfold Yul.evalTail
  unfold Yul.cons'
  unfold Yul.eval
  unfold Yul.evalPrimCall
  unfold Yul.evalArgs
  unfold Yul.evalTail
  unfold Yul.cons'
  unfold Yul.evalArgs
  unfold Yul.multifill'
  unfold Yul.primCall
  unfold Yul.eval
  unfold Yul.evalPrimCall
  unfold Yul.reverse'
  unfold Yul.evalArgs
  unfold Yul.evalTail
  unfold Yul.eval
  unfold Yul.cons'
  unfold Yul.evalArgs
  unfold Yul.evalTail
  unfold Yul.eval
  unfold Yul.cons'
  unfold Yul.evalArgs
  unfold Yul.head'
  unfold step
  unfold Id.run
  simp
  unfold dispatchBinaryMachineStateOp






  --unfold Yul.exec







-- theorem mulWad_implem_is_correct_proof : mulWad_implem_is_correct := by
--   intros x y fuel vs ss co hx hy hfuel hx_vs hy_vs
--   unfold interpret_mulWad_result
--   unfold Yul.exec -- exec one instruction
--   unfold mulWad_yul
--   unfold FunctionDefinition.body
--   simp
--   repeat (
--     unfold Yul.exec
--     unfold Yul.eval
--     unfold Yul.evalPrimCall
--     unfold Yul.reverse'
--     unfold Yul.head'
--     unfold Yul.evalArgs
--     unfold Yul.evalTail
--     unfold Yul.cons'
--     unfold Yul.multifill'
--     unfold Yul.primCall
--     unfold Yul.step
--   )
--   simp



-- /--
-- **Main theorem:** Executing `mulWad_yul.body` via the Yul interpreter
-- and extracting the result via `interpResult` agrees with the pure `mulWad`.
-- -/
-- theorem mulWad_yul_equiv
--     (x y fuel: ℕ)
--     (vs : VarStore)
--     -- fuel is sufficient to execute the body
--     (hfuel : fuel ≥ 20)
--     -- variables are passed through the varstore
--     (hx : vs.lookup "x" = some x₀)
--     (hy : vs.lookup "y" = some y₀)
--     (hz : vs.lookup "z" = some ⟨0⟩) :
--     -- executing the yul body matches the pure mulWad function
--     interpResult (Yul.exec fuel (.Block mulWad_yul.body) .none (.Ok (SharedState .Yul) vs)) = mulWad x y := by
--   --unfold interpResult
--   --simp only [Yul.exec, mulWad_yul, mulWad, hx, hy, hz]

--   -- overflow guard case
--   by_cases hguard : y₀ ≠ ⟨0⟩ ∧ x₀ > U256_MAX / y₀
--   · have pos_fuel : fuel ≥ 1 := by exact Nat.le_trans (by norm_num) hfuel
--     have spec_revert : mulWad x₀ y₀ = .revert := by
--       unfold mulWad
--       rw [if_pos hguard]
--     let computation := Yul.exec fuel (.Block mulWad_yul.body) .none (.Ok ss vs)
--     have exec_reverts : interpResult computation = .revert := by
--       unfold interpResult
--       -- prove computation always reverts under hguard
--       have computation_reverts : computation = .error .Revert := by



--     -- Now, putting together:
--     rw [exec_body, mulWad_guarded]
--   · -- guard false: y₀ = ⟨0⟩ ∨ ¬(x₀ > U256_MAX / y₀); then mulWad computes normally
--     sorry

end Solady.Proofs.Interp
