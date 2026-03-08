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

set_option maxHeartbeats 800000

namespace Solady.Proofs.InterpStep

open EvmYul
open EvmYul.Yul
open EvmYul.Yul.Ast
open EvmYul.Yul.Notation
open EvmYul.UInt256.YulBridge
open Solady
open Solady.Code

/-! # Interpreter stepping for mulWad -/

-- ═══════════════════════════════════════════════════════════════════
-- Layer 0 : helpers & primitive reductions
-- ═══════════════════════════════════════════════════════════════════

theorem lookup_bang_eq {ss : SharedState .Yul} {vs : VarStore}
    {id : Identifier} {v : UInt256}
    (h : vs.lookup id = some v) :
    Yul.State.lookup! id (Yul.State.Ok ss vs) = v := by
  simp only [Yul.State.lookup!, Option.get!]; rw [h]

-- step reductions
theorem step_not (s : Yul.State) (v : UInt256) :
    step (τ := .Yul) .NOT .none s [v] = Yul.execUnOp UInt256.lnot s [v] := by
  unfold step; simp [Id.run]; rfl
theorem step_gt (s : Yul.State) (a b : UInt256) :
    step (τ := .Yul) .GT .none s [a, b] = Yul.execBinOp UInt256.gt s [a, b] := by
  unfold step; simp [Id.run]; rfl
theorem step_div (s : Yul.State) (a b : UInt256) :
    step (τ := .Yul) .DIV .none s [a, b] = Yul.execBinOp UInt256.div s [a, b] := by
  unfold step; simp [Id.run]; rfl
theorem step_mul (s : Yul.State) (a b : UInt256) :
    step (τ := .Yul) .MUL .none s [a, b] = Yul.execBinOp UInt256.mul s [a, b] := by
  unfold step; simp [Id.run]; rfl
theorem step_revert (s : Yul.State) (a b : UInt256) :
    step (τ := .Yul) .REVERT .none s [a, b] = .error .Revert := by
  unfold step; simp [Id.run]; rfl
theorem step_mstore (s : Yul.State) (a b : UInt256) :
    step (τ := .Yul) .MSTORE .none s [a, b] =
    .ok (Yul.State.setMachineState (MachineState.mstore s.toMachineState a b) s, none) := by
  unfold step; simp [Id.run]; rfl


abbrev S (ss : SharedState .Yul) (vs : VarStore) : Yul.State := Yul.State.Ok ss vs


theorem primCall_gt (ss : SharedState .Yul) (vs : VarStore) (fuel : ℕ) (a b : UInt256) :
    Yul.primCall fuel (S ss vs) .GT [a, b] =
    .ok (Yul.State.Ok ss vs, [UInt256.gt a b]) := by
  unfold Yul.primCall; simp (config := { decide := false })
  rw [step_gt]; unfold Yul.execBinOp;
  sorry


-- primCall reductions
theorem primCall_not (n : ℕ) (ss : SharedState .Yul) (vs : VarStore) (v : UInt256) :
    Yul.primCall (n+1) (Yul.State.Ok ss vs) .NOT [v] =
    .ok (Yul.State.Ok ss vs, [UInt256.lnot v]) := by
  unfold Yul.primCall; simp (config := { decide := false })
  rw [step_not]; unfold Yul.execUnOp; rfl
-- theorem primCall_gt (n : ℕ) (ss : SharedState .Yul) (vs : VarStore) (a b : UInt256) :
--     Yul.primCall (n+1) (Yul.State.Ok ss vs) .GT [a, b] =
--     .ok (Yul.State.Ok ss vs, [UInt256.gt a b]) := by
--   unfold Yul.primCall; simp (config := { decide := false })
--   rw [step_gt]; unfold Yul.execBinOp; rfl
theorem primCall_div (n : ℕ) (ss : SharedState .Yul) (vs : VarStore) (a b : UInt256) :
    Yul.primCall (n+1) (Yul.State.Ok ss vs) .DIV [a, b] =
    .ok (Yul.State.Ok ss vs, [UInt256.div a b]) := by
  unfold Yul.primCall; simp (config := { decide := false })
  rw [step_div]; unfold Yul.execBinOp; rfl
theorem primCall_mul (n : ℕ) (ss : SharedState .Yul) (vs : VarStore) (a b : UInt256) :
    Yul.primCall (n+1) (Yul.State.Ok ss vs) .MUL [a, b] =
    .ok (Yul.State.Ok ss vs, [UInt256.mul a b]) := by
  unfold Yul.primCall; simp (config := { decide := false })
  rw [step_mul]; unfold Yul.execBinOp; rfl
theorem primCall_mstore (n : ℕ) (ss : SharedState .Yul) (vs : VarStore) (a b : UInt256) :
    Yul.primCall (n+1) (Yul.State.Ok ss vs) .MSTORE [a, b] =
    .ok (Yul.State.setMachineState
           (MachineState.mstore ss.toMachineState a b) (Yul.State.Ok ss vs), []) := by
  unfold Yul.primCall; simp (config := { decide := false })
  rw [step_mstore]; rfl
theorem primCall_revert (n : ℕ) (s : Yul.State) (a b : UInt256) :
    Yul.primCall (n+1) s .REVERT [a, b] = .error .Revert := by
  unfold Yul.primCall; simp (config := { decide := false }); rw [step_revert]

@[simp] theorem list_head_singleton (v : UInt256) : [v].head! = v := rfl

-- ═══════════════════════════════════════════════════════════════════
-- Layer 1 : eval sub-expression lemmas
-- ═══════════════════════════════════════════════════════════════════

-- eval (.Var id) — 1 fuel
theorem eval_var (fuel : ℕ) (ss : SharedState .Yul) (vs : VarStore)
    (id : Identifier) (v : UInt256) (hf : fuel ≥ 1)
    (hv : vs.lookup id = some v) (co : Option YulContract) :
    Yul.eval fuel (.Var id) co (Yul.State.Ok ss vs) =
    .ok (Yul.State.Ok ss vs, v) := by
  obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
  unfold Yul.eval; simp
  -- Goal: .ok (s, s[id]!) = .ok (s, v)
  congr
  unfold getElem! instGetElem?OfGetElemOfDecidable decidableGetElem? State.instGetElemIdentifierLiteralMemVarStoreStore
  simp
  -- We want to show that (Yul.State.Ok ss vs)[id]! = v because vs.lookup id = some v
  -- and State.lookup! just gets from vs. So this works by definition.
  -- Also, .ok means Except.ok, which is what eval returns for this case.
  -- So this line shows the equality holds as required.
  -- For reference: (Yul.State.Ok ss vs)[id]! = v follows from hv.
  rw [lookup_bang_eq hv]
  sorry

  -- unfold getElem! instGetElem?OfGetElemOfDecidable
  -- simp only []
  -- split
  -- · rename_i val h₁
  --   unfold decidableGetElem? at h₁
  --   split at h₁
  --   · rename_i h₂ h₃
  --     exact absurd h₃ (by
  --       intro h₄
  --       exact absurd h₄
  --     )
  --   · rename_i h₂
  --     exact absurd (Finmap.mem_of_lookup_eq_some hv) h₂
  -- · rename_i h₁
  --   unfold decidableGetElem? at h₁
  --   split at h₁
  --   · simp at h₁
  --   · rename_i h₂
  --     exact absurd (Finmap.mem_of_lookup_eq_some hv) h₂

-- eval (.Lit v) — 1 fuel
theorem eval_lit (fuel : ℕ) (ss : SharedState .Yul) (vs : VarStore)
    (v : UInt256) (hf : fuel ≥ 1) (co : Option YulContract) :
    Yul.eval fuel (.Lit v) co (Yul.State.Ok ss vs) =
    .ok (Yul.State.Ok ss vs, v) := by
  obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
  unfold Yul.eval; simp only []

end Solady.Proofs.InterpStep
