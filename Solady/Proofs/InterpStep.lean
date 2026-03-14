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
import Solady.Proofs.YulBase

/-!
# Interpreter stepping for mulWad

This file now simply re-exports `YulBase` lemmas and provides
compatibility wrappers where needed.

Most lemmas have been moved to `Solady.Proofs.YulBase`.
-/

namespace Solady.Proofs.InterpStep

open EvmYul
open EvmYul.Yul
open EvmYul.Yul.Ast
open EvmYul.Yul.Notation
open EvmYul.UInt256.YulBridge
open Solady
open Solady.Code
open Solady.Proofs.YulBase

abbrev S (ss : SharedState .Yul) (vs : VarStore) : Yul.State := Yul.State.Ok ss vs

-- Re-export YulBase lemmas
abbrev lookup_bang_eq := YulBase.lookup_bang_eq
abbrev step_not := YulBase.step_not
abbrev step_gt := YulBase.step_gt
abbrev step_div := YulBase.step_div
abbrev step_mul := YulBase.step_mul
abbrev step_revert := YulBase.step_revert
abbrev step_mstore := YulBase.step_mstore

-- Compatibility wrappers for primCall lemmas (specialized to Ok states)
theorem primCall_not (n : ℕ) (ss : SharedState .Yul) (vs : VarStore) (v : UInt256) :
    Yul.primCall (n+1) (Yul.State.Ok ss vs) .NOT [v] =
    .ok (Yul.State.Ok ss vs, [UInt256.lnot v]) := by
  exact YulBase.primCall_not n (Yul.State.Ok ss vs) v

theorem primCall_gt (n : ℕ) (ss : SharedState .Yul) (vs : VarStore) (a b : UInt256) :
    Yul.primCall (n+1) (Yul.State.Ok ss vs) .GT [a, b] =
    .ok (Yul.State.Ok ss vs, [UInt256.gt a b]) := by
  exact YulBase.primCall_gt n (Yul.State.Ok ss vs) a b

theorem primCall_div (n : ℕ) (ss : SharedState .Yul) (vs : VarStore) (a b : UInt256) :
    Yul.primCall (n+1) (Yul.State.Ok ss vs) .DIV [a, b] =
    .ok (Yul.State.Ok ss vs, [UInt256.div a b]) := by
  exact YulBase.primCall_div n (Yul.State.Ok ss vs) a b

theorem primCall_mul (n : ℕ) (ss : SharedState .Yul) (vs : VarStore) (a b : UInt256) :
    Yul.primCall (n+1) (Yul.State.Ok ss vs) .MUL [a, b] =
    .ok (Yul.State.Ok ss vs, [UInt256.mul a b]) := by
  exact YulBase.primCall_mul n (Yul.State.Ok ss vs) a b

theorem primCall_mstore (n : ℕ) (ss : SharedState .Yul) (vs : VarStore) (a b : UInt256) :
    Yul.primCall (n+1) (Yul.State.Ok ss vs) .MSTORE [a, b] =
    .ok (Yul.State.setMachineState
           (MachineState.mstore ss.toMachineState a b) (Yul.State.Ok ss vs), []) := by
  exact YulBase.primCall_mstore n ss vs a b

theorem primCall_revert (n : ℕ) (s : Yul.State) (a b : UInt256) :
    Yul.primCall (n+1) s .REVERT [a, b] = .error .Revert := by
  exact YulBase.primCall_revert n s a b

@[simp] theorem list_head_singleton (v : UInt256) : [v].head! = v := rfl

-- Compatibility wrapper for eval_var (adds hf parameter, converts fuel format)
theorem eval_var (fuel : ℕ) (ss : SharedState .Yul) (vs : VarStore)
    (id : Identifier) (v : UInt256) (hf : fuel ≥ 1)
    (hv : vs.lookup id = some v) (co : Option YulContract) :
    Yul.eval fuel (.Var id) co (Yul.State.Ok ss vs) =
    .ok (Yul.State.Ok ss vs, v) := by
  obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
  exact YulBase.eval_var m ss vs id v co hv

-- Compatibility wrapper for eval_lit
theorem eval_lit (fuel : ℕ) (ss : SharedState .Yul) (vs : VarStore)
    (v : UInt256) (hf : fuel ≥ 1) (co : Option YulContract) :
    Yul.eval fuel (.Lit v) co (Yul.State.Ok ss vs) =
    .ok (Yul.State.Ok ss vs, v) := by
  obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
  exact YulBase.eval_lit m (Yul.State.Ok ss vs) v co

end Solady.Proofs.InterpStep
