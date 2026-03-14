import Mathlib
import EvmYul.UInt256
import EvmYul.Yul.Ast
import EvmYul.Yul.Interpreter
import EvmYul.Yul.YulNotation
import EvmYul.Yul.State
import EvmYul.Yul.StateOps
import EvmYul.Semantics

/-!
# Yul Interpreter Base Theorem Library
-/

namespace Solady.Proofs.YulBase

open EvmYul
open EvmYul.Yul
open EvmYul.Yul.Ast
open EvmYul.Yul.Notation

/-! ## Tier A: primCall reduction lemmas -/

/-- Reduces `step .NOT` to `execUnOp UInt256.lnot` (bitwise NOT). -/
theorem step_not (s : Yul.State) (v : UInt256) :
    step (τ := .Yul) .NOT .none s [v] = Yul.execUnOp UInt256.lnot s [v] := by
  unfold step; simp [Id.run]; rfl

/-- Reduces `step .GT` to `execBinOp UInt256.gt` (greater-than comparison). -/
theorem step_gt (s : Yul.State) (a b : UInt256) :
    step (τ := .Yul) .GT .none s [a, b] = Yul.execBinOp UInt256.gt s [a, b] := by
  unfold step; simp [Id.run]; rfl

/-- Reduces `step .DIV` to `execBinOp UInt256.div` (unsigned division). -/
theorem step_div (s : Yul.State) (a b : UInt256) :
    step (τ := .Yul) .DIV .none s [a, b] = Yul.execBinOp UInt256.div s [a, b] := by
  unfold step; simp [Id.run]; rfl

/-- Reduces `step .MUL` to `execBinOp UInt256.mul` (multiplication mod 2^256). -/
theorem step_mul (s : Yul.State) (a b : UInt256) :
    step (τ := .Yul) .MUL .none s [a, b] = Yul.execBinOp UInt256.mul s [a, b] := by
  unfold step; simp [Id.run]; rfl

/-- Reduces `step .REVERT` to `.error .Revert` (halts execution with revert). -/
theorem step_revert (s : Yul.State) (a b : UInt256) :
    step (τ := .Yul) .REVERT .none s [a, b] = .error .Revert := by
  unfold step; simp [Id.run]; rfl

/-- Reduces `step .MSTORE` to updating machine memory at the given offset. -/
theorem step_mstore (s : Yul.State) (a b : UInt256) :
    step (τ := .Yul) .MSTORE .none s [a, b] =
    .ok (Yul.State.setMachineState (MachineState.mstore s.toMachineState a b) s, none) := by
  unfold step; simp [Id.run]; rfl

/-- `primCall` for NOT: returns bitwise NOT of the argument, state unchanged. -/
@[simp] theorem primCall_not (fuel : ℕ) (s : Yul.State) (v : UInt256) :
    Yul.primCall (fuel + 1) s .NOT [v] = .ok (s, [UInt256.lnot v]) := by
  unfold Yul.primCall; simp (config := { decide := false })
  rw [step_not]; unfold Yul.execUnOp; rfl

/-- `primCall` for MUL: returns product of two arguments, state unchanged. -/
@[simp] theorem primCall_mul (fuel : ℕ) (s : Yul.State) (a b : UInt256) :
    Yul.primCall (fuel + 1) s .MUL [a, b] = .ok (s, [a * b]) := by
  unfold Yul.primCall; simp (config := { decide := false })
  rw [step_mul]; unfold Yul.execBinOp; rfl

/-- `primCall` for DIV: returns unsigned quotient of two arguments, state unchanged. -/
@[simp] theorem primCall_div (fuel : ℕ) (s : Yul.State) (a b : UInt256) :
    Yul.primCall (fuel + 1) s .DIV [a, b] = .ok (s, [UInt256.div a b]) := by
  unfold Yul.primCall; simp (config := { decide := false })
  rw [step_div]; unfold Yul.execBinOp; rfl

/-- `primCall` for GT: returns 1 if a > b else 0 (UInt256), state unchanged. -/
@[simp] theorem primCall_gt (fuel : ℕ) (s : Yul.State) (a b : UInt256) :
    Yul.primCall (fuel + 1) s .GT [a, b] = .ok (s, [UInt256.gt a b]) := by
  unfold Yul.primCall; simp (config := { decide := false })
  rw [step_gt]; unfold Yul.execBinOp; rfl

/-- `primCall` for MSTORE: writes word at offset `a` in memory; returns empty list. -/
theorem primCall_mstore (fuel : ℕ) (ss : SharedState .Yul) (vs : VarStore) (a b : UInt256) :
    Yul.primCall (fuel + 1) (.Ok ss vs) .MSTORE [a, b] =
    .ok (Yul.State.setMachineState
           (MachineState.mstore ss.toMachineState a b) (.Ok ss vs), []) := by
  unfold Yul.primCall; simp (config := { decide := false })
  rw [step_mstore]; rfl

/-- `primCall` for REVERT: always yields `.error .Revert`. -/
theorem primCall_revert (fuel : ℕ) (s : Yul.State) (a b : UInt256) :
    Yul.primCall (fuel + 1) s .REVERT [a, b] = .error .Revert := by
  unfold Yul.primCall; simp (config := { decide := false })
  rw [step_revert]

/-! ## Tier B: eval reduction lemmas -/

/-- Evaluating a literal `.Lit v` returns the value and leaves state unchanged. -/
@[simp] theorem eval_lit (fuel : Nat) (s : State) (v : UInt256) (co) :
    Yul.eval (fuel+1) (.Lit v) co s = .ok (s, v) := by
  unfold Yul.eval; rfl

/-- Connects `Yul.State.lookup!` to `Finmap.lookup` when the identifier is in the store. -/
theorem lookup_bang_eq (ss : SharedState .Yul) (vs : VarStore)
    (id : Identifier) (v : UInt256) (h : vs.lookup id = some v) :
    Yul.State.lookup! id (Yul.State.Ok ss vs) = v := by
  simp only [Yul.State.lookup!, Option.get!]; rw [h]

/-- Evaluating a variable `.Var id` in an `.Ok` state returns its value from the varstore. -/
@[simp] theorem eval_var (fuel : ℕ) (ss : SharedState .Yul) (vs : VarStore)
    (id : Identifier) (v : UInt256) (co : Option YulContract)
    (hv : vs.lookup id = some v) :
    Yul.eval (fuel + 1) (.Var id) co (.Ok ss vs) = .ok (.Ok ss vs, v) := by
  unfold Yul.eval
  unfold getElem! instGetElem?OfGetElemOfDecidable decidableGetElem?
    State.instGetElemIdentifierLiteralMemVarStoreStore
  simp only [Yul.State.store]
  have hmem : id ∈ vs := Finmap.mem_of_lookup_eq_some hv
  simp only [hmem, dite_true]
  rw [lookup_bang_eq ss vs id v hv]

/-! ## Tier C: exec reduction lemmas -/

/-- Executing an empty block `.Block []` leaves state unchanged. -/
@[simp] theorem exec_block_nil (fuel : Nat) (s : State) (co) :
    Yul.exec (fuel+1) (.Block []) co s = .ok s := by
  unfold Yul.exec; rfl

/-- Block with head: run first stmt, then the rest on the resulting state. -/
theorem exec_block_cons (fuel : Nat) (stmt : Stmt) (stmts : List Stmt) (s : State) (co) :
    Yul.exec (fuel+1) (.Block (stmt :: stmts)) co s =
    match Yul.exec fuel stmt co s with
    | .error e => .error e
    | .ok s₁ => Yul.exec fuel (.Block stmts) co s₁ := by
  simp only [Yul.exec]; rfl

/-- Executing `.If cond body`: evaluate condition; if non-zero, run body, else skip. -/
theorem exec_if (fuel : Nat) (cond : Expr) (body : List Stmt) (s : State) (co) :
    Yul.exec (fuel+1) (.If cond body) co s =
    match Yul.eval fuel cond co s with
    | .error e => .error e
    | .ok (s', c) => if c ≠ ⟨0⟩ then Yul.exec fuel (.Block body) co s' else .ok s' := by
  simp only [Yul.exec]; rfl

/-- Executing `.Let [var] (.some (.Lit v))` inserts the variable with value `v` into the state. -/
theorem exec_let_lit (fuel : Nat) (var : Identifier) (v : UInt256) (s : State) (co) :
    Yul.exec (fuel+1) (.Let [var] (.some (.Lit v))) co s =
    .ok (s.insert var v) := by
  simp only [Yul.exec, Yul.State.insert, List.head!]

/-! ## Tier D: evalArgs equation lemmas

These give clean equations for `evalArgs` that avoid the
messy match expression from mutual recursion unfolding.
-/

/-- Evaluating no arguments returns the state and the empty list. -/
theorem evalArgs_succ_nil (n : ℕ) (co : Option YulContract) (s : State) :
    Yul.evalArgs (n + 1) ([] : List Expr) co s = .ok (s, []) := by
  unfold Yul.evalArgs; rfl

/-- Evaluating (e :: es) is evalTail applied to the result of evaluating e. -/
theorem evalArgs_succ_cons (n : ℕ) (co : Option YulContract) (s : State)
    (e : Expr) (es : List Expr) :
    Yul.evalArgs (n + 1) (e :: es) co s =
    Yul.evalTail n es co (Yul.eval n e co s) := by
  unfold Yul.evalArgs; rfl

/-- When the first arg evaluated to `.ok (s, v)`, evalTail (n+1) cons's v onto evalArgs n rest. -/
theorem evalTail_succ (n : ℕ) (co : Option YulContract) (s : State)
    (v : UInt256) (es : List Expr) :
    Yul.evalTail (n + 1) es co (.ok (s, v)) =
    Yul.cons' v (Yul.evalArgs n es co s) := by
  unfold Yul.evalTail; rfl

/-- evalTail with zero fuel yields OutOfFuel. -/
theorem evalTail_zero (co : Option YulContract) (s : State)
    (v : UInt256) (es : List Expr) :
    Yul.evalTail 0 es co (.ok (s, v)) = .error .OutOfFuel := by
  unfold Yul.evalTail; rfl

/-- cons' prepends a value to an ok (state, list) result. -/
theorem cons'_ok (v : UInt256) (s : State) (vs : List UInt256) :
    Yul.cons' v (.ok (s, vs)) = .ok (s, v :: vs) := by
  unfold Yul.cons'; rfl

/-- reverse' reverses the list in an ok (state, list) result. -/
theorem reverse'_ok (s : State) (vs : List UInt256) :
    Yul.reverse' (.ok (s, vs)) = .ok (s, vs.reverse) := by
  unfold Yul.reverse'; rfl

/-- head' takes the first element of the list in an ok (state, v::vs) result. -/
theorem head'_ok (s : State) (v : UInt256) (vs : List UInt256) :
    Yul.head' (.ok (s, v :: vs)) = .ok (s, v) := by
  unfold Yul.head'; simp [List.head!]

/-- evalPrimCall on an ok (s, args) is head' of primCall s prim args. -/
theorem evalPrimCall_ok (n : ℕ) (prim : Operation .Yul) (s : State) (args : List UInt256) :
    Yul.evalPrimCall n prim (.ok (s, args)) =
    Yul.head' (Yul.primCall n s prim args) := by
  unfold Yul.evalPrimCall; rfl

/-- execPrimCall on an ok (s, args) is multifill' vars (primCall s prim args). -/
theorem execPrimCall_ok (n : ℕ) (prim : Operation .Yul) (vars : List Identifier)
  (s : State) (args : List UInt256) :
    Yul.execPrimCall n prim vars (.ok (s, args)) =
    Yul.multifill' vars (Yul.primCall n s prim args) := by
  unfold Yul.execPrimCall; rfl

/-- multifill' with no variables maps ok (s, vs) to ok (s.multifill [] vs). -/
theorem multifill'_ok_nil (s : State) (vs : List UInt256) :
    Yul.multifill' [] (.ok (s, vs)) = .ok (s.multifill [] vs) := by
  unfold Yul.multifill'; rfl

/-- multifill' with one variable maps ok (s, [v]) to ok (s.multifill [var] [v]). -/
theorem multifill'_ok_singleton (var : Identifier) (s : State) (v : UInt256) :
    Yul.multifill' [var] (.ok (s, [v])) = .ok (s.multifill [var] [v]) := by
  unfold Yul.multifill'; rfl

/-- multifill with empty variable list leaves state unchanged. -/
theorem multifill_nil (s : State) (vs : List UInt256) :
    s.multifill [] vs = s := by
  unfold Yul.State.multifill
  cases s <;> simp [List.zip]

/-- For Ok state, multifill [var] [v] equals insert var v. -/
theorem multifill_singleton_ok (ss : SharedState .Yul) (vs : VarStore)
    (var : Identifier) (v : UInt256) :
    (Yul.State.Ok ss vs).multifill [var] [v] = (Yul.State.Ok ss vs).insert var v := by
  unfold Yul.State.multifill
  simp [List.zip, List.foldr, Yul.State.insert]

/-! ## Tier E: compound eval/exec via equation lemmas

Now we can chain the equation lemmas to build compound reductions.
-/

-- /-- Evaluating a unary primcall `Call prim [e]` at fuel n+2: subexpr e at fuel n, then primCall.
--     Requires n ≥ 1 so that evalTail has enough fuel. -/
-- theorem eval_unary_call (n : ℕ) (hn : n ≥ 1) (prim : Operation .Yul) (e : Expr)
--     (s s' : State) (v r : UInt256) (co)
--     (heval : Yul.eval n e co s = .ok (s', v))
--     (hprim : Yul.primCall (n + 1) s' prim [v] = .ok (s', [r])) :
--     Yul.eval (n + 2) (.Call (Sum.inl prim) [e]) co s = .ok (s', r) := by
--   obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
--   unfold Yul.eval
--   simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
--   rw [evalArgs_succ_cons, heval, evalTail_succ]
--   rw [cons'_ok]
--   rw [evalArgs_succ_cons, heval, evalTail_succ, cons'_ok, evalArgs_succ_nil,
--       reverse'_ok, evalPrimCall_ok]
--   simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
--   rw [hprim]; exact head'_ok s' r []

-- /-- Evaluating a binary primcall `Call prim [e₁, e₂]` at fuel n+2.
--     Internally e₂ is evaluated at fuel n and e₁ at fuel n-1; we require both results.
--     Requires n ≥ 2 so both subexpressions have enough fuel. -/
-- theorem eval_binary_call (n : ℕ) (hn : n ≥ 2) (prim : Operation .Yul) (e₁ e₂ : Expr)
--     (s : State) (v₁ v₂ r : UInt256) (co)
--     (heval₂ : Yul.eval n e₂ co s = .ok (s, v₂))
--     (heval₁ : Yul.eval (n - 1) e₁ co s = .ok (s, v₁))
--     (hprim : Yul.primCall (n + 1) s prim [v₁, v₂] = .ok (s, [r])) :
--     Yul.eval (n + 2) (.Call (Sum.inl prim) [e₁, e₂]) co s = .ok (s, r) := by
--   obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
--   simp at heval₁
--   unfold Yul.eval
--   simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
--   rw [evalArgs_succ_cons, heval₂, evalTail_succ, cons'_ok,
--       evalArgs_succ_cons, heval₁, evalTail_succ, cons'_ok, evalArgs_succ_nil,
--       reverse'_ok, evalPrimCall_ok]
--   simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
--   rw [hprim]; exact head'_ok s r []

-- /-! ## Tier F: exec for ExprStmtCall and Let-with-Call -/

-- /-- Executing `revert(v₁, v₂)` as a statement (ExprStmtCall) yields `.error .Revert`. -/
-- theorem exec_revert_lits (n : ℕ) (s : State) (v₁ v₂ : UInt256) (co) :
--     Yul.exec (n + 5) (.ExprStmtCall (.Call (Sum.inl .REVERT) [Expr.Lit v₁, Expr.Lit v₂])) co s =
--     .error .Revert := by
--   unfold Yul.exec
--   simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
--   rw [evalArgs_succ_cons, eval_lit, evalTail_succ, cons'_ok,
--       evalArgs_succ_cons, eval_lit, evalTail_succ, cons'_ok, evalArgs_succ_nil,
--       reverse'_ok, execPrimCall_ok]
--   simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
--   rw [primCall_revert]
--   unfold Yul.multifill'; rfl

-- /-- Executing `mstore(v₁, v₂)` on an Ok state updates machine memory and returns the updated state. -/
-- theorem exec_mstore_lits (n : ℕ) (ss : SharedState .Yul) (vs : VarStore)
--     (v₁ v₂ : UInt256) (co) :
--     Yul.exec (n + 5) (.ExprStmtCall (.Call (Sum.inl .MSTORE) [Expr.Lit v₁, Expr.Lit v₂])) co (.Ok ss vs) =
--     .ok (Yul.State.setMachineState (MachineState.mstore ss.toMachineState v₁ v₂) (.Ok ss vs)) := by
--   unfold Yul.exec
--   simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
--   rw [evalArgs_succ_cons, eval_lit, evalTail_succ, cons'_ok,
--       evalArgs_succ_cons, eval_lit, evalTail_succ, cons'_ok, evalArgs_succ_nil,
--       reverse'_ok, execPrimCall_ok]
--   simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
--   rw [primCall_mstore]
--   rw [multifill'_ok_nil, multifill_nil]

-- /-- Executing `var := prim(e₁, e₂)` (Let with binary primcall): evaluates e₁, e₂, runs primCall,
--     then inserts var with the result. Requires n ≥ 2 and both subexprs evaluate in Ok state. -/
-- theorem exec_let_binary_call (n : ℕ) (hn : n ≥ 2) (var : Identifier)
--     (prim : Operation .Yul) (e₁ e₂ : Expr) (ss : SharedState .Yul) (vs : VarStore) (co)
--     (v₁ v₂ r : UInt256)
--     (heval₂ : Yul.eval n e₂ co (.Ok ss vs) = .ok (.Ok ss vs, v₂))
--     (heval₁ : Yul.eval (n - 1) e₁ co (.Ok ss vs) = .ok (.Ok ss vs, v₁))
--     (hprim : Yul.primCall (n + 1) (.Ok ss vs) prim [v₁, v₂] = .ok (.Ok ss vs, [r])) :
--     Yul.exec (n + 2) (.Let [var] (.some (.Call (Sum.inl prim) [e₁, e₂]))) co (.Ok ss vs) =
--     .ok ((.Ok ss vs).insert var r) := by
--   obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
--   simp at heval₁
--   unfold Yul.exec
--   simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
--   rw [evalArgs_succ_cons, heval₂, evalTail_succ, cons'_ok,
--       evalArgs_succ_cons, heval₁, evalTail_succ, cons'_ok, evalArgs_succ_nil,
--       reverse'_ok, execPrimCall_ok]
--   simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
--   rw [hprim, multifill'_ok_singleton, multifill_singleton_ok]

end Solady.Proofs.YulBase
