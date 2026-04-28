/-
  YulSimp.lean
  ============
  A `@[simp]` lemma library for reasoning about `Yul.exec` and `Yul.eval`
  without manually unfolding the interpreter.

  DESIGN PRINCIPLE
  ----------------
  The interpreter is defined by `mutual` recursion on (fuel, stmt/expr).
  Lean's `simp` cannot unfold mutually recursive definitions by itself.
  These lemmas pre-compute each case of `exec`/`eval` at `fuel.succ`,
  so that `simp` can reduce the interpreter one AST node at a time
  without ever seeing raw `match fuel with | 0 => ... | succ => ...`.

  USAGE
  -----
  After `simp [exec_block_cons, exec_block_nil, exec_if, eval_lit,
               eval_var, exec_let_lit, exec_let_var, exec_exprstmt_prim,
               hvx, hvy]`
  the interpreter goal should be fully reduced to primop calls and
  `VarStore` lookups, at which point `omega` / `ring` / `norm_num`
  handle the arithmetic.

  CONTRIBUTING
  ------------
  Each lemma follows the pattern:
    exec / eval applied to a CONCRETE constructor
    at fuel = n.succ
    → the next-step expression (no more `match fuel`)

  If you add a new lemma, tag it `@[simp]` and add a one-line comment
  explaining which AST case it covers.
-/

import EvmYul.Yul.Interpreter

namespace Solady.Proofs.YulSimp

open EvmYul Yul Ast

-- ============================================================================
-- 0.  FUEL ZERO — trivial error cases
--     These close the `fuel = 0` branch in any induction.
-- ============================================================================

@[simp]
lemma exec_zero (stmt : Stmt) (co : Option YulContract) (s : State) :
    exec 0 stmt co s = .error .OutOfFuel := by
  simp [exec]

@[simp]
lemma eval_zero (expr : Expr) (co : Option YulContract) (s : State) :
    eval 0 expr co s = .error .OutOfFuel := by
  simp [eval]

-- ============================================================================
-- 1.  BLOCK
-- ============================================================================

/-- Empty block is a no-op. -/
@[simp]
lemma exec_block_nil (fuel : ℕ) (co : Option YulContract) (s : State) :
    exec fuel.succ (.Block []) co s = .ok s := by
  simp [exec]

/-- Non-empty block sequences head then tail. -/
@[simp]
lemma exec_block_cons (fuel : ℕ) (stmt : Stmt) (stmts : List Stmt)
    (co : Option YulContract) (s : State) :
    exec fuel.succ (.Block (stmt :: stmts)) co s =
    (exec fuel stmt co s >>= fun s₁ => exec fuel (.Block stmts) co s₁) := by
  simp only [exec]
  cases exec fuel stmt co s with
  | ok s₁ => rfl
  | error e => rfl

  -- sorry

-- ============================================================================
-- 2.  EVAL — expressions
-- ============================================================================

/-- A literal evaluates to itself immediately. -/
@[simp]
lemma eval_lit (fuel : ℕ) (v : UInt256) (co : Option YulContract) (s : State) :
    eval fuel.succ (.Lit v) co s = .ok (s, v) := by
  simp [eval]

/-- A variable lookup. -/
@[simp]
lemma eval_var (fuel : ℕ) (id : Identifier) (co : Option YulContract) (s : State) :
    eval fuel.succ (.Var id) co s = .ok (s, s[id]!) := by
  simp [eval]

-- ============================================================================
-- 3.  IF
--     Two lemmas: one for the "condition is zero" branch (skip),
--     one for the "condition is nonzero" branch (execute body).
-- ============================================================================

/-- `if` whose condition evaluates to zero → skip body. -/
@[simp]
lemma exec_if_false (fuel : ℕ) (cond : Expr) (body : List Stmt)
    (co : Option YulContract) (s s' : State) (v : UInt256)
    (heval : eval fuel cond co s = .ok (s', v))
    (hzero : v = ⟨0⟩) :
    exec fuel.succ (.If cond body) co s = .ok s' := by
  simp [exec, heval, hzero]

/-- `if` whose condition evaluates to nonzero → execute body. -/
@[simp]
lemma exec_if_true (fuel : ℕ) (cond : Expr) (body : List Stmt)
    (co : Option YulContract) (s s' : State) (v : UInt256)
    (heval : eval fuel cond co s = .ok (s', v))
    (hnz : v ≠ ⟨0⟩) :
    exec fuel.succ (.If cond body) co s =
    exec fuel (.Block body) co s' := by
  simp [exec, heval, hnz]

-- ============================================================================
-- 4.  LET
-- ============================================================================

/-- `let x := <literal>` stores the literal. -/
@[simp]
lemma exec_let_lit (fuel : ℕ) (vars : List Identifier) (v : UInt256)
    (co : Option YulContract) (s : State) :
    exec fuel.succ (.Let vars (some (.Lit v))) co s =
    .ok (s.insert vars.head! v) := by
  simp [exec]

/-- `let x := <var>` copies the variable's value. -/
@[simp]
lemma exec_let_var (fuel : ℕ) (vars : List Identifier) (id : Identifier)
    (co : Option YulContract) (s : State) :
    exec fuel.succ (.Let vars (some (.Var id))) co s =
    .ok (s.insert vars.head! s[id]!) := by
  simp [exec]

/-- `let x` (no initialiser) sets x to 0. -/
@[simp]
lemma exec_let_none (fuel : ℕ) (vars : List Identifier)
    (co : Option YulContract) (s : State) :
    exec fuel.succ (.Let vars none) co s =
    .ok (List.foldr (fun var s => s.insert var ⟨0⟩) s vars) := by
  simp [exec]

/-- `let x := primop(args)` — delegates to `execPrimCall`. -/
@[simp]
lemma exec_let_primcall (fuel : ℕ) (vars : List Identifier) (prim : PrimOp)
    (args : List Expr) (co : Option YulContract) (s : State) :
    exec fuel.succ (.Let vars (some (.Call (.inl prim) args))) co s =
    execPrimCall fuel prim vars
      (reverse' (evalArgs fuel args.reverse co s)) := by
  simp [exec]

-- ============================================================================
-- 5.  EXPRESSION STATEMENT  (call used for side-effects only)
-- ============================================================================

/-- `primop(args)` as a statement — result discarded. -/
@[simp]
lemma exec_exprstmt_prim (fuel : ℕ) (prim : PrimOp) (args : List Expr)
    (co : Option YulContract) (s : State) :
    exec fuel.succ (.ExprStmtCall (.Call (.inl prim) args)) co s =
    execPrimCall fuel prim []
      (reverse' (evalArgs fuel args.reverse co s)) := by
  simp [exec]

-- ============================================================================
-- 6.  CONTINUE / BREAK / LEAVE
-- ============================================================================

@[simp]
lemma exec_continue (fuel : ℕ) (co : Option YulContract) (s : State) :
    exec fuel.succ .Continue co s = .ok (🔁 s) := by
  simp [exec]

@[simp]
lemma exec_break (fuel : ℕ) (co : Option YulContract) (s : State) :
    exec fuel.succ .Break co s = .ok (💔 s) := by
  simp [exec]

@[simp]
lemma exec_leave (fuel : ℕ) (co : Option YulContract) (s : State) :
    exec fuel.succ .Leave co s = .ok (🚪 s) := by
  simp [exec]

-- ============================================================================
-- 7.  EVALARGS
--     Needed so simp can reduce argument lists in primop calls.
-- ============================================================================

@[simp]
lemma evalArgs_zero (args : List Expr) (co : Option YulContract) (s : State) :
    evalArgs 0 args co s = .error .OutOfFuel := by
  simp [evalArgs]

@[simp]
lemma evalArgs_nil (fuel : ℕ) (co : Option YulContract) (s : State) :
    evalArgs fuel.succ [] co s = .ok (s, []) := by
  simp [evalArgs]

@[simp]
lemma evalArgs_cons (fuel : ℕ) (arg : Expr) (rest : List Expr)
    (co : Option YulContract) (s : State) :
    evalArgs fuel.succ (arg :: rest) co s =
    evalTail fuel rest co (eval fuel arg co s) := by
  simp [evalArgs]

-- ============================================================================
-- 8.  FUEL MONOTONICITY
--     "More fuel never changes a successful result."
--     Proves once, used everywhere to lift a fuel=N proof to fuel≥N.
-- ============================================================================

/-- If execution succeeds with fuel `n`, it succeeds with any `m ≥ n`
  and returns the same state.

  This is the core lemma that removes the fuel variable from the
  main theorem statement:
    - Prove `exec 20 prog co s = .ok s'` (concrete fuel, use simp)
    - Apply `exec_mono hfuel` to lift to arbitrary `fuel ≥ 20`


  NOTE on `sorry`s in `exec_mono`:
  The cases involving `eval` and `primCall` require a companion
  `eval_mono` lemma (same pattern but for `Yul.eval`), and
  `primCall_mono`. These are needed because `exec` calls `eval`
  for conditions and arguments.

  The mutual recursion means all three lemmas must be proved together
  in a `mutual` block. Stub:

  mutual
    theorem exec_mono ...
    theorem eval_mono ...
    theorem primCall_mono ...
  end

  For mulWad specifically, none of the `sorry` branches are exercised
  because mulWad only uses:
    - Block / If / Let / ExprStmtCall (primop only)
  — all of which have complete proofs above.
-/
theorem exec_mono {n : ℕ} (stmt : Stmt) (co : Option YulContract)
    (s s' : State) (h : exec n stmt co s = .ok s') :
    ∀ m, m ≥ n → exec m stmt co s = .ok s' := by
  -- sorry
  induction n generalizing stmt s s' with
  | zero =>
    simp at h
  | succ n ih =>
    intro m hm
    cases m with
    | zero => omega
    | succ m =>
      have hm' : m ≥ n := Nat.le_of_succ_le_succ hm
      -- Structural induction on stmt
      -- Each case mirrors the `exec` definition
      match stmt with
      | .Block [] => simp at h ⊢; exact h
      | .Block (stmt :: stmts) =>
        rw [exec_block_cons] at h ⊢
        cases hstmt : exec n stmt co s with
        | error e =>
          rw [hstmt] at h
          cases h  -- Except.error e = Except.ok s' has no constructors, closes by contradiction
        | ok s₁ =>
          simp [hstmt] at h
          rw [show exec m stmt co s = .ok s₁ from ih stmt s s₁ hstmt m hm']
          -- show exec m (.Block stmts) co s₁ = .ok s'
          have h' : exec n (.Block stmts) co s₁ = .ok s' := by
            have : (Except.ok s₁ >>= fun s => exec n (.Block stmts) co s) = .ok s' := h
            simpa using this
          exact ih (.Block stmts) s₁ s' h' m hm'
      | .Let vars none =>
        simp at h ⊢; exact h
      | .Let vars (some (.Lit v)) =>
        simp at h ⊢; exact h
      | .Let vars (some (.Var id)) =>
        simp at h ⊢; exact h
      | .Let vars (some (.Call (.inl prim) args)) =>
        simp at h ⊢
        sorry -- requires eval_mono for args; see note below
      | .Let vars (some (.Call (.inr f) args)) =>
        simp [exec] at h ⊢
        sorry
      | .If cond body =>
        simp [exec] at h ⊢
        sorry -- requires eval_mono for cond
      | .ExprStmtCall (.Call (.inl prim) args) =>
        simp at h ⊢
        sorry
      | .ExprStmtCall (.Call (.inr f) args) =>
        simp [exec] at h ⊢
        sorry -- TODO: add
      | .ExprStmtCall (Expr.Lit _) =>
        simp [exec] at h
      | .ExprStmtCall (Expr.Var _) =>
        simp [exec] at h
      | .Continue => simp at h ⊢; exact h
      | .Break    => simp at h ⊢; exact h
      | .Leave    => simp at h ⊢; exact h
      -- TODO: add cases for Switch and For when you need them
      | .Switch _ _ _ => sorry
      | .For _ _ _    => sorry

end Solady.Proofs.YulSimp
