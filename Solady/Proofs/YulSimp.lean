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
--     "More fuel never changes a non-OutOfFuel result."
--     Proves once, used everywhere to lift a fuel=N proof to fuel≥N.
-- ============================================================================

mutual

/--
  `eval_monotonicity`: if `eval` returns a non-OutOfFuel result at fuel `n`,
  it returns the same result at any `m ≥ n`.

  Depends on `evalArgs_monotonicity` for argument list evaluation.
  User-defined function calls (.inr) require `call_monotonicity`.
-/
theorem eval_monotonicity {n : ℕ} {expr : Expr}
    {co : Option YulContract} {s : State}
    {r : Except Yul.Exception (State × UInt256)}
    (h_res : r ≠ .error .OutOfFuel)
    (h_eval : eval n expr co s = r) :
    ∀ m, m ≥ n → eval m expr co s = r := by
  induction n generalizing expr s r with
  | zero =>
    simp at h_eval
    subst h_eval
    exact absurd rfl h_res
  | succ n ih =>
    intro m hm
    cases m with
    | zero => omega
    | succ m =>
      have hm' : m ≥ n := Nat.le_of_succ_le_succ hm
      match expr with
      | .Lit v =>
        simp at h_eval ⊢; exact h_eval
      | .Var id =>
        simp at h_eval ⊢; exact h_eval
      | .Call (.inl prim) args =>
        -- evalPrimCall wraps primCall; args evaluated via evalArgs
        simp [eval] at h_eval ⊢
        -- evalArgs_monotonicity handles the argument list
        cases hargs : evalArgs n args.reverse co s with
        | error e =>
          simp [reverse', hargs] at h_eval
          subst h_eval
          -- h_res : .error e ≠ .error OutOfFuel
          have hne' : (.error e : Except Yul.Exception (State × List UInt256)) ≠ .error .OutOfFuel := by
            intro heq
            apply h_res
            simp [evalPrimCall, head', heq]
          have hargs' := evalArgs_monotonicity hne' hargs m hm'
          simp [reverse', hargs', evalPrimCall, head']
        | ok sv =>
          simp [reverse', hargs] at h_eval
          have hargs' := evalArgs_monotonicity (by simp) hargs m hm'
          rw [show evalArgs m args.reverse co s = .ok sv from hargs']
          simp [reverse', evalPrimCall, head']
          cases hprim : primCall n sv.1 prim sv.2.reverse with
          | error e =>
            simp [evalPrimCall, head', hprim] at h_eval
            subst h_eval
            have hne' : (.error e : Except Yul.Exception (State × List UInt256)) ≠ .error .OutOfFuel := by
              intro heq
              apply h_res
              simp [evalPrimCall, head', heq]
              exact Except.error.inj heq
            simp [primCall_monotonicity hne' hprim m hm']
          | ok res =>
            simp [evalPrimCall, head', hprim] at h_eval
            subst h_eval
            simp [primCall_monotonicity (by simp) hprim m hm']
      | .Call (.inr f) args =>
        -- user-defined function: requires call_monotonicity
        simp [eval] at h_eval ⊢
        cases hargs : evalArgs n args.reverse co s with
        | error e =>
          simp [reverse', hargs] at h_eval
          have hne' : (.error e : Except Yul.Exception (State × List UInt256)) ≠ .error .OutOfFuel := by
            intro heq
            apply h_res
            simp [evalArgs, reverse', heq] at h_eval
            subst h_eval
            simp [evalCall]
          have hargs' := evalArgs_monotonicity hne' hargs m hm'
          simp [reverse', hargs', evalCall, head']
          simp [evalCall] at h_eval
          apply h_eval
        | ok res =>
          simp [evalArgs, reverse', hargs] at h_eval
          have hargs' := evalArgs_monotonicity (by simp) hargs m hm'
          rw [show evalArgs m args.reverse co s = .ok res from hargs']
          simp [reverse', evalCall, head']
          unfold evalCall at h_eval ⊢
          cases hcall : call n res.2.reverse f co res.1 with
          | error e =>
            cases n with
            | zero =>
              simp [call] at hcall
              subst hcall
              exact absurd h_eval.symm h_res
            | succ n' =>
              simp at h_eval ⊢
              cases m with
              | zero => omega
              | succ m' =>
                have hm'' : m' ≥ n' := by omega
                simp [head'] at h_eval ⊢
                cases hcall' : call n' res.2.reverse (some f) co res.1 with
                | error e' =>
                  rw [hcall'] at h_eval
                  simp [head'] at h_eval
                  subst h_eval
                  have hne' : (.error e' : Except Yul.Exception (State × List EvmYul.Literal)) ≠ .error .OutOfFuel := by
                    intro heq
                    apply h_res
                    simp [call, Except.error.inj heq] at hcall'
                    simp [Except.error.inj heq]
                  rw [call_monotonicity hne' hcall' m' hm'']
                | ok sv =>
                  rw [hcall'] at h_eval
                  simp [head'] at h_eval
                  subst h_eval
                  rw [call_monotonicity (by simp) hcall' m' hm'']
          | ok sv =>
            cases n with
            | zero => simp [call] at hcall
            | succ n' =>
              cases m with
              | zero => omega
              | succ m' =>
                have hm'' : m' ≥ n' := by omega
                simp [head'] at h_eval ⊢
                cases hcall' : call n' res.2.reverse (some f) co res.1 with
                | error e' =>
                  rw [hcall'] at h_eval
                  simp [head'] at h_eval
                  subst h_eval
                  have hne' : (.error e' : Except Yul.Exception (State × List EvmYul.Literal)) ≠ .error .OutOfFuel := by
                    intro heq
                    apply h_res
                    simp [call, Except.error.inj heq] at hcall'
                    simp [Except.error.inj heq]
                  rw [call_monotonicity hne' hcall' m' hm'']
                | ok sv' =>
                  rw [hcall'] at h_eval
                  simp [head'] at h_eval
                  subst h_eval
                  rw [call_monotonicity (by simp) hcall' m' hm'']

/--
  `evalArgs_monotonicity`: if `evalArgs` returns a non-OutOfFuel result at fuel `n`,
  it returns the same result at any `m ≥ n`.

  Proved by induction on the argument list:
  - empty: trivially equal
  - cons: `eval_monotonicity` on head, recurse on tail
-/
theorem evalArgs_monotonicity {n : ℕ} {args : List Expr}
    {co : Option YulContract} {s : State}
    {r : Except Yul.Exception (State × List UInt256)}
    (h_res : r ≠ .error .OutOfFuel)
    (h_eval : evalArgs n args co s = r) :
    ∀ m, m ≥ n → evalArgs m args co s = r := by
  induction n generalizing args s r with
  | zero =>
    simp at h_eval
    subst h_eval
    exact absurd rfl h_res
  | succ n ih =>
    intro m hm
    cases m with
    | zero => omega
    | succ m =>
      have hm' : m ≥ n := Nat.le_of_succ_le_succ hm
      match args with
      | [] =>
        simp at h_eval ⊢; exact h_eval
      | arg :: rest =>
        -- evalArgs steps: eval head, then evalArgs on tail
        simp at h_eval ⊢
        cases harg : eval n arg co s with
        | error e =>
          -- head failed: lift error, bind propagates it
          simp [harg] at h_eval
          subst h_eval
          have hne' : (.error e : Except Yul.Exception (State × UInt256)) ≠ .error .OutOfFuel := h_res
          simp [eval_monotonicity hne' harg m hm']

        | ok sv =>
          -- head succeeded: lift, then recurse on tail
          simp [harg] at h_eval
          rw [eval_monotonicity (by simp) harg m hm']
          -- simp
          exact ih h_res h_eval m hm'

/--
  `primCall_monotonicity`: if `primCall` returns a non-OutOfFuel result at fuel `n`,
  it returns the same result at any `m ≥ n`.

  For non-contract opcodes (ADD, MUL, DIV, etc.), `primCall` delegates to `step`
  which does not recurse on fuel — so monotonicity is trivial.
  For contract-calling opcodes (CALL, STATICCALL, CALLCODE, DELEGATECALL),
  `primCall` recurses via `callDispatcher`, requiring `callDispatcher_monotonicity`.
-/
theorem primCall_monotonicity {n : ℕ} {s : State} {prim : PrimOp}
    {args : List UInt256}
    {r : Except Yul.Exception (State × List UInt256)}
    (h_res : r ≠ .error .OutOfFuel)
    (h_call : primCall n s prim args = r) :
    ∀ m, m ≥ n → primCall m s prim args = r := by
  induction n generalizing s r with
  | zero =>
    simp [primCall] at h_call
    subst h_call
    exact absurd rfl h_res
  | succ n ih =>
    intro m hm
    cases m with
    | zero => omega
    | succ m =>
      have hm' : m ≥ n := Nat.le_of_succ_le_succ hm
      simp [primCall] at h_call ⊢
      -- split on which opcode we're dealing with
      match prim with
      | .CALL =>
        -- delegates to callDispatcher which recurses on fuel
        simp [primCall] at h_call ⊢
        exact callDispatcher_monotonicity h_res h_call m hm'
      | .STATICCALL =>
        simp [primCall] at h_call ⊢
        exact callDispatcher_monotonicity h_res h_call m hm'
      | .CALLCODE =>
        simp [primCall] at h_call ⊢
        exact callDispatcher_monotonicity h_res h_call m hm'
      | .DELEGATECALL =>
        simp [primCall] at h_call ⊢
        exact callDispatcher_monotonicity h_res h_call m hm'
      | _ =>
        -- all other opcodes delegate to `step` which doesn't recurse on fuel
        -- so the result is independent of fuel beyond the outer check
        simp [primCall] at h_call ⊢
        exact h_call

/--
  `callDispatcher_monotonicity`: if `callDispatcher` returns a non-OutOfFuel
  result at fuel `n`, it returns the same result at any `m ≥ n`.

  `callDispatcher` calls `exec` on the contract's dispatcher body,
  so this requires `exec_monotonicity`.
-/
theorem callDispatcher_monotonicity {n : ℕ} {co : Option YulContract} {s : State}
    {r : Except Yul.Exception (State × List UInt256)}
    (h_res : r ≠ .error .OutOfFuel)
    (h_call : callDispatcher n co s = r) :
    ∀ m, m ≥ n → callDispatcher m co s = r := by
  induction n generalizing s r with
  | zero =>
    simp [callDispatcher] at h_call
    subst h_call
    exact absurd rfl h_res
  | succ n ih =>
    intro m hm
    cases m with
    | zero => omega
    | succ m =>
      have hm' : m ≥ n := Nat.le_of_succ_le_succ hm
      simp [callDispatcher] at h_call ⊢
      -- callDispatcher calls exec on the dispatcher body
      cases hexec : exec n (.Block [s.executionEnv.code.dispatcher]) co (👌 s.initcall [] []) with
      | error e =>
        simp [hexec] at h_call
        subst h_call
        have hne' : (.error e : Except Yul.Exception State) ≠ .error .OutOfFuel := h_res
        simp [exec_monotonicity hne' hexec m hm']
      | ok s₂ =>
        simp [hexec] at h_call
        rw [exec_monotonicity (by simp) hexec m hm']
        simp
        exact h_call

/--
  `call_monotonicity`: if `call` returns a non-OutOfFuel result at fuel `n`,
  it returns the same result at any `m ≥ n`.

  `call` calls `exec` on the function body, so this requires `exec_monotonicity`.
-/
theorem call_monotonicity {n : ℕ} {args : List UInt256}
    {f : Option YulFunctionName} {co : Option YulContract} {s : State}
    {r : Except Yul.Exception (State × List UInt256)}
    (h_res : r ≠ .error .OutOfFuel)
    (h_call : call n args f co s = r) :
    ∀ m, m ≥ n → call m args f co s = r := by
  induction n generalizing s r with
  | zero =>
    simp [call] at h_call
    subst h_call
    exact absurd rfl h_res
  | succ n ih =>
    intro m hm
    cases m with
    | zero => omega
    | succ m =>
      have hm' : m ≥ n := Nat.le_of_succ_le_succ hm
      simp [call] at h_call ⊢
      -- call looks up the function definition then calls exec on its body
      cases hfind : s.sharedState.accountMap.find? s.executionEnv.codeOwner with
      | none =>
        simp [hfind] at h_call ⊢
        exact h_call
      | some yulContract =>
        simp [hfind] at h_call ⊢
        -- split on function lookup
        cases hfopt : (match f with
          | none => some (FunctionDefinition.Def [] [] [_])
          | some name => yulContract.code.functions.lookup name) with
        | none =>
          simp [hfopt] at h_call ⊢; exact h_call
        | some fdef =>
          simp [hfopt] at h_call ⊢
          -- exec on function body
          cases hexec : exec n (.Block fdef.body) co (👌 s.initcall fdef.params args) with
          | error e =>
            simp [hexec] at h_call
            subst h_call
            have hne' : (.error e : Except Yul.Exception State) ≠ .error .OutOfFuel := h_res
            simp [exec_monotonicity hne' hexec m hm']
          | ok s₂ =>
            simp [hexec] at h_call
            rw [exec_monotonicity (by simp) hexec m hm']
            simp
            exact h_call

/--
  `loop_monotonicity`: if `loop` returns a non-OutOfFuel result at fuel `n`,
  it returns the same result at any `m ≥ n`.

  `loop` recurses on both `eval` (condition) and `exec` (body, post),
  so requires both `eval_monotonicity` and `exec_monotonicity`.
-/
theorem loop_monotonicity {n : ℕ} {cond : Expr} {post body : List Stmt}
    {co : Option YulContract} {s : State}
    {r : Except Yul.Exception State}
    (h_res : r ≠ .error .OutOfFuel)
    (h_loop : loop n cond post body co s = r) :
    ∀ m, m ≥ n → loop m cond post body co s = r := by
  induction n generalizing s r with
  | zero =>
    simp [loop] at h_loop
    subst h_loop
    exact absurd rfl h_res
  | succ n ih =>
    intro m hm
    cases m with
    | zero => omega
    | succ m =>
      -- loop needs at least 2 fuel (defined as `| 1 => .error .OutOfFuel`)
      cases m with
      | zero =>
        -- m+1 = 1, need n+1 ≤ 1 so n = 0, but we're in succ n case
        omega
      | succ m =>
        have hm' : m ≥ n := by omega
        simp [loop] at h_loop ⊢
        -- evaluate loop condition
        cases hcond : eval n cond co (👌 s) with
        | error e =>
          simp [hcond] at h_loop
          subst h_loop
          have hne' : (.error e : Except Yul.Exception (State × UInt256)) ≠ .error .OutOfFuel := h_res
          simp [eval_monotonicity hne' hcond m hm']
        | ok sv =>
          obtain ⟨s₁, v⟩ := sv
          simp [hcond] at h_loop ⊢
          rw [eval_monotonicity (by simp) hcond m hm']
          simp
          -- split on whether loop condition is zero (exit) or nonzero (continue)
          split_ifs with hv
          · -- condition zero: loop exits
            exact h_loop
          · -- condition nonzero: execute body
            cases hbody : exec n (.Block body) co s₁ with
            | error e =>
              simp [hbody] at h_loop
              subst h_loop
              have hne' : (.error e : Except Yul.Exception State) ≠ .error .OutOfFuel := h_res
              simp [exec_monotonicity hne' hbody m hm']
            | ok s₂ =>
              simp [hbody] at h_loop ⊢
              rw [exec_monotonicity (by simp) hbody m hm']
              simp
              -- handle control flow checkpoints from body
              match s₂ with
              | .OutOfFuel =>
                simp at h_loop ⊢; exact h_loop
              | .Checkpoint (.Break _ _) =>
                simp at h_loop ⊢; exact h_loop
              | .Checkpoint (.Leave _ _) =>
                simp at h_loop ⊢; exact h_loop
              | _ =>
                -- continue: execute post block, then recurse
                cases hpost : exec n (.Block post) co (🧟 s₂) with
                | error e =>
                  simp [hpost] at h_loop
                  subst h_loop
                  have hne' : (.error e : Except Yul.Exception State) ≠ .error .OutOfFuel := h_res
                  simp [exec_monotonicity hne' hpost m hm']
                | ok s₃ =>
                  simp [hpost] at h_loop ⊢
                  rw [exec_monotonicity (by simp) hpost m hm']
                  simp
                  -- recurse on the loop itself
                  cases hfor : exec n (.For cond post body) co (s₃✏️⟦s⟧?) with
                  | error e =>
                    simp [hfor] at h_loop
                    subst h_loop
                    have hne' : (.error e : Except Yul.Exception State) ≠ .error .OutOfFuel := h_res
                    simp [exec_monotonicity hne' hfor m hm']
                  | ok s₅ =>
                    simp [hfor] at h_loop ⊢
                    rw [exec_monotonicity (by simp) hfor m hm']
                    simp
                    exact h_loop



/--
  `execSwitchCases_monotonicity`: if `execSwitchCases` returns a non-OutOfFuel
  result at fuel `n`, it returns the same result at any `m ≥ n`.

  The return type `List (Literal × Except Exception State)` means OutOfFuel
  can appear either as the outer error or inside each branch result.
  We need to lift both:
  - The outer `Except` (execSwitchCases itself failing)
  - Each inner `Except` (individual branch results)

  We handle the inner ones by proving a helper first.
-/
theorem execSwitchCases_monotonicity {n : ℕ} {co : Option YulContract} {s : State}
    {cases' : List (EvmYul.Literal × List Stmt)}
    {r : Except Yul.Exception (List (EvmYul.Literal × Except Yul.Exception State))}
    (h_res : r ≠ .error .OutOfFuel)
    (h_exec : execSwitchCases n co s cases' = r) :
    ∀ m, m ≥ n → execSwitchCases m co s cases' = r := by
  induction n generalizing cases' s r with
  | zero =>
    -- fuel=0 with non-empty cases always returns OutOfFuel
    match cases' with
    | [] =>
      -- empty cases: result is .ok [] regardless of fuel, no monotonicity needed
      simp [execSwitchCases] at h_exec ⊢
      intro m _; exact h_exec
    | _ :: _ =>
      simp [execSwitchCases] at h_exec
      subst h_exec
      exact absurd rfl h_res
  | succ n ih =>
    intro m hm
    cases m with
    | zero => omega
    | succ m =>
      have hm' : m ≥ n := Nat.le_of_succ_le_succ hm
      match cases' with
      | [] =>
        -- empty: always .ok [], fuel irrelevant
        simp [execSwitchCases] at h_exec ⊢
        exact h_exec
      | (val, stmts) :: rest =>
        simp [execSwitchCases] at h_exec ⊢
        -- exec on this branch's body
        cases hbranch : exec n (.Block stmts) co s with
        | error (.YulHalt s₂ v) =>
          -- branch halted: lift via exec_monotonicity, recurse on rest
          simp [hbranch] at h_exec
          cases hrest : execSwitchCases n co s rest with
          | error e =>
            simp [hrest] at h_exec
            subst h_exec
            have hne_branch : (.error (.YulHalt s₂ v) : Except Yul.Exception State)
                ≠ .error .OutOfFuel := by simp
            have hne_rest : (.error e : Except Yul.Exception
                (List (Literal × Except Yul.Exception State))) ≠ .error .OutOfFuel := h_res
            rw [exec_monotonicity hne_branch hbranch m hm']
            simp
            rw [ih hne_rest hrest m hm']
          | ok rest' =>
            simp [hrest] at h_exec
            subst h_exec
            have hne_branch : (.error (.YulHalt s₂ v) : Except Yul.Exception State)
                ≠ .error .OutOfFuel := by simp
            rw [exec_monotonicity hne_branch hbranch m hm']
            simp
            rw [ih (by simp) hrest m hm']
        | error e =>
          -- branch errored (non-YulHalt): lift, recurse on rest
          simp [hbranch] at h_exec
          cases hrest : execSwitchCases n co s rest with
          | error e' =>
            simp [hrest] at h_exec
            subst h_exec
            -- e could be OutOfFuel if the branch itself ran out —
            -- but then h_res would be contradicted via the outer error
            by_cases heof : e = .OutOfFuel
            · subst heof
              -- exec n returned OutOfFuel: h_exec was .error OutOfFuel = r
              -- but we subst'd h_exec so r = .error e' from hrest
              -- and h_res says r ≠ .error OutOfFuel — contradiction
              exact absurd rfl h_res
            · have hne_branch : (.error e : Except Yul.Exception State)
                  ≠ .error .OutOfFuel := by simp [heof]
              have hne_rest : (.error e' : Except Yul.Exception
                  (List (Literal × Except Yul.Exception State))) ≠ .error .OutOfFuel := h_res
              rw [exec_monotonicity hne_branch hbranch m hm']
              simp
              rw [ih hne_rest hrest m hm']
          | ok rest' =>
            simp [hrest] at h_exec
            subst h_exec
            by_cases heof : e = .OutOfFuel
            · subst heof
              exact absurd rfl h_res
            · have hne_branch : (.error e : Except Yul.Exception State)
                  ≠ .error .OutOfFuel := by simp [heof]
              rw [exec_monotonicity hne_branch hbranch m hm']
              simp
              rw [ih (by simp) hrest m hm']
        | ok s₂ =>
          -- branch succeeded: lift, recurse on rest
          simp [hbranch] at h_exec
          cases hrest : execSwitchCases n co s rest with
          | error e =>
            simp [hrest] at h_exec
            subst h_exec
            have hne_rest : (.error e : Except Yul.Exception
                (List (Literal × Except Yul.Exception State))) ≠ .error .OutOfFuel := h_res
            rw [exec_monotonicity (by simp) hbranch m hm']
            simp
            rw [ih hne_rest hrest m hm']
          | ok rest' =>
            simp [hrest] at h_exec
            subst h_exec
            rw [exec_monotonicity (by simp) hbranch m hm']
            simp
            rw [ih (by simp) hrest m hm']

/--
  `exec_monotonicity`: if `exec` returns a non-OutOfFuel result at fuel `n`,
  it returns the same result at any `m ≥ n`.

  This is the main monotonicity lemma. All other lemmas in this block
  feed into this one.

  Remaining sorry: Switch requires execSwitchCases_monotonicity which
  follows the same pattern but is omitted for brevity.
-/
theorem exec_monotonicity {n : ℕ} {stmt : Stmt}
    {co : Option YulContract} {s : State} {r : Except Yul.Exception State}
    (h_res : r ≠ .error .OutOfFuel)
    (h_exec : exec n stmt co s = r) :
    ∀ m, m ≥ n → exec m stmt co s = r := by
  induction n generalizing stmt s r with
  | zero =>
    simp at h_exec
    subst h_exec
    exact absurd rfl h_res
  | succ n ih =>
    intro m hm
    cases m with
    | zero => omega
    | succ m =>
      have hm' : m ≥ n := Nat.le_of_succ_le_succ hm
      match stmt with
      | .Block [] =>
        simp at h_exec ⊢; exact h_exec
      | .Block (stmt :: stmts) =>
        rw [exec_block_cons] at h_exec ⊢
        cases hstmt : exec n stmt co s with
        | error e =>
          rw [hstmt] at h_exec
          subst h_exec
          have hne' : (.error e : Except Yul.Exception State) ≠ .error .OutOfFuel := h_res
          simp [ih hne' hstmt m hm']
        | ok s₁ =>
          rw [hstmt] at h_exec
          have h_exec' : exec n (.Block stmts) co s₁ = r := by
            have : (Except.ok s₁ >>= fun s => exec n (.Block stmts) co s) = r := h_exec
            simpa using this
          rw [ih (by simp) hstmt m hm']
          show exec m (.Block stmts) co s₁ = r
          exact ih h_res h_exec' m hm'
      | .Let vars none =>
        simp at h_exec ⊢; exact h_exec
      | .Let vars (some (.Lit v)) =>
        simp at h_exec ⊢; exact h_exec
      | .Let vars (some (.Var id)) =>
        simp at h_exec ⊢; exact h_exec
      | .Let vars (some (.Call (.inl prim) args)) =>
        -- primop let: evalArgs then primCall, both monotone
        simp at h_exec ⊢
        cases hargs : evalArgs n args.reverse co s with
        | error e =>
          simp [reverse', hargs] at h_exec
          subst h_exec
          have hne' : (.error e : Except Yul.Exception (State × List UInt256)) ≠ .error .OutOfFuel := h_res
          simp [reverse', evalArgs_monotonicity hne' hargs m hm']
        | ok sv =>
          simp [reverse', hargs] at h_exec ⊢
          rw [evalArgs_monotonicity (by simp) hargs m hm']
          simp
          exact primCall_monotonicity h_res h_exec m hm'
      | .Let vars (some (.Call (.inr f) args)) =>
        -- user function let: evalArgs then call, both monotone
        simp [exec] at h_exec ⊢
        cases hargs : evalArgs n args.reverse co s with
        | error e =>
          simp [reverse', hargs] at h_exec
          subst h_exec
          have hne' : (.error e : Except Yul.Exception (State × List UInt256)) ≠ .error .OutOfFuel := h_res
          simp [reverse', evalArgs_monotonicity hne' hargs m hm']
        | ok sv =>
          simp [reverse', hargs] at h_exec ⊢
          rw [evalArgs_monotonicity (by simp) hargs m hm']
          simp
          exact call_monotonicity h_res h_exec m hm'
      | .If cond body =>
        -- if: lift condition eval, then lift body if nonzero
        simp [exec] at h_exec ⊢
        cases hcond : eval n cond co s with
        | error e =>
          simp [hcond] at h_exec
          subst h_exec
          have hne' : (.error e : Except Yul.Exception (State × UInt256)) ≠ .error .OutOfFuel := h_res
          simp [eval_monotonicity hne' hcond m hm']
        | ok sv =>
          obtain ⟨s₁, v⟩ := sv
          simp [hcond] at h_exec ⊢
          rw [eval_monotonicity (by simp) hcond m hm']
          simp
          split_ifs with hv
          · exact h_exec
          · exact exec_monotonicity h_res h_exec m hm'
      | .ExprStmtCall (.Call (.inl prim) args) =>
        -- primop statement: same as primop let but result discarded
        simp at h_exec ⊢
        cases hargs : evalArgs n args.reverse co s with
        | error e =>
          simp [reverse', hargs] at h_exec
          subst h_exec
          have hne' : (.error e : Except Yul.Exception (State × List UInt256)) ≠ .error .OutOfFuel := h_res
          simp [reverse', evalArgs_monotonicity hne' hargs m hm']
        | ok sv =>
          simp [reverse', hargs] at h_exec ⊢
          rw [evalArgs_monotonicity (by simp) hargs m hm']
          simp
          exact primCall_monotonicity h_res h_exec m hm'
      | .ExprStmtCall (.Call (.inr f) args) =>
        -- user function statement
        simp [exec] at h_exec ⊢
        cases hargs : evalArgs n args.reverse co s with
        | error e =>
          simp [reverse', hargs] at h_exec
          subst h_exec
          have hne' : (.error e : Except Yul.Exception (State × List UInt256)) ≠ .error .OutOfFuel := h_res
          simp [reverse', evalArgs_monotonicity hne' hargs m hm']
        | ok sv =>
          simp [reverse', hargs] at h_exec ⊢
          rw [evalArgs_monotonicity (by simp) hargs m hm']
          simp
          exact call_monotonicity h_res h_exec m hm'
      | .ExprStmtCall (Expr.Lit _) =>
        -- always errors with InvalidExpression
        simp [exec] at h_exec
        subst h_exec
        simp [exec]
      | .ExprStmtCall (Expr.Var _) =>
        simp [exec] at h_exec
        subst h_exec
        simp [exec]
      | .Continue => simp at h_exec ⊢; exact h_exec
      | .Break    => simp at h_exec ⊢; exact h_exec
      | .Leave    => simp at h_exec ⊢; exact h_exec
      | .For cond post body =>
        -- delegate to loop_monotonicity
        simp [exec] at h_exec ⊢
        exact loop_monotonicity h_res h_exec m hm'
      | .Switch cond cases' default' =>
        simp [exec] at h_exec ⊢
        cases hcond : eval n cond co s with
        | error e =>
          simp [hcond] at h_exec
          subst h_exec
          have hne' : (.error e : Except Yul.Exception (State × UInt256)) ≠ .error .OutOfFuel := h_res
          simp [eval_monotonicity hne' hcond m hm']
        | ok sv =>
          obtain ⟨s₁, v⟩ := sv
          simp [hcond] at h_exec ⊢
          rw [eval_monotonicity (by simp) hcond m hm']
          simp
          cases hcases : execSwitchCases n co s₁ cases' with
          | error e =>
            simp [hcases] at h_exec
            subst h_exec
            have hne' : (.error e : Except Yul.Exception _) ≠ .error .OutOfFuel := h_res
            simp [execSwitchCases_monotonicity hne' hcases m hm']
          | ok branches =>
            simp [hcases] at h_exec ⊢
            rw [execSwitchCases_monotonicity (by simp) hcases m hm']
            simp
            cases hdefault : exec n (.Block default') co s₁ with
            | error e =>
              simp [hdefault] at h_exec
              subst h_exec
              have hne' : (.error e : Except Yul.Exception State) ≠ .error .OutOfFuel := h_res
              simp [exec_monotonicity hne' hdefault m hm']
            | ok s₂ =>
              simp [hdefault] at h_exec ⊢
              rw [exec_monotonicity (by simp) hdefault m hm']
              simp
              exact h_exec

end

/-- `exec_mono` as a corollary of `exec_monotonicity`. -/
theorem exec_monotonicity_ok {n : ℕ} (stmt : Stmt) (co : Option YulContract)
    (s s' : State) (h : exec n stmt co s = .ok s') :
    ∀ m, m ≥ n → exec m stmt co s = .ok s' :=
  exec_monotonicity (by simp) h

end Solady.Proofs.YulSimp
