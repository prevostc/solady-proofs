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
import Solady.Proofs.YulSimp

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
open Solady.Proofs.YulSimp

def interpret_mulWad_result (r : Except Yul.Exception Yul.State) : Option ℕ :=
  match r with
  | .ok s => some (s.lookup! "z").toNat
  | .error .Revert => .none
  | .error _ => none


def MULWAD_FUEL : ℕ := 12

def mulWad_exec_test (fuel : ℕ) (x y : ℕ) : Except Yul.Exception Yul.State :=
  let vs : VarStore := (∅ : VarStore)
    |>.insert "x" (UInt256.ofNat x)
    |>.insert "y" (UInt256.ofNat y)
  Yul.exec fuel (.Block Solady.Code.mulWad_yul.body) none (.Ok Inhabited.default vs)

def mulWad_exec_result (fuel : ℕ) (x y : ℕ) : Option ℕ :=
  match mulWad_exec_test fuel x y with
  | .ok (.Ok _ vs) => (vs.lookup "z").map (·.val.val)
  | _ => none

def mulWad_exec_is_out_of_fuel (fuel x y : ℕ) : Bool :=
  match mulWad_exec_test fuel x y with
  | .error .OutOfFuel => true
  | _ => false

def FUEL_OK : ℕ := 12

#eval do
  let result := mulWad_exec_test FUEL_OK (2 * 10^18) (3 * 10^18)
  return match result with
    | .ok s => s!"ok, z = {(State.lookup! "z" s).val.val}"
    | .error .OutOfFuel => "error: OutOfFuel"
    | .error .Revert => "error: Revert"
    | .error _ => "error: other"

-- For large numbers `decide` will time out, so we disable it for these examples only
set_option linter.style.nativeDecide false
-- fuel sufficiency
example : mulWad_exec_result FUEL_OK (2 * 10^18) (3 * 10^18) = some (6 * 10^18) :=
  by native_decide
example : mulWad_exec_is_out_of_fuel (FUEL_OK - 1) (2 * 10^18) (3 * 10^18) = true :=
  by native_decide
-- correctness spot checks
example : mulWad_exec_result FUEL_OK (5 * 10^18) (2 * 10^18) = some (10 * 10^18) :=
  by native_decide
example : mulWad_exec_result FUEL_OK 0            (3 * 10^18) = some 0  :=
  by native_decide
-- revert on overflow
example : mulWad_exec_is_out_of_fuel (FUEL_OK - 1) (2^200) (2^200) = true := by native_decide

set_option linter.style.nativeDecide true


/--
  Any `fuel ≥ FUEL_OK` can be reduced to exactly `fuel = FUEL_OK` for the
  purposes of `exec` on `mulWad_yul.body`.
  Proof: apply `exec_mono` after establishing the fuel=20 case.
-/
lemma mulWad_fuel_sufficient
    (fuel : ℕ) (hfuel : fuel ≥ FUEL_OK)
    (stmt : Stmt) (co : Option YulContract) (s s' : State)
    (hfuel_ok : exec FUEL_OK stmt co s = .ok s') :
    exec fuel stmt co s = .ok s' :=
  exec_mono stmt co s s' hfuel_ok fuel hfuel


theorem mulWad_implem_is_correct (x y fuel : ℕ) (vs : VarStore)
    (ss : SharedState .Yul) (co : Option YulContract)
    (hfuel : fuel ≥ FUEL_OK)
    (hvx : vs.lookup "x" = some (UInt256.ofNat x))
    (hvy : vs.lookup "y" = some (UInt256.ofNat y)) :
    interpret_mulWad_result
      (Yul.exec fuel (.Block mulWad_yul.body) co (.Ok ss vs))
    = mulWad x y
  := by

  -- Step 1: reduce the fuel to FUEL_OK
  suffices h : Yul.exec FUEL_OK (.Block mulWad_yul.body) co (.Ok ss vs)
              = Yul.exec fuel (.Block mulWad_yul.body) co (.Ok ss vs) by
    rw [← h]
    -- now goal only mentions FUEL_OK, prove it
    sorry
  -- Step 2: prove the fuel reduction
  apply mulWad_fuel_sufficient fuel hfuel
  rfl

  simp only [interpret_mulWad_result, mulWad_yul]
  unfold Yul.exec
  -- goal is now: exec 20 (.Block mulWad_yul.body) co (.Ok ss vs) = ...
  simp only [exec_block_cons, exec_block_nil, exec_if_true, exec_if_false,
        exec_let_primcall, exec_exprstmt_prim, eval_lit, eval_var,
        evalArgs_cons, evalArgs_nil, hvx, hvy]


  -- goal is now pure arithmetic / VarStore equalities
  by_cases hov : x * y > U256_MAX <;> simp_all <;> omega


  unfold mulWad
  by_cases hov : x * y > U256_MAX
  case pos =>
    simp [hov] at hov
    sorry
  case neg =>
    simp [hov] at hov
    sorry




-- Yul: gt(x, div(U256_MAX, y))  ↔  x > U256_MAX / y  ↔  x * y > U256_MAX
-- (for y ≠ 0, this is exactly Nat.div_lt_iff_lt_mul or similar)
lemma overflow_condition (x y : ℕ) (hy : y ≠ 0) :
    x > U256_MAX / y ↔ x * y > U256_MAX := by
  constructor
  -- · intro h; exact Nat.lt_of_div_lt_div ... -- roughly
  -- · intro h; exact Nat.div_lt_iff_lt_mul ...
  . sorry
  . sorry

lemma uint256_mul_no_overflow (x y : ℕ) (h : x * y < 2^256) :
    (UInt256.ofNat x * UInt256.ofNat y).val.val = x * y := by
  -- simp [UInt256.ofNat, HMul.hMul, Mul.mul, UInt256.mul]
  -- -- reduces to: (x % 2^256 * (y % 2^256)) % 2^256 = x * y
  -- omega  -- or: rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]; exact Nat.mod_eq_of_lt h
  . sorry

theorem mulWad_implem_is_correct_proof : mulWad_implem_is_correct := by sorry

-- Case 1: no overflow, returns a value
def mulWad_correct_no_overflow : Prop :=
  ∀ x y fuel vs ss co,
    x * y ≤ U256_MAX →           -- the actual meaningful condition
    fuel ≥ 20 →
    vs.lookup "x" = some (UInt256.ofNat x) →
    vs.lookup "y" = some (UInt256.ofNat y) →
    interpret_mulWad_result (...) = some (x * y / WAD)

-- Case 2: overflow, execution reverts
def mulWad_correct_overflow : Prop :=
  ∀ x y fuel vs ss co,
    x * y > U256_MAX →
    y ≠ 0 →                       -- Yul only reverts when y ≠ 0
    fuel ≥ 20 →
    vs.lookup "x" = some (UInt256.ofNat x) →
    vs.lookup "y" = some (UInt256.ofNat y) →
    exec_reverts (...)             -- whatever "revert happened" looks like in EVMYulLean

end Solady.Proofs.Interp
