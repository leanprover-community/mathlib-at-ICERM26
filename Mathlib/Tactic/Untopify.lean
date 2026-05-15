/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENNReal.Operations
public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Tactic.UntopifyAttr
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public meta import Mathlib.Tactic.ToAdditive

/-!
# `enat_to_nat`

This file implements the `enat_to_nat` tactic that shifts `ENat`s in the context to `Nat`.

## Implementation details
The implementation follows these steps:
1. Apply the `cases` tactic to each `ENat` variable, producing two goals: one where the variable
   is `⊤`, and one where it is a finite natural number.
2. Simplify arithmetic expressions involving infinities, making (in)equalities either trivial
   or free of infinities. This step uses the `enat_to_nat_top` simp set.
3. Translate the remaining goals from `ENat` to `Nat` using the `enat_to_nat_coe` simp set.

-/

public meta section

open scoped ENNReal NNReal

namespace Mathlib.Tactic.Untopify

attribute [untopify_top .] OfNat.ofNat_ne_zero
attribute [untopify_top =] not_false_eq_true
attribute [untopify_top .]
  ENNReal.coe_ne_top ENNReal.top_ne_coe ENNReal.coe_lt_top top_le_iff le_top
  top_add add_top
  ENNReal.sub_top ENNReal.top_sub_coe ENNReal.mul_top ENNReal.top_mul
  ENNReal.one_ne_top ENNReal.top_ne_one ENNReal.zero_ne_top ENNReal.top_ne_zero
  ENNReal.mul_top ENNReal.top_mul
  ENNReal.inv_top ENNReal.inv_zero ENNReal.div_top ENNReal.top_pow
  tsub_zero zero_tsub add_zero zero_add mul_zero zero_mul ENNReal.zero_div ENNReal.div_zero
  pow_zero zero_pow zpow_zero zero_le le_zero_iff
  ENNReal.top_zpow_def
  ENNReal.top_rpow_def

--@[untopify_top] lemma top_zpow_ofNat {n : ℕ} : ∞ ^ (ofNat(n + 1) : ℤ) = ∞ := by
  --rw [ENNReal.top_zpow_def]
  --cases n <;> simp

--example (a b : ℝ≥0∞) (h : ⊤ = a) : ⊤ = b := by simp_all

--@[untopify_top] lemma top_rpow_ofNat {n : ℕ} : ∞ ^ (ofNat(n + 1) : ℝ) = ∞ := by
  --rw [ENNReal.top_rpow_def]
  --cases n <;> simp

--@[untopify_top] lemma top_zpow_neg {n : ℕ} : ∞ ^ (- ofNat(n + 1) : ℤ) = 0 := by
  --rw [ENNReal.top_zpow_def]
  --cases n <;> simp

--@[untopify_top] lemma top_rpow_neg {n : ℕ} : ∞ ^ (- ofNat(n + 1) : ℝ) = 0 := by
  --rw [ENNReal.top_rpow_def]
  --cases n <;> simp

--@[untopify_top] lemma zero_zpow_ofNat {n : ℕ} : (0 : ℝ≥0∞) ^ (ofNat(n + 1) : ℤ) = 0 := by
  --rw [ENNReal.zero_zpow_def]
  --cases n <;> simp

--@[untopify_top] lemma zero_rpow_ofNat {n : ℕ} : (0 : ℝ≥0∞) ^ (ofNat(n + 1) : ℝ) = 0 := by
  --rw [ENNReal.zero_rpow_def]
  --cases n <;> simp

--@[untopify_top] lemma zero_zpow_neg {n : ℕ} : (0 : ℝ≥0∞) ^ (- ofNat(n + 1) : ℤ) = ∞ := by
  --rw [ENNReal.zero_zpow_def]
  --cases n <;> simp

--@[untopify_top] lemma zero_rpow_neg {n : ℕ} : (0 : ℝ≥0∞) ^ (- ofNat(n + 1) : ℝ) = ∞ := by
  --rw [ENNReal.zero_rpow_def]
  --cases n <;> simp

-- coercion lemmas: ENNReal.coe_rpow_of_ne_zero, ENNReal.coe_rpow_of_nonneg

@[untopify_top .] lemma not_lt_top (x : ℝ≥0∞) :
    ¬(⊤ < x) := by cases x <;> simp

@[untopify_coe .] lemma coe_add (m n : ℝ≥0) :
    (m : ℝ≥0∞) + (n : ℝ≥0∞) = ((m + n : ℝ≥0) : ℝ≥0∞) := by simp

@[untopify_coe .] lemma coe_sub (m n : ℝ≥0) :
    (m : ℝ≥0∞) - (n : ℝ≥0∞) = ((m - n : ℝ≥0) : ℝ≥0∞) := by simp

@[untopify_coe .] lemma coe_mul (m n : ℝ≥0) :
    (m : ℝ≥0∞) * (n : ℝ≥0∞) = ((m * n : ℝ≥0) : ℝ≥0∞) := by simp

@[untopify_coe .] lemma coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ℝ≥0∞) = (OfNat.ofNat n : ℝ≥0) := rfl

@[untopify_coe .] lemma coe_ofScientific (m : ℕ) (b : Bool) (e : ℕ) :
    (OfScientific.ofScientific m b e : ℝ≥0∞) = (OfScientific.ofScientific m b e : ℝ≥0) :=
  rfl

@[untopify_coe .] lemma coe_pow (x : ℝ≥0) (n : ℕ) : (↑x : ℝ≥0∞) ^ n = ↑(x ^ n) := by simp

@[untopify_coe .] lemma coe_zpow {r : ℝ≥0} (hr : 0 < r) (n : ℤ) : (↑r : ℝ≥0∞) ^ n = ↑(r ^ n) :=
  (ENNReal.coe_zpow hr.ne' n).symm

@[untopify_coe .] lemma coe_zpow_of_ne_zero {x : ℝ≥0} (h : 0 < x) (y : ℝ) : (↑x : ℝ≥0∞) ^ y = ↑(x ^ y)
 := (ENNReal.coe_rpow_of_ne_zero h.ne' y).symm

@[untopify_coe .] lemma coe_rpow_of_ne_zero {x : ℝ≥0} (h : 0 < x) (y : ℝ) : (↑x : ℝ≥0∞) ^ y = ↑(x ^ y)
 := (ENNReal.coe_rpow_of_ne_zero h.ne' y).symm

@[untopify_coe .] lemma coe_zero : (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) := rfl

@[untopify_coe .] lemma coe_one : (1 : ℝ≥0∞) = ((1 : ℝ≥0) : ℝ≥0∞) := rfl

@[untopify_coe .] lemma coe_div (a b : ℝ≥0) (hb : 0 < b) : (a / b : ℝ≥0∞) = ↑(a / b) :=
  (ENNReal.coe_div hb.ne').symm

@[untopify_coe .] lemma coe_inv (b : ℝ≥0) (hb : 0 < b) : (b⁻¹ : ℝ≥0∞) = ↑(b⁻¹) :=
  (ENNReal.coe_inv hb.ne').symm

attribute [untopify_coe .] ENNReal.coe_inj ENNReal.coe_le_coe ENNReal.coe_lt_coe

lemma ENNReal.trichotomy_induction {C : ℝ≥0∞ → Prop} (zero : C 0) (infty : C ∞)
    (pos : (x : ℝ≥0) → (hx : 0 < x) → C ↑x) (x : ℝ≥0∞) : C x := by
  refine ENNReal.recTopCoe infty (fun x ↦ ?_) x
  obtain (rfl | hx) := zero_le (a := x) |>.eq_or_lt
  · exact zero
  · exact pos x hx

open Qq Lean Elab Tactic Term Meta in
/-- Finds the first `ENat` in the context and applies the `cases` tactic to it.
Then simplifies expressions involving `⊤` using the `enat_to_nat_top` simp set. -/
elab "cases_first_with_top" : tactic => focus do
  let g ← getMainGoal
  g.withContext do
    let ctx ← getLCtx
    let decl? ← ctx.findDeclM? fun decl => do
      if ← (isExprDefEq (← inferType decl.toExpr) q(ENNReal)) then
        return Option.some decl
      else
        return Option.none
    let some decl := decl? | throwError "No ENNReals"
    let isInaccessible := ctx.inaccessibleFVars.find? (·.fvarId == decl.fvarId) |>.isSome
    if isInaccessible then
      let name : Name := `untopify_aux
      setGoals [← g.rename decl.fvarId name]
      let x := mkIdent name
      evalTactic (← `(tactic| cases $x:ident using ENNReal.trichotomy_induction))
    else
      let x := mkIdent decl.userName
      let hx ← mkFreshIdent .missing
      evalTactic
        (← `(tactic| cases $x:ident using ENNReal.trichotomy_induction with
            | zero => _
            | infty => _
            | pos $x:ident $hx:ident => _))
    evalTactic (← `(tactic| all_goals try grind only [$(mkIdent `untopify_top):term]))


/-- `enat_to_nat` shifts all `ENat`s in the context to `Nat`, rewriting propositions about them.
A typical use case is `enat_to_nat; lia`. -/
macro "untopify" : tactic =>
  `(tactic| focus (
    cases_first_with_top
    --(try grind only [$(Lean.mkIdent `untopify_top):term, $(Lean.mkIdent `untopify_coe):term])
  )
)

end Mathlib.Tactic.Untopify
