module
import Mathlib.Tactic -- for the linarith preprocessor for `ℝ≥0`.
import Mathlib.Tactic.Untopify

open scoped ENNReal NNReal

example (a b : ℝ≥0∞) (h : a = b) : a - b = b - a := by untopify

example (a b : ℝ≥0∞) (h : a ≤ b) : a - b < b + 1 := by
  untopify
  all_goals try linarith
  -- this goal should have actually been solved by `linarith`, but there's a small missing feature
  sorry

example (a b : ℝ≥0∞) (h : a ≤ b) : a - 2 * b ≤ b + 1 := by
  untopify
  all_goals try linarith
  -- this goal should have actually been solved by `linarith`, but there's a small missing feature
  -- (I think)
  sorry

example (a b c : ℝ≥0∞) (hab : a ≥ b) (hbc : b ≥ c) : a ≥ c := by
  untopify
  all_goals linarith

example (a b : ℝ≥0∞) (h : a = b) : a - b = b - a := by
  -- to test if the tactic works with inaccessible names
  let a : ℤ := 42
  let b : ℤ := 32
  untopify

variable {a b c d e f g : ENNReal}

section BasicFunctionalities

lemma spec1 (ha : a ≠ 0) : ⊤ * a = ⊤ := by untopify

lemma spec2 : (⊤ : ENNReal) * 2 = 4 * ⊤ := by untopify

lemma spec3 (n : Nat) : n ≤ (⊤ : ENNReal) := by untopify

lemma spec4 : (⊤ : ENNReal) * 0 = 0 := by untopify

lemma spec5 : 0 - (⊤ : ENNReal) ≤ ⊤ := by untopify

lemma spec6 : (0 : ENNReal) ^ 0 = 1 := by untopify

lemma spec7 : a ^ 0 = 1 := by simp

lemma spec8 (H : a ≤ b) : a ^ 8 ≤ b ^ 8 := by
  untopify
  gcongr

lemma spec9 : (0 : ENNReal) ^ 9 = 0 := by untopify

lemma spec9half (H : a ≤ b) : b ^ (- 5 : ℤ) ≤ a ^ (- 5 : ℤ) := by
    untopify
    all_goals

      try simp_all
      sorry

lemma spec10 (H : a ≤ b) : b ^ (- 5 : ℝ) ≤ a ^ (- 5 : ℝ) := by
    untopify
    all_goals
      try simp_all
      try sorry

lemma spec11 : (⊤ : ENNReal) ^ (- 5 : ℝ) = 0 := by untopify; simp

lemma spec12 : a + ⊤ = ⊤ := by untopify

lemma spec13 : (⊤ : ENNReal) - ⊤ = 0 := by untopify

-- maybe not this one
lemma spec14 : a + b = b + a := by untopify; rw [add_comm]

-- Should not require case splitting - finiteness can do it!
lemma spec15 (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a + b < ⊤ := by finiteness

lemma spec16 : a + b - ⊤ = 0 := by untopify

lemma spec17 : (⊤ : ENNReal) * 1 = ⊤ := by untopify

lemma spec18 (H : a ≤ b) (hb : b ≠ 0) : a / b ≤ 1 := by
  untopify
  exact (div_le_one₀ ‹_›).mpr H

lemma spec19 : ⊤ / (0 : ENNReal) = ⊤ := by untopify

lemma spec20 : a / ⊤ = 0 := by untopify

lemma spec21 : (⊤ : ENNReal) / ⊤ = 0 := by untopify

lemma spec22 (ha : a ≠ 0) : a / 0 = ⊤ := by untopify

lemma spec23 (ha : a ≠ ⊤) (hb : b ≠ ⊤) (ha' : a ≠ 0) (hb : b ≠ 0) :
    a / b * b = a := by
  untopify
  simp_all [pos_iff_ne_zero]

lemma spec24 : (⊤ : ENNReal)⁻¹ = 0 := by untopify

lemma spec25 (ha : a ≠ 0) : a⁻¹ ≠ ⊤ := by untopify

end BasicFunctionalities
