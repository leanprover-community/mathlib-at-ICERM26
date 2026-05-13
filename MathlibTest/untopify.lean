module
import Mathlib.Tactic -- for the linarith preprocessor for `ℝ≥0`.
import Mathlib.Tactic.Untopify

open scoped ENNReal NNReal

example (a b : ℝ≥0∞) (h : a = b) : a - b = b - a := by untopify


example (a : ℝ≥0) (ha : 0 ≤ a) (ha' : a < 0) : False := by linarith

example (a : ℝ) (ha : 0 < a) (b : ℝ≥0) (hb : 0 < b) (h : a ≤ b) :
    a - b < b + 1 := by
  linarith

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

lemma spec1 (ha : a ≠ 0) : ⊤ * a = ⊤ := by untopify; simp_all -- ugh

lemma spec2 : (⊤ : ENNReal) * 2 = 4 * ⊤ := by untopify

lemma spec3 (n : Nat) : n ≤ (⊤ : ENNReal) := by untopify

lemma spec4 : (⊤ : ENNReal) * 0 = 0 := by untopify; simp -- ugh

lemma spec5 : 0 - (⊤ : ENNReal) ≤ ⊤ := by untopify

lemma spec6 : (0 : ENNReal) ^ 0 = 1 := by untopify; simp -- ugh

lemma spec7 : a ^ 0 = 1 := by simp

lemma spec8 (H : a ≤ b) : a ^ 8 ≤ b ^ 8 := by
  untopify
  all_goals try simp_all
  sorry

lemma spec9 : (0 : ENNReal) ^ 9 = 0 := by untopify; simp

lemma spec10 (H : a ≤ b) : b ^ (- 5 : ℝ) ≤ a ^ (- 5 : ℝ) := by
    untopify
    all_goals try simp_all
    sorry

lemma spec11 : (⊤ : ENNReal) ^ (- 5 : ℝ) = 0 := by untopify; simp

lemma spec12 : a + ⊤ = ⊤ := by simp

lemma spec13 : (⊤ : ENNReal) - ⊤ = 0 := by simp

-- maybe not this one
lemma spec14 : a + b = b + a := by ring

-- Should not require case splitting - finiteness can do it!
lemma spec15 (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a + b < ⊤ := by finiteness

lemma spec16 : a + b - ⊤ = 0 := by simp

lemma spec17 : (⊤ : ENNReal) * 1 = ⊤ := by simp

-- This is probably false
lemma spec18 (H : a ≤ b) (hb : b ≠ 0) : a / b ≤ 1 := sorry

-- This is true I think?
lemma spec19 : ⊤ / (0 : ENNReal) = ⊤ := by simp [ENNReal.div_zero]

lemma spec20 : a / ⊤ = 0 := by simp

lemma spec21 : (⊤ : ENNReal) / ⊤ = 0 := by simp

lemma spec22 (ha : a ≠ 0) : a / 0 = ⊤ := by simp [ENNReal.div_zero, ha]

lemma spec23 (ha : a ≠ ⊤) (hb : b ≠ ⊤) (ha' : a ≠ 0) (hb : b ≠ 0) :
    a / b * b = a := by
  rw [div_mul_cancel_of_invertible]


lemma spec24 : (⊤ : ENNReal)⁻¹ = 0 := by simp

lemma spec25 (ha : a ≠ 0) : a⁻¹ ≠ ⊤ := by simp [ha]

end BasicFunctionalities
