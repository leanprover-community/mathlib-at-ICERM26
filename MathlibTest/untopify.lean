module
import Mathlib.Tactic.Untopify

open scoped ENNReal NNReal

example (a b : ℝ≥0∞) (h : a = b) : a - b = b - a := by
  untopify
  lia

example (a b : ℝ≥0∞) (h : a ≤ b) : a - b < b + 1 := by
  untopify
  sorry

example (a b : ℝ≥0∞) (h : a ≤ b) : a - 2 * b ≤ b + 1 := by
  untopify
  sorry

example (a b c : ℝ≥0∞) (hab : a ≥ b) (hbc : b ≥ c) : a ≥ c := by
  untopify
  sorry

example (a b : ℝ≥0∞) (h : a = b) : a - b = b - a := by
  -- to test if the tactic works with inaccessible names
  let a : ℤ := 42
  let b : ℤ := 32
  untopify
  lia
