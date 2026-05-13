/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module

public import PiecewiseC1.Adapter

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

namespace Path

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every piecewise-linear path is piecewise-`C¹`. -/
lemma IsPiecewiseLinear.isPiecewiseC1 {x y : E} {γ : Path x y}
    (hγ : γ.IsPiecewiseLinear) : γ.IsPiecewiseC1 := by
  rcases (show ∃ (N : ℕ) (hpos : 0 < N) (p : Fin (N + 1) → E) (h0 : p 0 = x)
    (hN : p (Fin.last N) = y), γ = piecewiseLinearInterpolation hpos p h0 hN from hγ) with
    ⟨N, hpos, p, h0, hN, rfl⟩
  refine isPiecewiseC1_of_subdivision (n := N) hpos (fun i => (i : ℝ) / N)
    ?_ ?_ ?_ ?_ ?_
  · simp
  · change (N : ℝ) / (N : ℝ) = 1
    exact div_self (by exact_mod_cast hpos.ne')
  · intro i
    constructor
    · positivity
    · exact div_le_one_of_le₀ (by exact_mod_cast Nat.lt_succ_iff.mp i.isLt) (by positivity)
  · intro i
    change ((i.castSucc : Fin (N + 1)) : ℝ) / (N : ℝ) <
      ((i.succ : Fin (N + 1)) : ℝ) / (N : ℝ)
    simp [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    gcongr
    norm_num
  · intro i
    let φ : ℝ → E := fun t =>
      AffineMap.lineMap (p i.castSucc) (p i.succ) ((N : ℝ) * t - i)
    have hφ : ContDiff ℝ 1 φ := by
      dsimp [φ, AffineMap.lineMap]
      fun_prop
    refine hφ.contDiffOn.congr ?_
    intro t ht
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      have hleft0 : (0 : ℝ) ≤ (fun j : Fin (N + 1) => (j : ℝ) / N) i.castSucc := by
        positivity
      have hright1 : (fun j : Fin (N + 1) => (j : ℝ) / N) i.succ ≤ 1 := by
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
        change ((i.succ : Fin (N + 1)) : ℝ) / (N : ℝ) ≤ 1
        rw [div_le_one₀ hNpos]
        exact_mod_cast Nat.succ_le_iff.mpr i.isLt
      exact ⟨hleft0.trans ht.1, ht.2.trans hright1⟩
    have htI : (⟨t, ht01⟩ : I) ∈
        Set.Icc (equalGrid N i.castSucc) (equalGrid N i.succ) := by
      constructor
      · simpa [equalGrid] using ht.1
      · simpa [equalGrid] using ht.2
    have happly :=
      piecewiseLinearInterpolation_apply_of_mem_Icc hpos p h0 hN i htI
    rw [Path.extend_apply _ ht01]
    exact happly


end Path

