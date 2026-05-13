/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module

public import PiecewiseLinear.Basic

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

namespace Path

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Every path in a real normed vector space can be uniformly approximated by piecewise linear
paths with the same endpoints. -/

theorem exists_isPiecewiseLinear_forall_dist_lt {x y : E} (γ : Path x y) :
    ∀ ε > 0, ∃ γ' : Path x y, γ'.IsPiecewiseLinear ∧ ∀ t : I, dist (γ t) (γ' t) < ε := by
  intro ε hε
  let ε' : ℝ := ε / 2
  have hε' : 0 < ε' := by positivity
  have hγuc : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  rcases Metric.uniformContinuous_iff.mp hγuc ε' hε' with ⟨δ, hδpos, hδ⟩

  rcases exists_nat_one_div_lt hδpos with ⟨n, hn⟩
  let N : ℕ := n + 1
  have hpos : 0 < N := Nat.succ_pos n
  have hstep : (1 : ℝ) / N < δ := by
    simpa [N, Nat.cast_add, Nat.cast_one] using hn

  let grid : Fin (N + 1) → I := fun i => ⟨i / N, by
    simp
    constructor
    · positivity
    · exact div_le_one_of_le₀ (by exact_mod_cast Nat.lt_succ_iff.mp i.isLt) (by positivity)⟩

  let pts : Fin (N + 1) → E := fun i => γ (grid i)

  have h0 : pts 0 = x := by
    simp [pts, grid]

  have hN : pts ⟨N, by omega⟩ = y := by
    simp [pts, grid]

  let γ' : Path x y := piecewiseLinearInterpolation hpos pts h0 (by simpa using hN)

  refine ⟨γ', ?_, ?_⟩
  · exact piecewiseLinearInterpolation_isPiecewiseLinear pts hpos h0 (by simpa using hN)
  · intro t
    have : ∃ i : Fin N, grid i.castSucc ≤ t ∧ t ≤ grid (i.succ) := by
      by_cases ht : t = 1
      · use Fin.last (N - 1)
        simp [grid]
        rw [ht]
        constructor
        · exact unitInterval.le_one'
        · apply le_of_eq
          grind
      · have ht : (t : ℝ) < 1 := by
          exact lt_of_le_of_ne t.2.2 (by
            intro h
            exact ht (Subtype.ext h))
        use ⟨Nat.floor ((N : ℝ) * (t : ℝ)), ?_⟩
        simp [grid]
        constructor
        · have hfloor : (Nat.floor ((N : ℝ) * (t : ℝ)) : ℝ) ≤ (N : ℝ) * (t : ℝ) := by
            apply Nat.floor_le
            apply mul_nonneg
            · exact Nat.cast_nonneg' N
            · exact t.2.1
          change ((Nat.floor ((N : ℝ) * (t : ℝ)) : ℝ) / (N : ℝ) ≤ (t : ℝ))
          apply (div_le_iff₀ (by exact_mod_cast hpos)).mpr
          simpa [mul_comm] using hfloor
        · have hfloor_lt :
              (N : ℝ) * (t : ℝ) <
                (Nat.floor ((N : ℝ) * (t : ℝ)) : ℝ) + 1 :=
            Nat.lt_floor_add_one ((N : ℝ) * (t : ℝ))
          change (t : ℝ) ≤
            ((Nat.floor ((N : ℝ) * (t : ℝ)) : ℝ) + 1) / (N : ℝ)
          apply le_of_lt
          rw [lt_div_iff₀ (by exact_mod_cast hpos)]
          simpa [mul_comm] using hfloor_lt
        · have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
          have hmul : (N : ℝ) * (t : ℝ) < (N : ℝ) := by
            simpa using mul_lt_mul_of_pos_left ht hNpos
          exact (Nat.floor_lt (mul_nonneg (le_of_lt hNpos) t.2.1)).2 hmul
    obtain ⟨i, hleft, hright⟩ := this
    have hdist_left : dist (grid i.castSucc) t < δ := by
      have hdist_le : dist (grid i.castSucc) t ≤ (1 : ℝ) / N := by
        rw [dist_comm, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
        · change (t : ℝ) - ((i : ℝ) / (N : ℝ)) ≤ (1 : ℝ) / (N : ℝ)
          have hright' : (t : ℝ) ≤ ((i : ℝ) + 1) / (N : ℝ) := by
            simpa [grid, Nat.cast_add, Nat.cast_one] using hright
          have hright'' : (t : ℝ) ≤ (i : ℝ) / (N : ℝ) + (1 : ℝ) / (N : ℝ) := by
            calc
              (t : ℝ) ≤ ((i : ℝ) + 1) / (N : ℝ) := hright'
              _ = (i : ℝ) / (N : ℝ) + (1 : ℝ) / (N : ℝ) := by ring
          linarith
        · exact sub_nonneg.mpr (by simpa [grid] using hleft)
      exact lt_of_le_of_lt hdist_le hstep
    have hdist_right : dist (grid i.castSucc) (grid i.succ) < δ := by
      have hdist_eq : dist (grid i.castSucc) (grid i.succ) = (1 : ℝ) / N := by
        rw [dist_comm, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
        · simp [grid, Nat.cast_add, Nat.cast_one, sub_eq_add_neg, add_div]
        · simp [grid, Nat.cast_add, Nat.cast_one]
          gcongr
          norm_num
      simpa [hdist_eq] using hstep

    have hγ_left : dist (γ t) (γ (grid i.castSucc)) < ε' := by
      exact Metric.mem_ball'.mp (hδ hdist_left)

    have hγ_right : dist (γ (grid i.castSucc)) (γ (grid i.succ)) < ε' := hδ hdist_right

    have hγγ' (i : Fin (N + 1)) : γ' (grid i) = γ (grid i) := by
      change (piecewiseLinearInterpolation hpos pts h0 (by simpa using hN)) (grid i) =
        γ (grid i)
      rw [piecewiseLinearInterpolation_apply_equalGrid]

    have hγ'_right : dist (γ' (grid i.castSucc)) (γ' t) < ε' := by
      have htmem : t ∈ Icc (equalGrid N i.castSucc) (equalGrid N i.succ) := by
        simpa [grid, equalGrid] using (show t ∈ Icc (grid i.castSucc) (grid i.succ) from
          ⟨hleft, hright⟩)
      have hγ't :
          γ' t =
            AffineMap.lineMap (pts i.castSucc) (pts i.succ) ((N : ℝ) * (t : ℝ) - i) := by
        change (piecewiseLinearInterpolation hpos pts h0 (by simpa using hN)) t =
          AffineMap.lineMap (pts i.castSucc) (pts i.succ) ((N : ℝ) * (t : ℝ) - i)
        exact piecewiseLinearInterpolation_apply_of_mem_Icc hpos pts h0 (by simpa using hN) i htmem
      have hγ'_left : γ' (grid i.castSucc) = pts i.castSucc := by
        rw [hγγ']
      have hpts_right : dist (pts i.castSucc) (pts i.succ) < ε' := by
        simpa [pts] using hγ_right
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
      have hc_nonneg : 0 ≤ (N : ℝ) * (t : ℝ) - (i : ℝ) := by
        have hleft' : ((i : ℝ) / (N : ℝ)) ≤ (t : ℝ) := by
          simpa [grid] using hleft
        have hleft'' : (i : ℝ) ≤ (N : ℝ) * (t : ℝ) :=
          (div_le_iff₀' hNpos).1 hleft'
        linarith
      have hc_le_one : (N : ℝ) * (t : ℝ) - (i : ℝ) ≤ 1 := by
        have hright' : (t : ℝ) ≤ ((i : ℝ) + 1) / (N : ℝ) := by
          simpa [grid, Nat.cast_add, Nat.cast_one] using hright
        have hright'' : (N : ℝ) * (t : ℝ) ≤ (i : ℝ) + 1 :=
          (le_div_iff₀' hNpos).1 hright'
        linarith
      have hnorm_le_one : ‖(N : ℝ) * (t : ℝ) - (i : ℝ)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
        exact hc_le_one
      rw [hγ'_left, hγ't, dist_left_lineMap]
      exact lt_of_le_of_lt
        (mul_le_of_le_one_left dist_nonneg hnorm_le_one) hpts_right

    calc
      dist (γ t) (γ' t) ≤
          dist (γ t) (γ (grid i.castSucc)) + dist (γ (grid i.castSucc)) (γ' t) := by
        exact dist_triangle _ _ _
      _ = dist (γ t) (γ (grid i.castSucc)) +
          dist (γ' (grid i.castSucc)) (γ' t) := by
        rw [dist_comm, hγγ']
      _ < ε' + ε' := by
        exact add_lt_add_of_lt_of_lt hγ_left hγ'_right
      _ = ε := by simp [ε']

theorem exists_isPiecewiseLinear_homotopy {x y : E} (γ γ' : Path x y) (H : Homotopy γ γ') :
  let hmap := ContinuousMap.curry H.toContinuousMap
  ∀ ε > 0, ∃ hmap' : Path (hmap 0) (hmap 1),
    hmap'.IsPiecewiseLinear ∧ ∀ t : I, dist (hmap t) (hmap' t) < ε := by
  intro hmap
  let hpath : Path (hmap 0) (hmap 1) :=
    { toFun := fun t => hmap t
      continuous_toFun := hmap.continuous
      source' := rfl
      target' := rfl }
  simpa using exists_isPiecewiseLinear_forall_dist_lt (γ := hpath)


end Path

