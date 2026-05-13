/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module

public import ComplexCurveIntegral.PathAdditivity

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

/-!
This file contains preliminary local versions of Cauchy integral theorem used in the proof of
the homotopy-invariance statement. The key input is exactness on balls; the later global theorem
uses these local identities together with a piecewise-`C¹` replacement of a topological homotopy.
-/
/--
Local Cauchy theorem on a ball: two piecewise-`C¹` paths in the same ball with the same endpoints
have the same integral for a holomorphic integrand.
-/
theorem eq_complexCurveIntegral_of_mapsInto_ball_piecewiseC1
    {a b c : ℂ} {r : ℝ} {f : ℂ → ℂ} {γ γ' : Path a b}
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (hγU : γ.MapsInto (Metric.ball c r))
    (hγ'U : γ'.MapsInto (Metric.ball c r))
    (hγC1 : γ.IsPiecewiseC1)
    (hγ'C1 : γ'.IsPiecewiseC1) :
    complexCurveIntegral f γ' = complexCurveIntegral f γ := by
  have hγU_extend : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ Metric.ball c r := by
    intro t ht
    simpa [Path.extend_apply γ ht] using hγU ⟨t, ht⟩
  have hγ'U_extend : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ'.extend t ∈ Metric.ball c r := by
    intro t ht
    simpa [Path.extend_apply γ' ht] using hγ'U ⟨t, ht⟩

  rcases hf.isExactOn_ball with ⟨F, hF⟩
  have hfU : ContinuousOn f (Metric.ball c r) := hf.continuousOn
  have hF_real : ∀ z ∈ Metric.ball c r,
      HasFDerivAt F ((fdzForm f z).restrictScalars ℝ) z := by
    intro z hz
    convert (hF z hz).hasFDerivAt.restrictScalars ℝ using 1
    · ext v
      simp [fdzForm, mul_comm]
    · exact IsScalarTower.complexToReal
    · exact IsScalarTower.complexToReal
  have hγ_int :
      IntervalIntegrable (complexCurveIntegrand f γ) volume 0 1 :=
    hγC1.intervalIntegrable_complexCurveIntegrand hγU_extend hfU
  have hγ'_int :
      IntervalIntegrable (complexCurveIntegrand f γ') volume 0 1 :=
    hγ'C1.intervalIntegrable_complexCurveIntegrand hγ'U_extend hfU
  have hγ_eq :
      complexCurveIntegral f γ = F b - F a :=
    complexCurveIntegral_eq_sub_of_hasPrimitiveOn_piecewiseC1
      hγC1 hγU_extend hF_real hγ_int
  have hγ'_eq :
      complexCurveIntegral f γ' = F b - F a :=
    complexCurveIntegral_eq_sub_of_hasPrimitiveOn_piecewiseC1
      hγ'C1 hγ'U_extend hF_real hγ'_int
  exact hγ'_eq.trans hγ_eq.symm

/-- Local ladder lemma for a path and a uniformly close perturbation.

This is the finite-subdivision argument described below:
choose a partition fine enough that adjacent points of `γ` are close compared with the
thickening radius, form the small quadrilaterals with vertical sides between `γ` and `γ'`,
apply `eq_complexCurveIntegral_of_mapsInto_ball_piecewiseC1` inside the ball centered at the
left endpoint of each cell, and telescope the segment contributions. -/
lemma complexCurveIntegral_eq_of_uniformClose_piecewiseC1_of_thickening
    {a b : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ γ' : Path a b}
    (hf : DifferentiableOn ℂ f U)
    (hγC1 : γ.IsPiecewiseC1)
    (hγ'C1 : γ'.IsPiecewiseC1)
    {ε : ℝ} (hεpos : 0 < ε)
    (hεU : Metric.thickening ε (Set.range γ) ⊆ U)
    (hclose : γ.UniformClose γ' (ε / 4)) :
    complexCurveIntegral f γ' = complexCurveIntegral f γ := by
  have hγ_uc : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  rcases Metric.uniformContinuous_iff.mp hγ_uc (ε / 4) (by positivity) with ⟨δ, hδ, huc⟩
  rcases exists_nat_one_div_lt hδ with ⟨n, hn⟩
  let N : ℕ := n + 1
  have hN : 0 < N := Nat.succ_pos n
  let grid : Fin (N + 1) → I := Path.equalGrid N
  have hmesh : (1 : ℝ) / N < δ := by
    simpa [N, Nat.cast_add, Nat.cast_one] using hn

  have hcell_close : ∀ i : Fin N,
      dist (γ (grid i.castSucc)) (γ (grid i.succ)) < ε / 4 := by
    intro i
    apply huc
    have hdist_eq :
        dist (grid i.castSucc) (grid i.succ) = (1 : ℝ) / N := by
      rw [dist_comm, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
      · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        simp [grid, Nat.cast_add, Nat.cast_one, sub_eq_add_neg, div_eq_mul_inv]
        field_simp [ne_of_gt hNpos]
        ring
      · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        rw [sub_nonneg]
        dsimp [grid, Path.equalGrid]
        change ((i.val : ℝ) / (N : ℝ)) ≤ ((i.val + 1 : ℕ) : ℝ) / (N : ℝ)
        gcongr
        exact Nat.le_succ _
    simpa [hdist_eq] using hmesh

  have hgrid_le : ∀ i : Fin N, grid i.castSucc ≤ grid i.succ := by
    intro i
    change (grid i.castSucc : ℝ) ≤ (grid i.succ : ℝ)
    dsimp [grid, Path.equalGrid]
    gcongr
    exact Nat.le_succ _

  have hgrid_dist_lt : ∀ i : Fin N, ∀ u : I,
      u ∈ Set.Icc (grid i.castSucc) (grid i.succ) →
        dist (grid i.castSucc) u < δ := by
    intro i u hu
    have hdist_le : dist (grid i.castSucc) u ≤ (1 : ℝ) / N := by
      rw [dist_comm, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
      · have hstep :
            (grid i.succ : ℝ) - (grid i.castSucc : ℝ) = (1 : ℝ) / N := by
          dsimp [grid, Path.equalGrid]
          change ((i.val + 1 : ℕ) : ℝ) / (N : ℝ) - (i.val : ℝ) / (N : ℝ) =
            (1 : ℝ) / N
          have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
          field_simp [ne_of_gt hNpos]
          norm_num [Nat.cast_add, Nat.cast_one]
        calc
          (u : ℝ) - (grid i.castSucc : ℝ)
              ≤ (grid i.succ : ℝ) - (grid i.castSucc : ℝ) := by
                have hu2 : (u : ℝ) ≤ (grid i.succ : ℝ) := hu.2
                exact sub_le_sub_right hu2 _
          _ = (1 : ℝ) / N := hstep
      · exact sub_nonneg.mpr hu.1
    exact lt_of_le_of_lt hdist_le hmesh

  have hγ_mem_ball : ∀ i : Fin N, ∀ u : I,
      u ∈ Set.Icc (grid i.castSucc) (grid i.succ) →
        γ u ∈ Metric.ball (γ (grid i.castSucc)) ε := by
    intro i u hu
    rw [Metric.mem_ball]
    exact lt_trans (huc (by simpa [dist_comm] using hgrid_dist_lt i u hu)) (by linarith)

  have hγ'_mem_ball : ∀ i : Fin N, ∀ u : I,
      u ∈ Set.Icc (grid i.castSucc) (grid i.succ) →
        γ' u ∈ Metric.ball (γ (grid i.castSucc)) ε := by
    intro i u hu
    rw [Metric.mem_ball]
    calc
      dist (γ' u) (γ (grid i.castSucc))
          ≤ dist (γ' u) (γ u) + dist (γ u) (γ (grid i.castSucc)) := dist_triangle _ _ _
      _ < ε / 4 + ε / 4 := by
        exact add_lt_add (by simpa [dist_comm] using hclose u)
          (by simpa [dist_comm] using huc (hgrid_dist_lt i u hu))
      _ < ε := by linarith

  have hsegment_mem_ball : ∀ i : Fin N, ∀ u : I, ∀ p q : ℂ,
      p ∈ Metric.ball (γ (grid i.castSucc)) ε →
      q ∈ Metric.ball (γ (grid i.castSucc)) ε →
        Path.segment p q u ∈ Metric.ball (γ (grid i.castSucc)) ε := by
    intro i u p q hp hq
    exact (convex_ball (γ (grid i.castSucc)) ε).segment_subset hp hq
      (by
        rw [← Path.range_segment]
        exact ⟨u, rfl⟩)

  -- The local quadrilateral identity in the ball centered at the left endpoint of the cell.
  have hcell :
      ∀ i : Fin N,
        let c := γ (grid i.castSucc)
        let top : Path c (γ' (grid i.succ)) :=
          (γ.subpath (grid i.castSucc) (grid i.succ)).trans
            (Path.segment (γ (grid i.succ)) (γ' (grid i.succ)))
        let bottom : Path c (γ' (grid i.succ)) :=
          (Path.segment (γ (grid i.castSucc)) (γ' (grid i.castSucc))).trans
            (γ'.subpath (grid i.castSucc) (grid i.succ))
        complexCurveIntegral f bottom = complexCurveIntegral f top := by
    intro i
    dsimp
    refine eq_complexCurveIntegral_of_mapsInto_ball_piecewiseC1
      (c := γ (grid i.castSucc)) (r := ε) ?_ ?_ ?_ ?_ ?_
    · exact hf.mono (by
        intro z hz
        apply hεU
        rw [Metric.mem_thickening_iff]
        exact ⟨γ (grid i.castSucc), ⟨grid i.castSucc, rfl⟩, hz⟩)
    · -- the top side followed by the right vertical side lies in this ball
      intro t
      rw [Path.trans_apply]
      split_ifs with ht
      · apply hγ_mem_ball
        constructor
        · exact Icc.le_convexCombo (hgrid_le i) _
        · exact Icc.convexCombo_le (hgrid_le i) _
      · apply hsegment_mem_ball
        · exact hγ_mem_ball i (grid i.succ) ⟨hgrid_le i, le_rfl⟩
        · exact hγ'_mem_ball i (grid i.succ) ⟨hgrid_le i, le_rfl⟩
    · -- the left vertical side followed by the bottom side lies in this ball
      intro t
      rw [Path.trans_apply]
      split_ifs with ht
      · apply hsegment_mem_ball
        · exact Metric.mem_ball_self hεpos
        · exact hγ'_mem_ball i (grid i.castSucc) ⟨le_rfl, hgrid_le i⟩
      · apply hγ'_mem_ball
        constructor
        · exact Icc.le_convexCombo (hgrid_le i) _
        · exact Icc.convexCombo_le (hgrid_le i) _
    · -- concatenation of the `γ`-subpath with a segment is piecewise-`C¹`
      exact (hγC1.subpath (grid i.castSucc) (grid i.succ)).trans
        (Path.segment_isPiecewiseC1 (γ (grid i.succ)) (γ' (grid i.succ)))
    · -- concatenation of a segment with the `γ'`-subpath is piecewise-`C¹`
      exact (Path.segment_isPiecewiseC1 (γ (grid i.castSucc)) (γ' (grid i.castSucc))).trans
        (hγ'C1.subpath (grid i.castSucc) (grid i.succ))

  -- Summing `hcell i` over all cells and using additivity of curve integrals over subpaths
  -- gives cancellation of the vertical sides. The endpoint verticals are constant because
  -- `γ` and `γ'` have the same endpoints.
  let A : Fin N → ℂ := fun i =>
    complexCurveIntegral f (γ.subpath (grid i.castSucc) (grid i.succ))
  let B : Fin N → ℂ := fun i =>
    complexCurveIntegral f (γ'.subpath (grid i.castSucc) (grid i.succ))
  let V : Fin (N + 1) → ℂ := fun j =>
    complexCurveIntegral f (Path.segment (γ (grid j)) (γ' (grid j)))

  have hcell_add : ∀ i : Fin N, V i.castSucc + B i = A i + V i.succ := by
    intro i
    have hc := hcell i
    dsimp [A, B, V] at hc ⊢
    let Ucell : Set ℂ := Metric.ball (γ (grid i.castSucc)) ε
    have hfUcell : ContinuousOn f Ucell := hf.continuousOn.mono (by
      intro z hz
      apply hεU
      rw [Metric.mem_thickening_iff]
      exact ⟨γ (grid i.castSucc), ⟨grid i.castSucc, rfl⟩, hz⟩)
    have hsegL_U : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
        (Path.segment (γ (grid i.castSucc)) (γ' (grid i.castSucc))).extend r ∈ Ucell := by
      intro r hr
      rw [Path.extend_apply _ hr]
      exact hsegment_mem_ball i ⟨r, hr⟩ (γ (grid i.castSucc)) (γ' (grid i.castSucc))
        (Metric.mem_ball_self hεpos)
        (hγ'_mem_ball i (grid i.castSucc) ⟨le_rfl, hgrid_le i⟩)
    have hsegR_U : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
        (Path.segment (γ (grid i.succ)) (γ' (grid i.succ))).extend r ∈ Ucell := by
      intro r hr
      rw [Path.extend_apply _ hr]
      exact hsegment_mem_ball i ⟨r, hr⟩ (γ (grid i.succ)) (γ' (grid i.succ))
        (hγ_mem_ball i (grid i.succ) ⟨hgrid_le i, le_rfl⟩)
        (hγ'_mem_ball i (grid i.succ) ⟨hgrid_le i, le_rfl⟩)
    have hγsub_U : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
        (γ.subpath (grid i.castSucc) (grid i.succ)).extend r ∈ Ucell := by
      intro r hr
      rw [Path.extend_apply _ hr]
      apply hγ_mem_ball
      constructor
      · exact Icc.le_convexCombo (hgrid_le i) _
      · exact Icc.convexCombo_le (hgrid_le i) _
    have hγ'sub_U : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
        (γ'.subpath (grid i.castSucc) (grid i.succ)).extend r ∈ Ucell := by
      intro r hr
      rw [Path.extend_apply _ hr]
      apply hγ'_mem_ball
      constructor
      · exact Icc.le_convexCombo (hgrid_le i) _
      · exact Icc.convexCombo_le (hgrid_le i) _
    rw [complexCurveIntegral_trans_piecewiseC1
          hsegL_U hγ'sub_U hfUcell
          (Path.segment_isPiecewiseC1 (γ (grid i.castSucc)) (γ' (grid i.castSucc)))
          (hγ'C1.subpath (grid i.castSucc) (grid i.succ)),
        complexCurveIntegral_trans_piecewiseC1
          hγsub_U hsegR_U hfUcell
          (hγC1.subpath (grid i.castSucc) (grid i.succ))
          (Path.segment_isPiecewiseC1 (γ (grid i.succ)) (γ' (grid i.succ)))] at hc
    exact hc

  have hsum_cell :
      (∑ i : Fin N, V i.castSucc) + ∑ i : Fin N, B i =
        (∑ i : Fin N, A i) + ∑ i : Fin N, V i.succ := by
    calc
      (∑ i : Fin N, V i.castSucc) + ∑ i : Fin N, B i
          = ∑ i : Fin N, (V i.castSucc + B i) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ i : Fin N, (A i + V i.succ) := by
              exact Finset.sum_congr rfl (fun i _ => hcell_add i)
      _ = (∑ i : Fin N, A i) + ∑ i : Fin N, V i.succ := by
              rw [Finset.sum_add_distrib]

  have hgrid0 : grid 0 = 0 := by
    ext
    simp [grid]
  have hgridN : grid (Fin.last N) = 1 := by
    ext
    change (N : ℝ) / (N : ℝ) = 1
    exact div_self (by exact_mod_cast hN.ne')
  have hV0 : V 0 = 0 := by
    have hγ0 : γ (grid 0) = a := by simp [hgrid0]
    have hγ'0 : γ' (grid 0) = a := by simp [hgrid0]
    dsimp [V]
    rw [hγ0, hγ'0, Path.segment_same]
    simp [complexCurveIntegral, curveIntegral_refl]
  have hVlast : V (Fin.last N) = 0 := by
    have hγ1 : γ (grid (Fin.last N)) = b := by simp [hgridN]
    have hγ'1 : γ' (grid (Fin.last N)) = b := by simp [hgridN]
    dsimp [V]
    rw [hγ1, hγ'1, Path.segment_same]
    simp [complexCurveIntegral, curveIntegral_refl]

  have hVsum : (∑ i : Fin N, V i.castSucc) = ∑ i : Fin N, V i.succ := by
    have hcast : (∑ i : Fin N, V i.castSucc) = ∑ j : Fin (N + 1), V j := by
      have h := Fin.sum_univ_castSucc V
      rw [hVlast, add_zero] at h
      exact h.symm
    have hsucc : (∑ i : Fin N, V i.succ) = ∑ j : Fin (N + 1), V j := by
      have h := Fin.sum_univ_succ V
      rw [hV0, zero_add] at h
      exact h.symm
    exact hcast.trans hsucc.symm

  have hsum_BA : (∑ i : Fin N, B i) = ∑ i : Fin N, A i := by
    have h := hsum_cell
    rw [hVsum] at h
    have h' :
        (∑ i : Fin N, V i.succ) + (∑ i : Fin N, B i) =
          (∑ i : Fin N, V i.succ) + (∑ i : Fin N, A i) := by
      simpa [add_comm, add_left_comm, add_assoc] using h
    exact add_left_cancel h'

  have hγU_extend : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → γ.extend r ∈ U := by
    intro r hr
    apply hεU
    rw [Metric.mem_thickening_iff]
    exact ⟨γ ⟨r, hr⟩, ⟨⟨r, hr⟩, rfl⟩, by
      rw [Path.extend_apply γ hr]
      simpa using (Metric.mem_ball_self hεpos : γ ⟨r, hr⟩ ∈ Metric.ball (γ ⟨r, hr⟩) ε)⟩
  have hγ'U_extend : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → γ'.extend r ∈ U := by
    intro r hr
    apply hεU
    rw [Metric.mem_thickening_iff]
    refine ⟨γ ⟨r, hr⟩, ⟨⟨r, hr⟩, rfl⟩, ?_⟩
    rw [Path.extend_apply γ' hr]
    exact lt_trans (by simpa [dist_comm] using hclose ⟨r, hr⟩) (by linarith)

  have hA_sum : (∑ i : Fin N, A i) = complexCurveIntegral f γ := by
    simpa [A, grid] using
      complexCurveIntegral_sum_equalGrid_subpath
        (U := U) (f := f) (γ := γ) hγU_extend hf.continuousOn hN hγC1
  have hB_sum : (∑ i : Fin N, B i) = complexCurveIntegral f γ' := by
    simpa [B, grid] using
      complexCurveIntegral_sum_equalGrid_subpath
        (U := U) (f := f) (γ := γ') hγ'U_extend hf.continuousOn hN hγ'C1

  calc
    complexCurveIntegral f γ' = ∑ i : Fin N, B i := hB_sum.symm
    _ = ∑ i : Fin N, A i := hsum_BA
    _ = complexCurveIntegral f γ := hA_sum

/--
Local stability of the complex curve integral: there is a uniform neighborhood of a piecewise-`C¹`
path in which all piecewise-`C¹` perturbations stay in `U` and have the same integral.
-/
theorem exists_eps_eq_complexCurveIntegral_of_uniformClose_piecewiseC1'
    {a b : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ : Path a b}
    (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (hγU : γ.MapsInto U)
    (hγC1 : γ.IsPiecewiseC1) :
    ∃ ε > 0, ∀ {γ' : Path a b},
      γ'.IsPiecewiseC1 →
      γ.UniformClose γ' ε →
        γ'.MapsInto U ∧
        complexCurveIntegral f γ' = complexCurveIntegral f γ := by
  let K : Set ℂ := Set.range γ
  have hK_compact : IsCompact K := isCompact_range γ.continuous
  have hK_subset : K ⊆ U := by
    rintro z ⟨t, rfl⟩
    exact hγU t
  rcases hK_compact.exists_thickening_subset_open hU_open hK_subset with
    ⟨δ, hδpos, hδU⟩
  let ε : ℝ := δ / 4
  have hεpos : 0 < ε := by positivity
  refine ⟨ε, hεpos, ?_⟩
  intro γ' hγ'C1 hclose
  have hγ'U : γ'.MapsInto U := by
    intro t
    apply hδU
    rw [Metric.mem_thickening_iff]
    refine ⟨γ t, ⟨t, rfl⟩, ?_⟩
    exact lt_of_lt_of_le (by simpa [ε, dist_comm] using hclose t) (by linarith)
  refine ⟨hγ'U, ?_⟩
  exact complexCurveIntegral_eq_of_uniformClose_piecewiseC1_of_thickening
    hf hγC1 hγ'C1 hδpos hδU (by
      intro t
      simpa [ε] using hclose t)

