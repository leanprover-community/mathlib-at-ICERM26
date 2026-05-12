/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module


public import PiecewiseLinear.PiecewiseC1_Adapter

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

namespace Path

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_uniform_grid_homotopy_slices_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (γ γ' : Path x y) (H : Homotopy γ γ') :
    let hmap := ContinuousMap.curry H.toContinuousMap
    ∀ ε > 0, ∃ N : ℕ, ∃ _hN : 0 < N,
      ∀ i : Fin N,
        dist
          (hmap (equalGrid N i.castSucc))
          (hmap (equalGrid N i.succ)) < ε
          := by
  intro hmap ε hε

  -- `hmap : C(I, C(I,E))` is uniformly continuous.
  have hhmap_uc : UniformContinuous hmap :=
    CompactSpace.uniformContinuous_of_continuous hmap.continuous
  rcases Metric.uniformContinuous_iff.mp hhmap_uc ε hε with ⟨δ, hδ, huc⟩

  -- Pick `N` with mesh size `1 / N < δ`.
  rcases exists_nat_one_div_lt hδ with ⟨n, hn⟩
  let N : ℕ := n + 1
  have hN : 0 < N := Nat.succ_pos n
  have hstep : (1 : ℝ) / N < δ := by
    simpa [N, Nat.cast_add, Nat.cast_one] using hn

  refine ⟨N, hN, ?_⟩
  intro i

  apply huc
  have hdist_eq :
      dist (equalGrid N i.castSucc) (equalGrid N i.succ) = (1 : ℝ) / N := by
    rw [dist_comm, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
    · simp [Nat.cast_add, Nat.cast_one, sub_eq_add_neg, add_div]
    · simp [Nat.cast_add, Nat.cast_one]
      gcongr
      norm_num
  simpa [hdist_eq] using hstep

theorem exists_piecewiseC1_chain_of_homotopy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} {γ γ' : Path x y}
    {U : Set E} (hU_open : IsOpen U)
    (hγC1 : γ.IsPiecewiseC1) (hγ'C1 : γ'.IsPiecewiseC1)
    (hγU : γ.MapsInto U) (hγ'U : γ'.MapsInto U)
    (H : Homotopy γ γ') (hHU : ∀ s t : I, H (s, t) ∈ U) :
    ∀ ε > 0, ∃ N : ℕ, ∃ _hN : 0 < N, ∃ Γ : Fin (N + 1) → Path x y,
      Γ 0 = γ ∧
      Γ (Fin.last N) = γ' ∧
      (∀ i : Fin (N + 1), (Γ i).IsPiecewiseC1) ∧
      (∀ i : Fin (N + 1), (Γ i).MapsInto U) ∧
      ∀ i : Fin N, ∀ t : I, dist (Γ i.castSucc t) (Γ i.succ t) < ε := by
  intro ε hε
  let K : Set E := Set.range H.toContinuousMap
  have hK_compact : IsCompact K := isCompact_range H.toContinuousMap.continuous
  have hK_subset : K ⊆ U := by
    rintro z ⟨st, rfl⟩
    exact hHU st.1 st.2
  rcases hK_compact.exists_thickening_subset_open hU_open hK_subset with
    ⟨δ, hδ, hδU⟩
  let η : ℝ := min (ε / 4) (δ / 2)
  have hη : 0 < η := by positivity
  have hη_lt_δ : η < δ := by
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ)
  have hη_le_eps4 : η ≤ ε / 4 := min_le_left _ _
  rcases exists_uniform_grid_homotopy_slices_close γ γ' H η hη with
    ⟨N, hN, hgrid⟩
  let approx : Fin (N + 1) → Path x y := fun i =>
    Classical.choose (exists_isPiecewiseLinear_forall_dist_lt (H.eval (equalGrid N i)) η hη)
  have approx_PL : ∀ i : Fin (N + 1), (approx i).IsPiecewiseLinear := by
    intro i
    exact (Classical.choose_spec
      (exists_isPiecewiseLinear_forall_dist_lt (H.eval (equalGrid N i)) η hη)).1
  have approx_close : ∀ i : Fin (N + 1), ∀ t : I,
      dist ((H.eval (equalGrid N i)) t) (approx i t) < η := by
    intro i t
    exact (Classical.choose_spec
      (exists_isPiecewiseLinear_forall_dist_lt (H.eval (equalGrid N i)) η hη)).2 t
  let Γ : Fin (N + 1) → Path x y := fun i =>
    if i = 0 then γ else if i = Fin.last N then γ' else approx i
  refine ⟨N, hN, Γ, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Γ]
  · have hlast_ne_zero : (Fin.last N : Fin (N + 1)) ≠ 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
      omega
    simp [Γ, hlast_ne_zero]
  · intro i
    by_cases hi0 : i = 0
    · subst i
      simpa [Γ] using hγC1
    · by_cases hiN : i = Fin.last N
      · subst i
        have hlast_ne_zero : (Fin.last N : Fin (N + 1)) ≠ 0 := by
          intro h
          have hval := congrArg Fin.val h
          simp at hval
          omega
        simp [Γ, hlast_ne_zero]
        exact hγ'C1
      · simpa [Γ, hi0, hiN] using (approx_PL i).isPiecewiseC1
  · intro j
    change ∀ t : I, Γ j t ∈ U
    intro t
    by_cases hj0 : j = 0
    · subst j
      exact (show ∀ t : I, γ t ∈ U from hγU) t
    · by_cases hjN : j = Fin.last N
      · subst j
        have hlast_ne_zero : (Fin.last N : Fin (N + 1)) ≠ 0 := by
          intro h
          have hval := congrArg Fin.val h
          simp at hval
          omega
        simpa [Γ, hlast_ne_zero] using ((show ∀ t : I, γ' t ∈ U from hγ'U) t)
      · apply hδU
        rw [Metric.mem_thickening_iff]
        refine ⟨(H.eval (equalGrid N j)) t, ?_, ?_⟩
        · exact ⟨(equalGrid N j, t), rfl⟩
        · have hclose := approx_close j t
          simpa [Γ, hj0, hjN, dist_comm] using lt_of_lt_of_le hclose hη_lt_δ.le
  · intro i t
    have hΓ_close : ∀ j : Fin (N + 1), ∀ t : I,
        dist (Γ j t) ((H.eval (equalGrid N j)) t) < η := by
      intro j t
      by_cases hj0 : j = 0
      · subst j
        have hgrid0 : equalGrid N (0 : Fin (N + 1)) = 0 := by
          ext
          simp
        simp [Γ, hgrid0, η, hη]
      · by_cases hjN : j = Fin.last N
        · subst j
          have hlast_ne_zero : (Fin.last N : Fin (N + 1)) ≠ 0 := by
            intro h
            have hval := congrArg Fin.val h
            simp at hval
            omega
          have hgridN : equalGrid N (Fin.last N) = 1 := by
            ext
            change (N : ℝ) / (N : ℝ) = 1
            exact div_self (by exact_mod_cast hN.ne')
          have hzero : dist (γ' t) ((H.eval 1) t) < η := by
            simpa using hη
          simpa [Γ, hlast_ne_zero, hgridN] using hzero
        · have hΓj : Γ j = approx j := by
            simp [Γ, hj0, hjN]
          rw [hΓj, dist_comm]
          exact approx_close j t
    have hslice : dist ((H.eval (equalGrid N i.castSucc)) t)
        ((H.eval (equalGrid N i.succ)) t) < η := by
      change dist ((H.curry (equalGrid N i.castSucc)) t)
        ((H.curry (equalGrid N i.succ)) t) < η
      exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist t) (hgrid i)
    have hleft := hΓ_close i.castSucc t
    have hright := hΓ_close i.succ t
    have hright' : dist ((H.eval (equalGrid N i.succ)) t) (Γ i.succ t) < η := by
      rw [dist_comm]
      exact hright
    calc
      dist (Γ i.castSucc t) (Γ i.succ t)
          ≤ dist (Γ i.castSucc t) ((H.eval (equalGrid N i.castSucc)) t) +
            dist ((H.eval (equalGrid N i.castSucc)) t) (Γ i.succ t) := by
              exact dist_triangle _ _ _
      _ ≤ dist (Γ i.castSucc t) ((H.eval (equalGrid N i.castSucc)) t) +
            (dist ((H.eval (equalGrid N i.castSucc)) t)
              ((H.eval (equalGrid N i.succ)) t) +
              dist ((H.eval (equalGrid N i.succ)) t) (Γ i.succ t)) := by
              gcongr
              exact dist_triangle _ _ _
      _ < η + (η + η) := by
              exact add_lt_add hleft (add_lt_add hslice hright')
      _ ≤ ε := by
              linarith

/-- A homotopy can be replaced by a homotopy through piecewise-`C¹` paths, staying uniformly
close to the original homotopy and hence inside the same open set.

The construction is the one suggested by the finite chain theorem above: sample the original
homotopy finely in the homotopy parameter, approximate the sampled slices by piecewise-linear
paths, keep the endpoints fixed as `γ` and `γ'`, and concatenate the straight-line homotopies
between consecutive sampled paths. The mesh is chosen small enough that every straight segment
stays inside the thickening of the image of `H`. -/
theorem exists_piecewiseC1_homotopy_of_homotopy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} {γ γ' : Path x y}
    {U : Set E} (hU_open : IsOpen U)
    (hγC1 : γ.IsPiecewiseC1) (hγ'C1 : γ'.IsPiecewiseC1)
    (H : Homotopy γ γ') (hHU : ∀ s t : I, H (s, t) ∈ U) :
    ∀ ε > 0, ∃ Γ : Homotopy γ γ',
      (∀ s : I, (Γ.eval s).IsPiecewiseC1) ∧
      (∀ s : I, (Γ.eval s).MapsInto U) ∧
      ∀ s t : I, dist (Γ.eval s t) (H.eval s t) < ε := by
  intro ε hε
  let K : Set E := Set.range H.toContinuousMap
  have hK_compact : IsCompact K := isCompact_range H.toContinuousMap.continuous
  have hK_subset : K ⊆ U := by
    rintro z ⟨st, rfl⟩
    exact hHU st.1 st.2
  rcases hK_compact.exists_thickening_subset_open hU_open hK_subset with
    ⟨δ, hδ, hδU⟩
  let η : ℝ := min (ε / 8) (δ / 4)
  have hη : 0 < η := by positivity
  have hη_lt_δ : η < δ := by
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hη_le_eps8 : η ≤ ε / 8 := min_le_left _ _
  have hη_le_δ4 : η ≤ δ / 4 := min_le_right _ _

  -- Work with a mesh fine enough in the homotopy variable, uniformly over the whole cell.
  let ρ : ℝ := min η (ε / 8)
  have hρ : 0 < ρ := by positivity
  let hmap := ContinuousMap.curry H.toContinuousMap
  have hhmap_uc : UniformContinuous hmap :=
    CompactSpace.uniformContinuous_of_continuous hmap.continuous
  rcases Metric.uniformContinuous_iff.mp hhmap_uc ρ hρ with ⟨θ, hθ, huc⟩
  rcases exists_nat_one_div_lt hθ with ⟨n, hn⟩
  let N : ℕ := n + 1
  have hN : 0 < N := Nat.succ_pos n
  have hmesh : (1 : ℝ) / N < θ := by
    simpa [N, Nat.cast_add, Nat.cast_one] using hn
  have hgrid_any : ∀ i : Fin N, ∀ s : I,
      s ∈ Icc (equalGrid N i.castSucc) (equalGrid N i.succ) →
        dist (hmap (equalGrid N i.castSucc)) (hmap s) < ρ := by
    intro i s hs
    apply huc
    have hdist_le : dist (equalGrid N i.castSucc) s ≤ (1 : ℝ) / N := by
      rw [dist_comm, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
      · have hright : (s : ℝ) ≤ (equalGrid N i.succ : ℝ) := hs.2
        have hstep :
            (equalGrid N i.succ : ℝ) - (equalGrid N i.castSucc : ℝ) = (1 : ℝ) / N := by
          simp [Nat.cast_add, Nat.cast_one, sub_eq_add_neg, add_div]
        linarith
      · exact sub_nonneg.mpr hs.1
    exact lt_of_le_of_lt hdist_le hmesh

  let approx : Fin (N + 1) → Path x y := fun i =>
    Classical.choose (exists_isPiecewiseLinear_forall_dist_lt (H.eval (equalGrid N i)) η hη)
  have approx_PL : ∀ i : Fin (N + 1), (approx i).IsPiecewiseLinear := by
    intro i
    exact (Classical.choose_spec
      (exists_isPiecewiseLinear_forall_dist_lt (H.eval (equalGrid N i)) η hη)).1
  have approx_close : ∀ i : Fin (N + 1), ∀ t : I,
      dist ((H.eval (equalGrid N i)) t) (approx i t) < η := by
    intro i t
    exact (Classical.choose_spec
      (exists_isPiecewiseLinear_forall_dist_lt (H.eval (equalGrid N i)) η hη)).2 t

  -- Keep the two endpoint slices exactly equal to the original endpoint paths.
  let slices : Fin (N + 1) → Path x y := fun i =>
    if i = 0 then γ else if i = Fin.last N then γ' else approx i
  have hslices_zero : slices 0 = γ := by
    simp [slices]
  have hslices_last : slices (Fin.last N) = γ' := by
    have hlast_ne_zero : (Fin.last N : Fin (N + 1)) ≠ 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
    simp [slices, hlast_ne_zero]
  have hslices_C1 : ∀ i : Fin (N + 1), (slices i).IsPiecewiseC1 := by
    intro i
    by_cases hi0 : i = 0
    · subst i
      simpa [slices] using hγC1
    · by_cases hiN : i = Fin.last N
      · subst i
        have hlast_ne_zero : (Fin.last N : Fin (N + 1)) ≠ 0 := by
          intro h
          have hval := congrArg Fin.val h
          simp at hval
        simpa [slices, hlast_ne_zero] using hγ'C1
      · simpa [slices, hi0, hiN] using (approx_PL i).isPiecewiseC1
  have hslices_close : ∀ j : Fin (N + 1), ∀ t : I,
      dist (slices j t) ((H.eval (equalGrid N j)) t) < η := by
    intro j t
    by_cases hj0 : j = 0
    · subst j
      have hgrid0 : equalGrid N (0 : Fin (N + 1)) = 0 := by
        ext
        simp
      simp [slices, hgrid0, η, hη]
    · by_cases hjN : j = Fin.last N
      · subst j
        have hlast_ne_zero : (Fin.last N : Fin (N + 1)) ≠ 0 := by
          intro h
          have hval := congrArg Fin.val h
          simp at hval
        have hgridN : equalGrid N (Fin.last N) = 1 := by
          ext
          change (N : ℝ) / (N : ℝ) = 1
          exact div_self (by exact_mod_cast hN.ne')
        have hzero : dist (γ' t) ((H.eval 1) t) < η := by
          simpa using hη
        simpa [slices, hlast_ne_zero, hgridN] using hzero
      · have hslice : slices j = approx j := by
          simp [slices, hj0, hjN]
        rw [hslice, dist_comm]
        exact approx_close j t

  let p : Fin (N + 1) → C(I, E) := fun i => (slices i).toContinuousMap
  have hp0 : p 0 = γ.toContinuousMap := by
    ext t
    simp [p, hslices_zero]
  have hpN : p (Fin.last N) = γ'.toContinuousMap := by
    ext t
    simp [p, hslices_last]
  let Φ : Path γ.toContinuousMap γ'.toContinuousMap :=
    piecewiseLinearInterpolation hN p hp0 hpN

  have hcover_cell : ∀ s : I, ∃ i : Fin N,
      s ∈ Icc (equalGrid N i.castSucc) (equalGrid N i.succ) := by
    intro s
    by_cases hs : s = 1
    · let i : Fin N := ⟨N - 1, by omega⟩
      refine ⟨i, ?_⟩
      constructor
      · rw [hs]
        exact unitInterval.le_one'
      · rw [hs]
        change (1 : ℝ) ≤ (equalGrid N i.succ : ℝ)
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        have hnum : (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) := by
          exact_mod_cast Nat.sub_add_cancel hN
        simp [i, hnum]
    · have hslt : (s : ℝ) < 1 := by
        exact lt_of_le_of_ne s.2.2 (by
          intro h
          exact hs (Subtype.ext h))
      refine ⟨⟨Nat.floor ((N : ℝ) * (s : ℝ)), ?_⟩, ?_⟩
      · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        have hmul : (N : ℝ) * (s : ℝ) < (N : ℝ) := by
          simpa using mul_lt_mul_of_pos_left hslt hNpos
        exact (Nat.floor_lt (mul_nonneg (le_of_lt hNpos) s.2.1)).2 hmul
      · constructor
        · have hfloor : (Nat.floor ((N : ℝ) * (s : ℝ)) : ℝ) ≤
              (N : ℝ) * (s : ℝ) := by
            apply Nat.floor_le
            apply mul_nonneg
            · exact Nat.cast_nonneg' N
            · exact s.2.1
          change ((Nat.floor ((N : ℝ) * (s : ℝ)) : ℝ) / (N : ℝ) ≤ (s : ℝ))
          apply (div_le_iff₀ (by exact_mod_cast hN)).mpr
          simpa [mul_comm] using hfloor
        · have hfloor_lt :
              (N : ℝ) * (s : ℝ) <
                (Nat.floor ((N : ℝ) * (s : ℝ)) : ℝ) + 1 :=
            Nat.lt_floor_add_one ((N : ℝ) * (s : ℝ))
          change (s : ℝ) ≤
            (((⟨Nat.floor ((N : ℝ) * (s : ℝ)), by
              have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
              have hmul : (N : ℝ) * (s : ℝ) < (N : ℝ) := by
                simpa using mul_lt_mul_of_pos_left hslt hNpos
              exact (Nat.floor_lt (mul_nonneg (le_of_lt hNpos) s.2.1)).2 hmul⟩ : Fin N).succ :
                Fin (N + 1)) : ℝ) / (N : ℝ)
          simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
          apply le_of_lt
          rw [lt_div_iff₀ (by exact_mod_cast hN)]
          simpa [mul_comm] using hfloor_lt

  have hΦ_endpoints : ∀ s : I, Φ s 0 = x ∧ Φ s 1 = y := by
    intro s
    rcases hcover_cell s with ⟨i, hs⟩
    have hΦs :=
      piecewiseLinearInterpolation_apply_of_mem_Icc hN p hp0 hpN i hs
    constructor
    · have h := congrFun (congrArg ContinuousMap.toFun hΦs) 0
      simpa [p, AffineMap.lineMap_apply] using h
    · have h := congrFun (congrArg ContinuousMap.toFun hΦs) 1
      simpa [p, AffineMap.lineMap_apply] using h

  let Γ : Homotopy γ γ' :=
    { toFun := fun st => Φ st.1 st.2
      continuous_toFun := by
        exact ContinuousMap.continuous_uncurry_of_continuous Φ.toContinuousMap
      map_zero_left := by
        intro t
        simp only [Path.source, coe_toContinuousMap, Φ]
      map_one_left := by
        intro t
        simp only [Path.target, coe_toContinuousMap, Φ]
      prop' := by
        intro s f hf
        rcases hf with rfl | rfl
        · simpa using (hΦ_endpoints s).1
        · simpa using (hΦ_endpoints s).2 }

  refine ⟨Γ, ?_, ?_, ?_⟩
  · intro s
    rcases hcover_cell s with ⟨i, hs⟩
    let c : I := ⟨(N : ℝ) * (s : ℝ) - i, by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      constructor
      · have hleft' : ((i : ℝ) / (N : ℝ)) ≤ (s : ℝ) := by
          simpa [equalGrid] using hs.1
        have hleft'' : (i : ℝ) ≤ (N : ℝ) * (s : ℝ) :=
          (div_le_iff₀' hNpos).1 hleft'
        linarith
      · have hright' : (s : ℝ) ≤ ((i : ℝ) + 1) / (N : ℝ) := by
          simpa [equalGrid, Nat.cast_add, Nat.cast_one] using hs.2
        have hright'' : (N : ℝ) * (s : ℝ) ≤ (i : ℝ) + 1 :=
          (le_div_iff₀' hNpos).1 hright'
        linarith⟩
    have hΦs :=
      piecewiseLinearInterpolation_apply_of_mem_Icc hN p hp0 hpN i hs
    have heval :
        Γ.eval s = (linearHomotopy (slices i.castSucc) (slices i.succ)).eval c := by
      ext t
      have h := congrFun (congrArg ContinuousMap.toFun hΦs) t
      simpa [Γ, Homotopy.eval, linearHomotopy, p, c] using h
    simpa [heval] using
      (IsPiecewiseC1.lineMap (hslices_C1 i.castSucc) (hslices_C1 i.succ) c)
  · intro s
    change ∀ t : I, Γ.eval s t ∈ U
    intro t
    rcases hcover_cell s with ⟨i, hs⟩
    let c : I := ⟨(N : ℝ) * (s : ℝ) - i, by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      constructor
      · have hleft' : ((i : ℝ) / (N : ℝ)) ≤ (s : ℝ) := by
          simpa [equalGrid] using hs.1
        have hleft'' : (i : ℝ) ≤ (N : ℝ) * (s : ℝ) :=
          (div_le_iff₀' hNpos).1 hleft'
        linarith
      · have hright' : (s : ℝ) ≤ ((i : ℝ) + 1) / (N : ℝ) := by
          simpa [equalGrid, Nat.cast_add, Nat.cast_one] using hs.2
        have hright'' : (N : ℝ) * (s : ℝ) ≤ (i : ℝ) + 1 :=
          (le_div_iff₀' hNpos).1 hright'
        linarith⟩
    have hΦs :=
      piecewiseLinearInterpolation_apply_of_mem_Icc hN p hp0 hpN i hs
    have hΓst : Γ.eval s t =
        AffineMap.lineMap (slices i.castSucc t) (slices i.succ t) (c : ℝ) := by
      change Φ s t =
        AffineMap.lineMap (slices i.castSucc t) (slices i.succ t) (c : ℝ)
      have h := congrFun (congrArg ContinuousMap.toFun hΦs) t
      simpa [p, c] using h
    let center : E := (H.eval (equalGrid N i.castSucc)) t
    have hleft_mem : slices i.castSucc t ∈ Metric.ball center δ := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le (hslices_close i.castSucc t) hη_lt_δ.le
    have hright_grid : dist ((H.eval (equalGrid N i.castSucc)) t)
        ((H.eval (equalGrid N i.succ)) t) < ρ := by
      have hright_mem_cell :
          equalGrid N i.succ ∈ Icc (equalGrid N i.castSucc) (equalGrid N i.succ) :=
        ⟨hs.1.trans hs.2, le_rfl⟩
      change dist ((hmap (equalGrid N i.castSucc)) t)
        ((hmap (equalGrid N i.succ)) t) < ρ
      exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist t)
        (hgrid_any i (equalGrid N i.succ) hright_mem_cell)
    have hright_mem : slices i.succ t ∈ Metric.ball center δ := by
      rw [Metric.mem_ball]
      have hgrid_right_comm :
          dist ((H.eval (equalGrid N i.succ)) t) center < ρ := by
        simpa [center, dist_comm] using hright_grid
      calc
        dist (slices i.succ t) center
            ≤ dist (slices i.succ t) ((H.eval (equalGrid N i.succ)) t) +
              dist ((H.eval (equalGrid N i.succ)) t) center := dist_triangle _ _ _
        _ < η + ρ := add_lt_add (hslices_close i.succ t) hgrid_right_comm
        _ < δ := by
          have hρ_le_η : ρ ≤ η := min_le_left _ _
          linarith
    have hline_mem : AffineMap.lineMap (slices i.castSucc t) (slices i.succ t) (c : ℝ) ∈
        Metric.ball center δ := by
      exact (convex_ball center δ).segment_subset hleft_mem hright_mem
        (by
          rw [segment_eq_image_lineMap]
          exact ⟨(c : ℝ), c.2, rfl⟩)
    apply hδU
    rw [Metric.mem_thickening_iff]
    refine ⟨center, ?_, ?_⟩
    · exact ⟨(equalGrid N i.castSucc, t), rfl⟩
    · rw [hΓst]
      simpa [Metric.mem_ball] using hline_mem
  · intro s t
    rcases hcover_cell s with ⟨i, hs⟩
    let c : I := ⟨(N : ℝ) * (s : ℝ) - i, by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      constructor
      · have hleft' : ((i : ℝ) / (N : ℝ)) ≤ (s : ℝ) := by
          simpa [equalGrid] using hs.1
        have hleft'' : (i : ℝ) ≤ (N : ℝ) * (s : ℝ) :=
          (div_le_iff₀' hNpos).1 hleft'
        linarith
      · have hright' : (s : ℝ) ≤ ((i : ℝ) + 1) / (N : ℝ) := by
          simpa [equalGrid, Nat.cast_add, Nat.cast_one] using hs.2
        have hright'' : (N : ℝ) * (s : ℝ) ≤ (i : ℝ) + 1 :=
          (le_div_iff₀' hNpos).1 hright'
        linarith⟩
    have hΦs :=
      piecewiseLinearInterpolation_apply_of_mem_Icc hN p hp0 hpN i hs
    have hΓst : Γ.eval s t =
        AffineMap.lineMap (slices i.castSucc t) (slices i.succ t) (c : ℝ) := by
      change Φ s t =
        AffineMap.lineMap (slices i.castSucc t) (slices i.succ t) (c : ℝ)
      have h := congrFun (congrArg ContinuousMap.toFun hΦs) t
      simpa [p, c] using h
    let center : E := (H.eval (equalGrid N i.castSucc)) t
    have hleft_mem : slices i.castSucc t ∈ Metric.ball center (ε / 2) := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le (hslices_close i.castSucc t) (by linarith)
    have hright_grid : dist ((H.eval (equalGrid N i.castSucc)) t)
        ((H.eval (equalGrid N i.succ)) t) < ρ := by
      have hright_mem_cell :
          equalGrid N i.succ ∈ Icc (equalGrid N i.castSucc) (equalGrid N i.succ) :=
        ⟨hs.1.trans hs.2, le_rfl⟩
      change dist ((hmap (equalGrid N i.castSucc)) t)
        ((hmap (equalGrid N i.succ)) t) < ρ
      exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist t)
        (hgrid_any i (equalGrid N i.succ) hright_mem_cell)
    have hright_mem : slices i.succ t ∈ Metric.ball center (ε / 2) := by
      rw [Metric.mem_ball]
      have hgrid_right_comm :
          dist ((H.eval (equalGrid N i.succ)) t) center < ρ := by
        simpa [center, dist_comm] using hright_grid
      calc
        dist (slices i.succ t) center
            ≤ dist (slices i.succ t) ((H.eval (equalGrid N i.succ)) t) +
              dist ((H.eval (equalGrid N i.succ)) t) center := dist_triangle _ _ _
        _ < η + ρ := add_lt_add (hslices_close i.succ t) hgrid_right_comm
        _ < ε / 2 := by
          have hρ_le_eps8 : ρ ≤ ε / 8 := min_le_right _ _
          linarith
    have hline_mem : AffineMap.lineMap (slices i.castSucc t) (slices i.succ t) (c : ℝ) ∈
        Metric.ball center (ε / 2) := by
      exact (convex_ball center (ε / 2)).segment_subset hleft_mem hright_mem
        (by
          rw [segment_eq_image_lineMap]
          exact ⟨(c : ℝ), c.2, rfl⟩)
    have hline_close :
        dist (Γ.eval s t) center < ε / 2 := by
      rw [hΓst]
      simpa [Metric.mem_ball] using hline_mem
    have hHs_close : dist center (H.eval s t) < ρ := by
      change dist ((hmap (equalGrid N i.castSucc)) t) ((hmap s) t) < ρ
      exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist t) (hgrid_any i s hs)
    calc
      dist (Γ.eval s t) (H.eval s t)
          ≤ dist (Γ.eval s t) center + dist center (H.eval s t) := dist_triangle _ _ _
      _ < ε / 2 + ρ := add_lt_add hline_close hHs_close
      _ < ε := by
        have hρ_le_eps8 : ρ ≤ ε / 8 := min_le_right _ _
        linarith



end Path
