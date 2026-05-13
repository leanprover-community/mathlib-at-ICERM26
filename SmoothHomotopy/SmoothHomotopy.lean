import Mathlib

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

open scoped unitInterval Topology
open Set Metric ContinuousMap

structure IsC2PathIn' {x y : E} (γ : Path x y) (s : Set E) : Prop where
  range_subset : Set.range γ ⊆ s
  contDiffOn : ContDiffOn ℝ 2 γ.extend (Icc 0 1)

structure IsC2HomotopyIn' {γ₁ γ₂ : C(I, E)} (φ : Homotopy γ₁ γ₂) (s : Set E) : Prop where
  range_subset : Set.range φ ⊆ s
  contDiffOn : ContDiffOn ℝ 2
    (fun p : ℝ × ℝ ↦ φ (projIcc 0 1 zero_le_one p.1, projIcc 0 1 zero_le_one p.2))
    (Icc 0 1 ×ˢ Icc 0 1)

private lemma topological_homotopy {s : Set E} [SimplyConnectedSpace ↥s]
    {x y z : E} (hx : x ∈ s)
    (γ₁ : Path x y) (hγ₁ : Set.range γ₁ ⊆ s)
    (γ₂ : Path x z) (hγ₂ : Set.range γ₂ ⊆ s) :
    ∃ φ₀ : Homotopy (γ₁ : C(I, E)) (γ₂ : C(I, E)), Set.range φ₀ ⊆ s := by
  sorry

private lemma smooth_approx_2d (f : ℝ × ℝ → E) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ × ℝ → E, ContDiff ℝ ⊤ g ∧ ∀ p : ℝ × ℝ, dist (g p) (f p) < ε := by
  sorry

def bilinCorr (g : ℝ → ℝ → E) (b₀ b₁ : ℝ → E) : ℝ → ℝ → E :=
  fun s t ↦ g s t + (1 - s) • (b₀ t - g 0 t) + s • (b₁ t - g 1 t)

omit [CompleteSpace E] in
@[simp] lemma bilinCorr_zero (g : ℝ → ℝ → E) (b₀ b₁ : ℝ → E) (t : ℝ) :
    bilinCorr g b₀ b₁ 0 t = b₀ t := by simp [bilinCorr]

omit [CompleteSpace E] in
@[simp] lemma bilinCorr_one (g : ℝ → ℝ → E) (b₀ b₁ : ℝ → E) (t : ℝ) :
    bilinCorr g b₀ b₁ 1 t = b₁ t := by simp [bilinCorr]

omit [CompleteSpace E] in
lemma bilinCorr_contDiffOn
    {g : ℝ → ℝ → E} (hg : ContDiff ℝ ⊤ (fun p : ℝ × ℝ ↦ g p.1 p.2))
    {b₀ b₁ : ℝ → E} (hb₀ : ContDiffOn ℝ 2 b₀ (Icc 0 1)) (hb₁ : ContDiffOn ℝ 2 b₁ (Icc 0 1)) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ bilinCorr g b₀ b₁ p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) := by
  sorry

theorem exists_smooth_homotopy
    {s : Set E} (hs : IsOpen s) [SimplyConnectedSpace ↥s]
    {x y z : E} (hx : x ∈ s)
    {γ₁ : Path x y} (hγ₁ : IsC2PathIn' γ₁ s)
    {γ₂ : Path x z} (hγ₂ : IsC2PathIn' γ₂ s) :
    ∃ φ : Homotopy (γ₁ : C(I, E)) (γ₂ : C(I, E)), IsC2HomotopyIn' φ s := by
  obtain ⟨φ₀, hφ₀_range⟩ :=
    topological_homotopy hx γ₁ hγ₁.range_subset γ₂ hγ₂.range_subset
  obtain ⟨δ, hδ, hδs⟩ :=
    (isCompact_range φ₀.continuous).exists_thickening_subset_open hs hφ₀_range
  let f₀ : ℝ × ℝ → E := fun p ↦
    φ₀ (projIcc 0 1 zero_le_one p.1, projIcc 0 1 zero_le_one p.2)
  have hf₀_cont : Continuous f₀ :=
    φ₀.continuous.comp (continuous_projIcc.prodMap continuous_projIcc)
  obtain ⟨g', hg'_smooth, hg'_close⟩ :=
    smooth_approx_2d f₀ hf₀_cont (ε := δ / 3) (by linarith)
  let g : ℝ → ℝ → E := fun s t ↦ g' (s, t)
  -- γ₁.extend = f₀(0, ·) and γ₂.extend = f₀(1, ·)
  have hb₀_eq : ∀ t : ℝ, γ₁.extend t = f₀ (0, t) := by
    intro t
    simp only [f₀, Path.extend, Set.IccExtend]
    have h0 : projIcc 0 1 zero_le_one (0 : ℝ) = (0 : I) :=
      Subtype.ext (by simp [coe_projIcc])
    rw [h0]
    exact (φ₀.apply_zero _).symm
  have hb₁_eq : ∀ t : ℝ, γ₂.extend t = f₀ (1, t) := by
    intro t
    simp only [f₀, Path.extend, Set.IccExtend]
    have h1 : projIcc 0 1 zero_le_one (1 : ℝ) = (1 : I) :=
      Subtype.ext (by simp [coe_projIcc])
    rw [h1]
    exact (φ₀.apply_one _).symm
  let h := bilinCorr g γ₁.extend γ₂.extend
  have hh0 : ∀ t : I, h 0 (t : ℝ) = γ₁ t := fun t ↦ by
    show bilinCorr g γ₁.extend γ₂.extend 0 (t : ℝ) = γ₁ t
    simp [γ₁.extend_extends' t]
  have hh1 : ∀ t : I, h 1 (t : ℝ) = γ₂ t := fun t ↦ by
    show bilinCorr g γ₁.extend γ₂.extend 1 (t : ℝ) = γ₂ t
    simp [γ₂.extend_extends' t]
  have hh_c2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ h p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) :=
    bilinCorr_contDiffOn hg'_smooth hγ₁.contDiffOn hγ₂.contDiffOn
  have hh_cont : Continuous (fun p : I × I ↦ h (p.1 : ℝ) (p.2 : ℝ)) :=
    hh_c2.continuousOn.comp_continuous
      (continuous_subtype_val.prodMap continuous_subtype_val)
      (fun ⟨sv, tv⟩ ↦ ⟨sv.2, tv.2⟩)
  let φ : Homotopy (γ₁ : C(I, E)) (γ₂ : C(I, E)) :=
    { toFun         := fun ⟨sv, tv⟩ ↦ h (sv : ℝ) (tv : ℝ)
      continuous_toFun := hh_cont
      map_zero_left := hh0
      map_one_left  := hh1 }
  refine ⟨φ, ?_, ?_⟩
  · -- range(φ) ⊆ s
    rw [range_subset_iff]
    intro ⟨sv, tv⟩
    apply hδs
    rw [mem_thickening_iff]
    refine ⟨φ₀ (sv, tv), mem_range_self _, ?_⟩
    have hsv0 : (0 : ℝ) ≤ (sv : ℝ) := sv.2.1
    have hsv1 : (sv : ℝ) ≤ 1        := sv.2.2
    -- f₀(sv,tv) = φ₀(sv,tv) since projIcc is identity on I
    have hf₀_eq : f₀ ((sv : ℝ), (tv : ℝ)) = φ₀ (sv, tv) := by
      simp only [f₀, projIcc_of_mem zero_le_one sv.2, projIcc_of_mem zero_le_one tv.2,
                 Subtype.eta]
    -- Algebraic decomposition
    have hdecomp : h (sv : ℝ) (tv : ℝ) - φ₀ (sv, tv) =
        (g (sv : ℝ) (tv : ℝ) - f₀ ((sv : ℝ), (tv : ℝ)))
        + (1 - (sv : ℝ)) • (γ₁.extend (tv : ℝ) - g 0 (tv : ℝ))
        + (sv : ℝ)       • (γ₂.extend (tv : ℝ) - g 1 (tv : ℝ)) := by
      rw [show φ₀ (sv, tv) = f₀ ((sv : ℝ), (tv : ℝ)) from hf₀_eq.symm]
      show bilinCorr g γ₁.extend γ₂.extend (sv : ℝ) (tv : ℝ) - f₀ ((sv : ℝ), (tv : ℝ)) = _
      simp only [bilinCorr]; abel
    -- Piece 1: ‖g(sv,tv) - f₀(sv,tv)‖ < δ/3
    have hp1 : ‖g (sv : ℝ) (tv : ℝ) - f₀ ((sv : ℝ), (tv : ℝ))‖ < δ / 3 := by
      rw [← dist_eq_norm]; exact hg'_close ((sv : ℝ), (tv : ℝ))
    -- Piece 2: ‖(1-sv)·(γ₁.extend tv - g(0,tv))‖ < δ/3
    have hp2 : ‖(1 - (sv : ℝ)) • (γ₁.extend (tv : ℝ) - g 0 (tv : ℝ))‖ < δ / 3 := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      have hb : ‖γ₁.extend (tv : ℝ) - g 0 (tv : ℝ)‖ < δ / 3 := by
        rw [hb₀_eq, ← dist_eq_norm, dist_comm]
        exact hg'_close (0, (tv : ℝ))
      nlinarith [norm_nonneg (γ₁.extend (tv : ℝ) - g 0 (tv : ℝ))]
    -- Piece 3: ‖sv·(γ₂.extend tv - g(1,tv))‖ < δ/3
    have hp3 : ‖(sv : ℝ) • (γ₂.extend (tv : ℝ) - g 1 (tv : ℝ))‖ < δ / 3 := by
      rw [norm_smul, Real.norm_of_nonneg hsv0]
      have hb : ‖γ₂.extend (tv : ℝ) - g 1 (tv : ℝ)‖ < δ / 3 := by
        rw [hb₁_eq, ← dist_eq_norm, dist_comm]
        exact hg'_close (1, (tv : ℝ))
      nlinarith [norm_nonneg (γ₂.extend (tv : ℝ) - g 1 (tv : ℝ))]
    calc dist (h (sv : ℝ) (tv : ℝ)) (φ₀ (sv, tv))
        = ‖h (sv : ℝ) (tv : ℝ) - φ₀ (sv, tv)‖ := dist_eq_norm _ _
      _ = ‖(g (sv : ℝ) (tv : ℝ) - f₀ ((sv : ℝ), (tv : ℝ)))
            + (1 - (sv : ℝ)) • (γ₁.extend (tv : ℝ) - g 0 (tv : ℝ))
            + (sv : ℝ) • (γ₂.extend (tv : ℝ) - g 1 (tv : ℝ))‖ := by rw [hdecomp]
      _ ≤ ‖g (sv : ℝ) (tv : ℝ) - f₀ ((sv : ℝ), (tv : ℝ))‖
            + ‖(1 - (sv : ℝ)) • (γ₁.extend (tv : ℝ) - g 0 (tv : ℝ))‖
            + ‖(sv : ℝ) • (γ₂.extend (tv : ℝ) - g 1 (tv : ℝ))‖ := by
          linarith [norm_add_le (g (sv : ℝ) (tv : ℝ) - f₀ ((sv : ℝ), (tv : ℝ)))
                      ((1 - (sv : ℝ)) • (γ₁.extend (tv : ℝ) - g 0 (tv : ℝ))),
                    norm_add_le
                      ((g (sv : ℝ) (tv : ℝ) - f₀ ((sv : ℝ), (tv : ℝ))) +
                       (1 - (sv : ℝ)) • (γ₁.extend (tv : ℝ) - g 0 (tv : ℝ)))
                      ((sv : ℝ) • (γ₂.extend (tv : ℝ) - g 1 (tv : ℝ)))]
      _ < δ / 3 + δ / 3 + δ / 3 := by linarith
      _ = δ := by ring
  · -- ContDiffOn on [0,1]²
    apply hh_c2.congr
    intro ⟨sv, tv⟩ ⟨hsv, htv⟩
    -- φ (projIcc sv, projIcc tv) = h sv tv
    -- since projIcc is identity on [0,1]: ↑(projIcc 0 1 _ sv) = sv
    have hs : (↑(projIcc 0 1 zero_le_one sv) : ℝ) = sv := by
      simp only [coe_projIcc]
      rw [min_eq_right (mem_Icc.mp hsv).2, max_eq_right (mem_Icc.mp hsv).1]
    have ht : (↑(projIcc 0 1 zero_le_one tv) : ℝ) = tv := by
      simp only [coe_projIcc]
      rw [min_eq_right (mem_Icc.mp htv).2, max_eq_right (mem_Icc.mp htv).1]
    show h ↑(projIcc 0 1 zero_le_one sv) ↑(projIcc 0 1 zero_le_one tv) = h sv tv
    rw [hs, ht]

end
