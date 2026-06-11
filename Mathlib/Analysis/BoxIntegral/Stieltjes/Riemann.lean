/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.Basic

-- Need to migrate to Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.LinearMapPiProd

/-! # Compatibility of Riemann integration and the interval integral

-/

@[expose] public section

/-- Move to Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic -/
theorem ContinuousLinearMap.intervalIntegrable_comp {𝕜 : Type*} {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} {μ : MeasureTheory.Measure ℝ} {f : ℝ → E}
    [RCLike 𝕜] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
    [CompleteSpace F] [CompleteSpace E] (L : E →L[𝕜] F) (hf : IntervalIntegrable f μ a b) :
    IntervalIntegrable (L ∘ f) μ a b :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

@[simp]
theorem Finset.sum_indicator_singleton_eq_self {ι : Type*} {M : Type*} [Fintype ι] [AddCommMonoid M]
    (F : ι → M) : ∑ i, Set.indicator {i} F = F := by
  ext j
  simp only [Finset.sum_apply, Set.indicator]
  rw [Finset.sum_eq_single j] <;> grind

namespace BoxIntegral

open intervalIntegral MeasureTheory Finset

variable {a b : ℝ} {f : ℝ → ℝ} {L : ℝ}

theorem HasRiemannIntegral.oscillation_tendsto_zero (hab : a < b) (hf : RiemannIntegrable a b f)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ π : Prepartition (Ioc a b), π.IsPartition → π.mesh_size ≤ δ →
     ∑ J ∈ π.boxes, ((J.upper₁ - J.lower₁) * (sSup (f '' J.Icc₁) - sInf (f '' J.Icc₁))) < ε := by
  obtain ⟨ δ, hδpos, hδ ⟩ := (hasRiemannIntegral_iff_lim_sum hab).mp hf.hasRiemannIntegral (ε/5)
    (by positivity)
  refine ⟨ δ, hδpos, fun π hπ hmesh ↦ ?_ ⟩
  let ε' := ε / (5 * (b - a))
  have hε' : 0 < ε' := by positivity
  have hup (J : Box (Fin 1)) : ∃ x ∈ Set.Icc a b, J ∈ π.boxes →
    x ∈ J.Icc₁ ∧ f x > sSup (f '' J.Icc₁) - ε' := by
    by_cases hJ : J ∈ π.boxes
    · have := exists_lt_of_lt_csSup (by simp [J.lower_le_upper₁])
        (sub_lt_self (sSup (f '' J.Icc₁)) hε')
      simp only [Box.Icc₁_def, Set.mem_image, Set.mem_Icc, exists_exists_and_eq_and] at this
      obtain ⟨ x, hx ⟩ := this
      replace hJ := π.le_of_mem hJ
      simp only [Box.le_iff₁, hab, Ioc.lower₁, Ioc.upper₁,
        Set.mem_Icc, Prepartition.mem_boxes, Box.Icc₁_def, gt_iff_lt] at hJ ⊢
      refine ⟨ x, by grind, fun _ ↦ hx ⟩
    use a; simp [hab.le, hJ]
  have hdown (J : Box (Fin 1)) : ∃ x ∈ Set.Icc a b, J ∈ π.boxes →
    x ∈ J.Icc₁ ∧ f x < sInf (f '' J.Icc₁) + ε' := by
    by_cases hJ : J ∈ π.boxes
    · have := exists_lt_of_csInf_lt (by simp [J.lower_le_upper₁])
        (lt_add_of_pos_right (sInf (f '' J.Icc₁)) hε')
      simp only [Box.Icc₁_def, Set.mem_image, Set.mem_Icc, exists_exists_and_eq_and] at this
      obtain ⟨ x, hx ⟩ := this
      replace hJ := π.le_of_mem hJ
      simp only [Box.le_iff₁, hab, Ioc.lower₁, Ioc.upper₁,
        Set.mem_Icc, Prepartition.mem_boxes, Box.Icc₁_def] at hJ ⊢
      refine ⟨ x, by grind, fun _ ↦ hx ⟩
    use a; simp [hab.le, hJ]
  choose xup hxup using hup
  choose xdown hxdown using hdown
  let π' : Bool → TaggedPrepartition (Ioc a b) := fun p ↦ {
    boxes := π.boxes
    le_of_mem' := π.le_of_mem'
    pairwiseDisjoint := π.pairwiseDisjoint
    tag J := if p then (fun _ ↦ xup J) else (fun _ ↦ xdown J)
    tag_mem_Icc J := by
      split_ifs
      · simpa [hab] using (hxup J).1
      · simpa [hab] using (hxdown J).1
    }
  have hπ' (p : Bool) : dist (∑ J ∈ π.boxes, (J.upper₁ - J.lower₁) • f ((π' p).tag J 0))
    (riemannIntegral a b f) < ε / 5 := by
    convert hδ (π' p) ?_ hπ hmesh
    intro J hJ; simp only [π']
    split_ifs
    · simpa [hab] using ((hxup J).2 hJ).1
    simpa [hab] using ((hxdown J).2 hJ).1
  calc
    _ ≤ ∑ J ∈ π.boxes, (J.upper₁ - J.lower₁) * (f ((π' true).tag J 0) - f ((π' false).tag J 0)
      + 2 * ε') := by
      refine sum_le_sum fun J hJ ↦ ?_
      have := J.lower_le_upper₁
      simp only [Box.Icc₁_def, ↓reduceIte, Bool.false_eq_true, ge_iff_le, π']; gcongr
      grw [((hxup J).2 hJ).2, ((hxdown J).2 hJ).2, Box.Icc₁_def ]
      apply le_of_eq; ring
    _ = ∑ J ∈ π.boxes, (J.upper₁ - J.lower₁) * f ((π' true).tag J 0) -
        ∑ J ∈ π.boxes, (J.upper₁ - J.lower₁) * f ((π' false).tag J 0)
        + 2 * ε / 5 := by
      simp only [Fin.isValue, mul_sub, mul_add, sum_add_distrib, sum_sub_distrib,
        ← sum_mul, add_right_inj]
      have := hπ.sum_of_sub id
      simp only [id_eq, sum_sub_distrib, hab, Ioc.upper₁, Ioc.lower₁] at this
      grind
    _ ≤ dist (∑ J ∈ π.boxes, (J.upper₁ - J.lower₁) • f ((π' true).tag J 0))
        (riemannIntegral a b f)
        + dist (∑ J ∈ π.boxes, (J.upper₁ - J.lower₁) • f ((π' false).tag J 0))
        (riemannIntegral a b f)
        + 2 * ε / 5 := by
      grw [←dist_triangle_right, Real.dist_eq, ←le_abs_self]; simp
    _ < _ := by
      have hhen (p : Bool) : (π' p).IsHenstock := by
        simp only [π']; split_ifs
        · intro J hJ; simpa [hab] using ((hxup J).2 hJ).1
        intro J hJ; simpa [hab] using ((hxdown J).2 hJ).1
      grw [hδ (π' _) (hhen _) hπ hmesh, hδ (π' _) (hhen _) hπ hmesh]
      linarith

private theorem RiemannIntegrable.intervalIntegrable_scalar (hf : RiemannIntegrable a b f) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  obtain ⟨ M, hM ⟩ := Bornology.IsBounded.exists_norm_le hf.bounded
  apply IntegrableOn.of_bound (by simp) _ M
  · apply ae_restrict_of_forall_mem (by measurability)
    intro x hx; apply hM; simp only [Set.mem_image]; exact ⟨ x, Set.uIoc_subset_uIcc hx, rfl ⟩
  sorry

private theorem HasRiemannIntegral.intervalIntegral_eq_scalar (hf : HasRiemannIntegral a b f L) :
    ∫ x in a..b, f x = L := by
  sorry

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]
variable {B : E →L[ℝ] F →L[ℝ] G} {a b : ℝ} {f : ℝ → E} {g : ℝ → F} {L : G} {M : E}

/-- The Euclidean space-valued Riemann integral agrees with the interval integral. -/
private theorem riemannIntegral_eq_intervalIntegral_euclidean {ι : Type*} [Fintype ι]
    {f : ℝ → ι → ℝ} (hf : RiemannIntegrable a b f) : IntervalIntegrable f volume a b ∧
    riemannIntegral a b f = ∫ x in a..b, f x := by
  set L := riemannIntegral a b f
  have hriem (i : ι) : HasRiemannIntegral a b (fun x ↦ f x i) (L i) := by
    convert hf.hasRiemannIntegral.map (φ := .proj i)
  have hinteg (i : ι) : IntervalIntegrable (fun x ↦ f x i) volume a b :=
    (hriem i).riemannIntegrable.intervalIntegrable_scalar
  have hinteg' (i : ι) : IntervalIntegrable (fun x ↦ Set.indicator {i} (f x)) volume a b := by
    convert (ContinuousLinearMap.toSpanSingleton ℝ
      (Set.indicator {i} (fun _ ↦ (1:ℝ)))).intervalIntegrable_comp (hinteg i) with _ x
    ext; simp [Set.indicator]; aesop
  have hint_eq (i : ι) : ∫ x in a..b, Set.indicator {i} (f x) = Set.indicator {i} L := by
    convert (ContinuousLinearMap.toSpanSingleton ℝ
      (Set.indicator {i} (fun _ ↦ (1:ℝ)))).intervalIntegral_comp_comm (hinteg i) with x
    · ext; simp [Set.indicator]; aesop
    ext; simp [Set.indicator, (hriem i).intervalIntegral_eq_scalar]; aesop
  constructor
  · have : IntervalIntegrable (∑ i, (fun x ↦ Set.indicator {i} (f x))) volume a b :=
      .sum _ (by aesop)
    convert this; ext1 j; simp
  calc
    _ = ∑ i, Set.indicator {i} L := by simp
    _ = ∑ i ∈ .univ, ∫ x in a..b, Set.indicator {i} (f x) := by simp_rw [hint_eq]
    _ = _ := by rw [←intervalIntegral.integral_finsetSum (fun i _ ↦ hinteg' i)]; simp

/-- The finite-dimensional Riemann integral agrees with the interval integral. -/
theorem riemannIntegral_eq_intervalIntegral [hfin : Module.Finite ℝ E]
    (hf : RiemannIntegrable a b f) : IntervalIntegrable f volume a b ∧
    riemannIntegral a b f = ∫ x in a..b, f x := by
  let e := (Module.Basis.ofVectorSpace ℝ E).repr.trans (Finsupp.linearEquivFunOnFinite _ _ _)
  let T := e.toContinuousLinearMap
  let S := e.symm.toContinuousLinearMap
  have hriem := riemannIntegral_eq_intervalIntegral_euclidean (hf.map (φ := T))
  constructor
  · convert S.intervalIntegrable_comp hriem.1; aesop
  have hriem' := congrArg S (riemannIntegral_map (φ := T) hf)
  rw [hriem.2, ←S.intervalIntegral_comp_comm hriem.1] at hriem'
  simpa [S, T] using hriem'.symm

theorem HasRiemannIntegral.intervalIntegral_eq [hfin : Module.Finite ℝ E]
    (hf : HasRiemannIntegral a b f M) : ∫ x in a..b, f x = M := by
  rw [←(riemannIntegral_eq_intervalIntegral hf.riemannIntegrable).2, hf.riemannIntegral_eq]

/-- Theorem A.3 (b).  If g′ is continuous on [a, b] and if in addition f is
Riemann integrable, then ∫ₐᵇ f(x) dg(x) = ∫ₐᵇ f(x) g′(x) dx. Interval integral version. -/
theorem HasStieltjesIntegral.of_contDiffOn [Module.Finite ℝ G] (hg : ContDiffOn ℝ 1 g (.uIcc a b))
    (hf : RiemannIntegrable a b f) :
    HasStieltjesIntegral a b B f g (∫ x in a..b, B (f x) (deriv g x)) := by
  wlog hab : a ≤ b
  · rw [symm_iff, ←integral_symm]
    exact this ((Set.uIcc_comm a b) ▸ hg) hf.symm (by order)
  obtain rfl | hab := hab.eq_or_lt
  · simp
  set g' := derivWithin g (.uIcc a b)
  have : ∫ x in a..b, B (f x) (deriv g x) = ∫ x in a..b, B (f x) (g' x) := by
    apply intervalIntegral.integral_congr_uIoo; intro x hx
    simp only [g'] at hx ⊢
    rw [derivWithin_of_mem_nhds]
    simpa [← mem_interior_iff_mem_nhds, Set.uIcc_of_lt, Set.uIoo_of_lt, hab] using hx
  rw [this]
  convert of_contDiffOn_eq_riemann hg hf
  simp only [Set.uIcc_of_lt hab] at hg
  have hriem : RiemannIntegrable a b (fun x ↦ B (f x) (g' x)) :=
    hf.mul_continuous (by simpa [g', Set.uIcc_of_lt hab] using
      hg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (le_refl _))
  rw [(riemannIntegral_eq_intervalIntegral hriem).2]

end BoxIntegral
