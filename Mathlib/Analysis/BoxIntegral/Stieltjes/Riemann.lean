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

/-- If a real-valued function is squeezed by two sequences of ae measurable functions converging
to each other in measure, then it is ae measurable. -/
theorem aemeasurable_of_le_ge_tendstoMeasure {α : Type*} [MeasurableSpace α]
  {μ : MeasureTheory.Measure α} {g : α → ℝ} {ι : Type*} {l : Filter ι} [l.NeBot]
  [l.IsCountablyGenerated] {f_lo f_hi : ι → α → ℝ} (hflo_mes : ∀ n, AEMeasurable (f_lo n) μ)
  (hg : ∀ᶠ n in l, ∀ᵐ (x : α) ∂μ, f_lo n x ≤ g x ∧ g x ≤ f_hi n x)
  (hconv : MeasureTheory.TendstoInMeasure μ (f_hi - f_lo) l 0) : AEMeasurable g μ := by
    obtain ⟨ n, htop, hconv ⟩ := hconv.exists_seq_tendsto_ae'
    obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp (htop.eventually hg)
    apply AEMeasurable.congr (AEMeasurable.iSup (fun k : Set.Ici N ↦ hflo_mes (n k)))
    simp_rw [←Filter.eventually_imp_distrib_left, ←MeasureTheory.ae_all_iff] at hN
    filter_upwards [hN, hconv] with x hg hconv
    have : Filter.atTop.Tendsto (fun k : Set.Ici N ↦ g x - f_lo (n k) x) (nhds 0) :=
      squeeze_zero (fun k ↦ by linarith [(hg k k.property).1])
        (fun k ↦ by simp; linarith [(hg k k.property).2])
        (hconv.comp (Filter.tendsto_Ici_atTop.mp fun ⦃_⦄ ↦ id))
    replace this := this.const_sub (g x)
    simp only [sub_sub_cancel, sub_zero] at this
    apply iSup_eq_of_forall_le_of_tendsto (by aesop) this

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

private noncomputable def TaggedPrepartition.lower_darboux (f : ℝ → ℝ)
    (π : TaggedPrepartition (Ioc a b)) : ℝ → ℝ :=
  ∑ J ∈ π.boxes, J.toSet₁.indicator (fun _ ↦ sInf (f '' J.Icc₁))

private noncomputable def TaggedPrepartition.upper_darboux (f : ℝ → ℝ)
    (π : TaggedPrepartition (Ioc a b)) : ℝ → ℝ :=
  ∑ J ∈ π.boxes, J.toSet₁.indicator (fun _ ↦ sSup (f '' J.Icc₁))

private theorem TaggedPrepartition.lower_darboux_le (π : TaggedPrepartition (Ioc a b)) {M : ℝ}
    {f : ℝ → ℝ} (hab : a < b) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hπ : π.IsPartition) :
    ∀ x ∈ Set.Ioc a b, π.lower_darboux f x ≤ f x := by
  intro x hx
  obtain ⟨ J, hJ, hmem ⟩ := hπ (fun _ ↦ x) (by simpa [hab] using hx)
  unfold lower_darboux
  rw [Finset.sum_apply, Finset.sum_eq_single J]
  · simp_all only [Set.mem_Icc, and_imp, Set.mem_Ioc, mem_toPrepartition, Box.mem₁, Box.toSet₁_def,
    Set.indicator, and_self, ↓reduceIte, Box.Icc₁_def]
    apply csInf_le
    · refine bddBelow_def.mp ⟨ -M, fun y hy ↦ ?_ ⟩
      simp only [Set.mem_image, Set.mem_Icc] at hy
      obtain ⟨ z, hz, rfl ⟩ := hy
      replace hJ := π.le_of_mem hJ
      simp [Box.le_iff₁, hab] at hJ
      grind
    grind
  · intro I hI; simp only [ne_eq, Set.indicator_apply_eq_zero]
    intro hIJ hxI
    have := Disjoint.notMem_of_mem_right (π.pairwiseDisjoint hI hJ hIJ) hmem
    simp at this hxI; grind
  intro h; exfalso; exact h hJ

private theorem TaggedPrepartition.upper_darboux_ge (π : TaggedPrepartition (Ioc a b)) {M : ℝ}
    (hab : a < b) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hπ : π.IsPartition) :
    ∀ x ∈ Set.Ioc a b, π.upper_darboux f x ≥ f x := by
  intro x hx
  obtain ⟨ J, hJ, hmem ⟩ := hπ (fun _ ↦ x) (by simpa [hab] using hx)
  unfold upper_darboux
  rw [Finset.sum_apply, Finset.sum_eq_single J]
  · simp_all only [Set.mem_Icc, and_imp, Set.mem_Ioc, mem_toPrepartition, Box.mem₁, Box.toSet₁_def,
    Set.indicator, and_self, ↓reduceIte, Box.Icc₁_def]
    apply le_csSup
    · refine bddAbove_def.mp ⟨ M, fun y hy ↦ ?_ ⟩
      simp only [Set.mem_image, Set.mem_Icc] at hy
      obtain ⟨ z, hz, rfl ⟩ := hy
      replace hJ := π.le_of_mem hJ
      simp [Box.le_iff₁, hab] at hJ
      grind
    grind
  · intro I hI; simp only [ne_eq, Set.indicator_apply_eq_zero]
    intro hIJ hxI
    have := Disjoint.notMem_of_mem_right (π.pairwiseDisjoint hI hJ hIJ) hmem
    simp at this hxI; grind
  intro h; exfalso; exact h hJ

private theorem TaggedPrepartition.lower_darboux_integrable (π : TaggedPrepartition (Ioc a b))
    (f : ℝ → ℝ) : IntervalIntegrable (π.lower_darboux f) volume a b := by
  unfold TaggedPrepartition.lower_darboux
  apply IntervalIntegrable.sum
  intro J hJ
  refine ⟨ .indicator ?_ (by measurability), .indicator ?_ (by measurability) ⟩
  <;> exact MeasureTheory.integrableOn_const (by simp) (by finiteness)

private theorem TaggedPrepartition.upper_darboux_integrable (π : TaggedPrepartition (Ioc a b))
    (f : ℝ → ℝ) : IntervalIntegrable (π.upper_darboux f) volume a b := by
  unfold TaggedPrepartition.upper_darboux
  apply IntervalIntegrable.sum
  intro J hJ
  refine ⟨ .indicator ?_ (by measurability), .indicator ?_ (by measurability) ⟩
  <;> exact MeasureTheory.integrableOn_const (by simp) (by finiteness)

private theorem RiemannIntegrable.darboux_integrable (hab : a < b) (hf : RiemannIntegrable a b f) :
  (IntegrationParams.Riemann.toFilteriUnion (Ioc a b) ⊤).Tendsto (fun π ↦
    eLpNorm (π.upper_darboux f - π.lower_darboux f) 1 (volume.restrict (.Ioc a b))) (nhds 0) := by
  sorry

private theorem RiemannIntegrable.intervalIntegrable_scalar (hf : RiemannIntegrable a b f)
    (hab : a < b) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  obtain ⟨ M, hM ⟩ := Bornology.IsBounded.exists_norm_le hf.bounded
  apply IntegrableOn.of_bound (by simp) (AEMeasurable.aestronglyMeasurable _) M
  · apply ae_restrict_of_forall_mem (by measurability)
    intro x hx; apply hM; simp only [Set.mem_image]; exact ⟨ x, Set.uIoc_subset_uIcc hx, rfl ⟩
  let l := IntegrationParams.Riemann.toFilteriUnion (Ioc a b) ⊤
  have : l.IsCountablyGenerated := by sorry
  simp only [Set.uIcc_of_lt hab, Real.norm_eq_abs] at hM
  replace hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M := by grind
  have hmes_lo (π : TaggedPrepartition (Ioc a b)) : AEMeasurable
    (TaggedPrepartition.lower_darboux f π) (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab.le]
    exact (π.lower_darboux_integrable f).aestronglyMeasurable.aemeasurable
  have hmes_hi (π : TaggedPrepartition (Ioc a b)) : AEMeasurable
    (TaggedPrepartition.upper_darboux f π) (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab.le]
    exact (π.upper_darboux_integrable f).aestronglyMeasurable.aemeasurable
  apply aemeasurable_of_le_ge_tendstoMeasure (l := l) (f_hi := TaggedPrepartition.upper_darboux f)
    hmes_lo
  · apply Filter.eventually_of_mem (IntegrationParams.eventually_isPartition _ _)
    intro π hπ
    apply MeasureTheory.ae_restrict_of_forall_mem (by measurability)
    rw [Set.uIoc_of_le hab.le]
    intro x hx; exact ⟨ π.lower_darboux_le hab hM hπ x hx, π.upper_darboux_ge hab hM hπ x hx⟩
  apply MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero _ (by fun_prop) _
  · intro π
    convert ((hmes_hi π).sub (hmes_lo π)).aestronglyMeasurable using 1
  simp only [Pi.sub_apply, sub_zero, Set.uIoc_of_le hab.le]
  exact hf.darboux_integrable hab

private theorem HasRiemannIntegral.intervalIntegral_eq_scalar (hf : HasRiemannIntegral a b f L)
    (hab : a < b) : ∫ x in a..b, f x = L := by
  sorry

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]
variable {B : E →L[ℝ] F →L[ℝ] G} {a b : ℝ} {f : ℝ → E} {g : ℝ → F} {L : G} {M : E}

/-- The Euclidean space-valued Riemann integral agrees with the interval integral. -/
private theorem riemannIntegral_eq_intervalIntegral_euclidean {ι : Type*} [Fintype ι]
    {f : ℝ → ι → ℝ} (hf : RiemannIntegrable a b f) : IntervalIntegrable f volume a b ∧
    riemannIntegral a b f = ∫ x in a..b, f x := by
  wlog hab : a ≤ b
  · rw [riemannIntegral.integral_symm, integral_symm, IntervalIntegrable.symm_iff, neg_inj]
    exact this hf.symm (by order)
  obtain rfl | hab := hab.eq_or_lt
  · simp
  set L := riemannIntegral a b f
  have hriem (i : ι) : HasRiemannIntegral a b (fun x ↦ f x i) (L i) := by
    convert hf.hasRiemannIntegral.map (φ := .proj i)
  have hinteg (i : ι) : IntervalIntegrable (fun x ↦ f x i) volume a b :=
    (hriem i).riemannIntegrable.intervalIntegrable_scalar hab
  have hinteg' (i : ι) : IntervalIntegrable (fun x ↦ Set.indicator {i} (f x)) volume a b := by
    convert (ContinuousLinearMap.toSpanSingleton ℝ
      (Set.indicator {i} (fun _ ↦ (1:ℝ)))).intervalIntegrable_comp (hinteg i) with _ x
    ext; simp [Set.indicator]; aesop
  have hint_eq (i : ι) : ∫ x in a..b, Set.indicator {i} (f x) = Set.indicator {i} L := by
    convert (ContinuousLinearMap.toSpanSingleton ℝ
      (Set.indicator {i} (fun _ ↦ (1:ℝ)))).intervalIntegral_comp_comm (hinteg i) with x
    · ext; simp [Set.indicator]; aesop
    ext; simp [Set.indicator, (hriem i).intervalIntegral_eq_scalar hab]; aesop
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
