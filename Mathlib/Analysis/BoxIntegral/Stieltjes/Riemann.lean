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
  {μ : MeasureTheory.Measure α} {g : α → ℝ} {ι : Type*} {l : Filter ι}
  (hl : ∃ y : ℕ → ι, Filter.atTop.Tendsto y l) {f_lo f_hi : ι → α → ℝ}
  (hflo_mes : ∀ n, AEMeasurable (f_lo n) μ)
  (hg : ∀ᶠ n in l, ∀ᵐ (x : α) ∂μ, f_lo n x ≤ g x ∧ g x ≤ f_hi n x)
  (hconv : MeasureTheory.TendstoInMeasure μ (f_hi - f_lo) l 0) : AEMeasurable g μ := by
    obtain ⟨ y, hl ⟩ := hl
    replace hg := hl.eventually hg
    replace hconv := hconv.comp hl
    obtain ⟨ n, htop, hconv ⟩ := hconv.exists_seq_tendsto_ae'
    obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp (htop.eventually hg)
    apply AEMeasurable.congr (AEMeasurable.iSup (fun k : Set.Ici N ↦ hflo_mes (y (n k))))
    simp_rw [←Filter.eventually_imp_distrib_left, ←MeasureTheory.ae_all_iff] at hN
    filter_upwards [hN, hconv] with x hg hconv
    have : Filter.atTop.Tendsto (fun k : Set.Ici N ↦ g x - f_lo (y (n k)) x) (nhds 0) :=
      squeeze_zero (fun k ↦ by linarith [(hg k k.property).1])
        (fun k ↦ by simp; linarith [(hg k k.property).2])
        (hconv.comp (Filter.tendsto_Ici_atTop.mp fun ⦃_⦄ ↦ id))
    replace this := this.const_sub (g x)
    simp only [sub_sub_cancel, sub_zero] at this
    apply iSup_eq_of_forall_le_of_tendsto (by aesop) this

open Filter in
theorem BoxIntegral.IntegrationParams.eventually_isHenstock_of_Riemann {ι : Type*} [Fintype ι]
    (B : Box ι) : ∀ᶠ π in IntegrationParams.toFilteriUnion B ⊤ (l := IntegrationParams.Riemann),
    π.IsHenstock := by
  simp only [toFilteriUnion, toFilterDistortioniUnion, toFilterDistortion, Prepartition.iUnion_top,
    eventually_iSup, eventually_inf_principal, Set.mem_setOf_eq]
  refine (fun _ ↦ mem_iInf_of_mem (fun _ ↦ ⟨ 1, by norm_num ⟩) ?_)
  apply mem_iInf_of_mem (by simp [RCond]) _
  simp only [mem_principal, Set.setOf_subset_setOf]
  exact fun _ hπ _ ↦ hπ.isHenstock (by aesop)

namespace BoxIntegral

open intervalIntegral MeasureTheory Finset TaggedPrepartition

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

private theorem TaggedPrepartition.darboux_bounds (π : TaggedPrepartition (Ioc a b)) {M : ℝ}
    {f : ℝ → ℝ} (hab : a < b) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hπ : π.IsPartition) :
    ∀ x ∈ Set.Ioc a b, π.lower_darboux f x ≤ f x ∧ f x ≤ π.upper_darboux f x:= by
  intro x hx
  obtain ⟨ J, hJ, hmem ⟩ := hπ (fun _ ↦ x) (by simpa [hab] using hx)
  have h (g : Box (Fin 1) → ℝ → ℝ) :
    (∑ I ∈ π.boxes, I.toSet₁.indicator (g I)) x = g J x := by
    rw [sum_apply, sum_eq_single J]
    · simp_all
    · intro I hI; simp only [ne_eq, Set.indicator_apply_eq_zero]
      intro hIJ hxI
      have := Disjoint.notMem_of_mem_right (π.pairwiseDisjoint hI hJ hIJ) hmem
      simp at this hxI; grind
    intros; simp_all
  simp_rw [lower_darboux, upper_darboux, h, Box.Icc₁]
  simp at hmem
  replace hJ := π.le_of_mem hJ
  simp [Box.le_iff₁, hab] at hJ
  exact ⟨ csInf_le (bddBelow_def.mp ⟨ -M, fun y hy ↦ by grind ⟩) (by grind),
    le_csSup (bddAbove_def.mp ⟨ M, fun y hy ↦ by grind ⟩) (by grind) ⟩

private theorem TaggedPrepartition.integrable_of_piecewise (π : TaggedPrepartition (Ioc a b))
    (g : (Box (Fin 1)) → ℝ) :
    ∀ J ∈ π.boxes, IntervalIntegrable (J.toSet₁.indicator fun _ ↦ g J) volume a b := by
  refine fun _ _ ↦ ⟨ .indicator ?_ (by measurability), .indicator ?_ (by measurability) ⟩
  <;> exact MeasureTheory.integrableOn_const (by simp) (by finiteness)

private theorem TaggedPrepartition.lower_darboux_integrable (π : TaggedPrepartition (Ioc a b))
    (f : ℝ → ℝ) : IntervalIntegrable (π.lower_darboux f) volume a b :=
  .sum _ (π.integrable_of_piecewise _)

private theorem TaggedPrepartition.upper_darboux_integrable (π : TaggedPrepartition (Ioc a b))
    (f : ℝ → ℝ) : IntervalIntegrable (π.upper_darboux f) volume a b :=
  .sum _ (π.integrable_of_piecewise _)

private theorem RiemannIntegrable.darboux_integrable (hab : a < b) (hf : RiemannIntegrable a b f) :
  (IntegrationParams.Riemann.toFilteriUnion (Ioc a b) ⊤).Tendsto (fun π ↦
    eLpNorm (π.upper_darboux f - π.lower_darboux f) 1 (volume.restrict (.Ioc a b))) (nhds 0) := by
  sorry

open Prepartition.Even in
private theorem RiemannIntegrable.intervalIntegrable_scalar (hf : RiemannIntegrable a b f)
    (hab : a < b) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  obtain ⟨ M, hM ⟩ := Bornology.IsBounded.exists_norm_le hf.bounded
  apply IntegrableOn.of_bound (by simp) (AEMeasurable.aestronglyMeasurable _) M
  · apply ae_restrict_of_forall_mem (by measurability)
    intro x hx; apply hM; simp only [Set.mem_image]; exact ⟨ x, Set.uIoc_subset_uIcc hx, rfl ⟩
  let l := IntegrationParams.Riemann.toFilteriUnion (Ioc a b) ⊤
  simp only [Set.uIcc_of_lt hab, Real.norm_eq_abs] at hM
  replace hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M := by grind
  have hmes_lo (π : TaggedPrepartition (Ioc a b)) : AEMeasurable
    (π.lower_darboux f) (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab.le]
    exact (π.lower_darboux_integrable f).aestronglyMeasurable.aemeasurable
  have hmes_hi (π : TaggedPrepartition (Ioc a b)) : AEMeasurable
    (π.upper_darboux f) (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab.le]
    exact (π.upper_darboux_integrable f).aestronglyMeasurable.aemeasurable
  apply aemeasurable_of_le_ge_tendstoMeasure (l := l) (f_hi := TaggedPrepartition.upper_darboux f)
    _ hmes_lo
  · apply Filter.eventually_of_mem (IntegrationParams.eventually_isPartition _ _)
    intro π hπ
    apply ae_restrict_of_forall_mem (by measurability)
    rw [Set.uIoc_of_le hab.le]
    exact π.darboux_bounds hab hM hπ
  · apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero _ (by fun_prop) _
    · intro π
      convert ((hmes_hi π).sub (hmes_lo π)).aestronglyMeasurable using 1
    simp only [Pi.sub_apply, sub_zero, Set.uIoc_of_le hab.le]
    exact hf.darboux_integrable hab
  simp only [Filter.tendsto_iff_eventually,
    IntegrationParams.Riemann_toFilteriUnion_eventually_iff_mesh, gt_iff_lt,
    Prepartition.mesh_size_le_iff, Prepartition.mem_boxes, mem_toPrepartition, tsub_le_iff_right,
    Fin.forall_fin_one, Fin.isValue, Prepartition.iUnion_top, and_imp, Filter.eventually_atTop,
    ge_iff_le, forall_exists_index, l]
  classical
  let π : ℕ → TaggedPrepartition (Ioc a b) := fun N ↦
    let e : Prepartition.Even := ⟨ a, b, N+1, hab, by positivity ⟩
    {
      boxes := e.toPrepartition.boxes
      le_of_mem' := e.toPrepartition.le_of_mem'
      pairwiseDisjoint := e.toPrepartition.pairwiseDisjoint
      tag J := if J ≤ Ioc a b then J.upper else (Ioc a b).upper
      tag_mem_Icc J := by
        split_ifs with h
        · exact (BoxIntegral.Box.le_iff_Icc.mp h) J.upper_mem_Icc
        exact (Ioc a b).upper_mem_Icc
    }
  refine ⟨ π, fun p ε hε hp ↦ ⟨ ⌈(a-b) / ε ⌉₊, ?_ ⟩ ⟩
  intro N hN
  apply hp (π N)
  · simp only [Prepartition.Even.toPrepartition, TaggedPrepartition.mem_mk, Prepartition.mem_mk,
    mem_image, mem_range, Order.lt_add_one_iff, box, Fin.isValue,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, z_mono, Ioc.upper,
    Ioc.lower, π]
    intro i hi
    rw [z_succ, add_comm]; gcongr; field_simp

    sorry
  · intro J hJ
    simp only [Box.Icc₁_eq, Box.Icc₁_def, Fin.isValue, Set.mem_Icc, (π N).le_of_mem hJ, ↓reduceIte,
      Set.mem_setOf_eq, π]
    simpa [Box.upper₁] using J.lower_le_upper₁
  have : (π N).IsPartition := Prepartition.Even.toPrepartition.isPartition _
  simpa [isPartition_iff_iUnion_eq] using this



private theorem HasRiemannIntegral.intervalIntegral_eq_scalar (hf : HasRiemannIntegral a b f L)
    (hab : a < b) : ∫ x in a..b, f x = L := by
  have hint := hf.riemannIntegrable
  obtain ⟨ M, hM ⟩ := Bornology.IsBounded.exists_norm_le hint.bounded
  replace hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M := by simp [Set.uIcc_of_lt hab] at hM; grind
  apply tendsto_nhds_unique _ (hf.lim hab)
  rw [←tendsto_sub_nhds_zero_iff, tendsto_zero_iff_abs_tendsto_zero]
  have := hf.riemannIntegrable.darboux_integrable hab
  simp_rw [eLpNorm_one_eq_lintegral_enorm] at this
  have h (π : TaggedPrepartition (Ioc a b)) : ∫⁻ (x : ℝ) in .Ioc a b,
    ‖(π.upper_darboux f - π.lower_darboux f) x‖ₑ ≠ ⊤ := by
    rw [←integrable_toReal_iff]
    · exact .abs ((π.upper_darboux_integrable f).sub (π.lower_darboux_integrable f)).1
    · exact ((π.upper_darboux_integrable f).1.1.aemeasurable.sub
      (π.lower_darboux_integrable f).1.1.aemeasurable).enorm
    exact Filter.Eventually.of_forall (by finiteness)
  rw [←ENNReal.tendsto_toReal_zero_iff h] at this
  apply squeeze_zero' (by simp) _ this
  filter_upwards [IntegrationParams.eventually_isPartition _ _,
    IntegrationParams.eventually_isHenstock_of_Riemann _] with π hπ hhen
  rw [←ENNReal.ofReal_le_iff_le_toReal (h π)]
  simp only [← Pi.sub_apply, Fin.isValue, smul_eq_mul, Function.comp_apply,
    upper_darboux, lower_darboux, ← sum_sub_distrib, ← Set.indicator_sub', sum_apply]
  have h3 : ∀ J ∈ π.boxes, a ≤ J.lower₁ ∧ J.upper₁ ≤ b := by
    intro J hJ; simpa [Box.le_iff₁, Box.toSet₁, hab] using π.le_of_mem hJ
  have hmem : ∀ J ∈ π.boxes, π.tag J 0 ∈ J.Icc₁ := by
    intro J hJ; simpa using hhen J hJ
  have h0_1 : ∀ J ∈ π.boxes, sInf (f '' J.Icc₁) ≤ f (π.tag J 0) := by
    intro J hJ
    simp only [Box.Icc₁, Fin.isValue]
    apply csInf_le (bddBelow_def.mp ⟨ -M, fun y hy ↦ by grind ⟩) (Set.mem_image_of_mem _ _)
    simpa [Box.Icc₁] using hmem J hJ
  have h0_2 : ∀ J ∈ π.boxes, f (π.tag J 0) ≤ sSup (f '' J.Icc₁) := by
    intro J hJ
    simp only [Box.Icc₁, Fin.isValue]
    apply le_csSup (bddAbove_def.mp ⟨ M, fun y hy ↦ by grind ⟩) (Set.mem_image_of_mem _ _)
    simpa [Box.Icc₁] using hmem J hJ
  have h0 : ∀ J ∈ π.boxes, 0 ≤ sSup (f '' J.Icc₁) - sInf (f '' J.Icc₁) := by
    intro J hJ; linarith [h0_1 J hJ, h0_2 J hJ]
  have h1 (J : Box (Fin 1)): 0 ≤ J.upper₁ - J.lower₁ := by linarith [J.lower_le_upper₁]
  have h2 (x : ℝ) : ∀ J ∈ π.boxes, 0 ≤ J.toSet₁.indicator
    ((fun x ↦ sSup (f '' J.Icc₁)) - fun x ↦ sInf (f '' J.Icc₁)) x := by
    intro J hJ; simp only [Set.indicator, Box.toSet₁_def, Set.mem_Ioc, Pi.sub_apply]
    split_ifs
    · exact h0 J hJ
    simp
  have h4 : ∀ J ∈ π.boxes, volume (.Ioc J.lower₁ J.upper₁ ∩ .Ioc a b) =
    ENNReal.ofReal (J.upper₁ - J.lower₁) := by
    intro J hJ; calc
      _ = volume (.Ioc J.lower₁ J.upper₁) := by congr 1; grind
      _ = _ := by simp
  simp_rw [Real.enorm_of_nonneg (sum_nonneg (h2 _)), ENNReal.ofReal_sum_of_nonneg (h2 _)]
  rw [lintegral_finsetSum]
  · have (x : ℝ) (E : Set ℝ) (g : ℝ → ℝ): ENNReal.ofReal (E.indicator g x) =
        E.indicator (fun x ↦ ENNReal.ofReal (g x)) x := by simp [Set.indicator]; aesop
    simp_rw [this]
    simp only [Pi.sub_apply, Fin.isValue, Box.toSet₁_def, measurableSet_Ioc,
      lintegral_indicator, Measure.restrict_restrict, lintegral_const, MeasurableSet.univ,
      Measure.restrict_apply, Set.univ_inter, ge_iff_le]
    trans ∑ J ∈ π.boxes, ENNReal.ofReal ((J.upper₁ - J.lower₁) *
      (sSup (f '' J.Icc₁) - sInf (f '' J.Icc₁)))
    · rw [←ENNReal.ofReal_sum_of_nonneg (fun J hJ ↦ mul_nonneg (h1 J) (h0 J hJ))]
      apply ENNReal.ofReal_le_ofReal
      simp only [Fin.isValue, mul_sub, sum_sub_distrib, abs_le', tsub_le_iff_right, neg_sub]
      have h5 : ∑ J ∈ π.boxes, (J.upper₁ - J.lower₁) * f (π.tag J 0) ≤
        ∑ J ∈ π.boxes, (J.upper₁ - J.lower₁) * sSup (f '' J.Icc₁) := by
        apply sum_le_sum; intro J hJ; specialize h1 J; specialize h0_2 J hJ; gcongr
      have h6 : ∑ J ∈ π.boxes, (J.upper₁ - J.lower₁) * f (π.tag J 0) ≥
        ∑ J ∈ π.boxes, (J.upper₁ - J.lower₁) * sInf (f '' J.Icc₁) := by
        apply sum_le_sum; intro J hJ; specialize h1 J; specialize h0_1 J hJ; gcongr
      have h7 : ∫ x in a..b, f x ≤ ∑ J ∈ π.boxes, (J.upper₁ - J.lower₁) * sSup (f '' J.Icc₁)
        := calc
        _ ≤ ∫ x in a..b, π.upper_darboux f x :=
          intervalIntegral.integral_mono_on_of_le_Ioo hab.le
            (hint.intervalIntegrable_scalar hab) (π.upper_darboux_integrable f)
            (fun x hx ↦ (π.darboux_bounds hab hM hπ x (by grind)).2)
        _ = _ := by
          simp only [upper_darboux, sum_apply]
          rw [intervalIntegral.integral_finsetSum]
          · apply sum_congr rfl; intro J hJ
            rw [intervalIntegral.integral_eq_integral_of_support_subset]
            · simp [J.lower_le_upper₁]
            apply Set.support_indicator_subset.trans
            grind [Box.toSet₁]
          apply π.integrable_of_piecewise
      have h8 : ∫ x in a..b, f x ≥ ∑ J ∈ π.boxes, (J.upper₁ - J.lower₁) * sInf (f '' J.Icc₁)
        := calc
        _ ≥ ∫ x in a..b, π.lower_darboux f x :=
          intervalIntegral.integral_mono_on_of_le_Ioo hab.le
            (π.lower_darboux_integrable f) (hint.intervalIntegrable_scalar hab)
            (fun x hx ↦ (π.darboux_bounds hab hM hπ x (by grind)).1)
        _ = _ := by
          simp only [lower_darboux, sum_apply]
          rw [intervalIntegral.integral_finsetSum]
          · apply sum_congr rfl; intro J hJ
            rw [intervalIntegral.integral_eq_integral_of_support_subset]
            · simp [J.lower_le_upper₁]
            apply Set.support_indicator_subset.trans
            have := π.le_of_mem hJ
            simp_all [Box.le_iff₁, Box.toSet₁]
            grind
          apply π.integrable_of_piecewise
      grind
    apply le_of_eq (sum_congr (by rfl) _); intro J hJ
    rw [mul_comm, h4 J hJ, ENNReal.ofReal_mul' (h1 J)]
  intros; measurability

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
