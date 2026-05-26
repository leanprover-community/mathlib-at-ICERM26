/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-! # Riemann–Stieltjes integral and Stieltjes measure

In this file we show that the Riemann–Stieltjes integral
`∫⟨B⟩ x in a..b, f x ∂g` defined in `Analysis.BoxIntegral.Stieltjes.Defs` is compatible
with the Stieltjes measure defined in `MeasureTheory.Measure.Stieltjes` when g is monotone.

-/

@[expose] public section

namespace BoxIntegral

open ContinuousLinearMap MeasureTheory Set intervalIntegral

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {a b : ℝ}

theorem HasStieltjesIntegral.of_continuous_of_Stieltjes
    {f : ℝ → E} (hab : a < b)
    (hf : ContinuousOn f (.Icc a b)) (g : StieltjesFunction ℝ) :
    HasStieltjesIntegral a b ((lsmul ℝ ℝ).flip) f (g : ℝ → ℝ) (∫ x in a..b, f x ∂g.measure) := by
  rw [hasStieltjesIntegral_iff_lim_sum hab]
  intro ε hε
  let M := g.measure.real (.Ioc a b)
  let η := ε / (M + 1)
  have hM_nonneg : 0 ≤ M := measureReal_nonneg
  have hη_pos : 0 < η := by positivity
  obtain ⟨δ, hδ_pos, hδf⟩ := hf.metric_uniform η hη_pos
  let δ' : NNReal := NNReal.mk (δ / 2) (by positivity)
  refine ⟨δ', show (0 : ℝ) < δ / 2 by positivity, fun π hhen hpart hmesh ↦ ?_⟩
  let step : ℝ → E :=
    ∑ J ∈ π.boxes, fun x ↦ J.toSet₁.indicator (fun _ ↦ f (π.tag J 0)) x
  have hindicator_int (J : Box (Fin 1)) :
      IntervalIntegrable (J.toSet₁.indicator (fun _ ↦ f (π.tag J 0))) g.measure a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    refine IntegrableOn.indicator ?_ measurableSet_Ioc
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    refine (intervalIntegrable_const_iff enorm_ne_top).mpr (Or.inr ?_)
    simp [uIoc_of_le hab.le, StieltjesFunction.measure_Ioc]
  have hstep_int : IntervalIntegrable step g.measure a b :=
    IntervalIntegrable.sum π.boxes (fun J _ ↦ hindicator_int J)
  have hf_int : IntervalIntegrable f g.measure a b :=
    hf.intervalIntegrable_of_Icc hab.le
  have hstep_integral :
      ∫ x in a..b, step x ∂g.measure =
        ∑ J ∈ π.boxes, (g J.upper₁ - g J.lower₁) • f (π.tag J 0) := by
    simp only [step, Finset.sum_apply]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun J hJ ↦ ?_
      rw [intervalIntegral.integral_of_le hab.le, Box.toSet₁_def,
        setIntegral_indicator measurableSet_Ioc]
      have hJ_sub : Set.Ioc J.lower₁ J.upper₁ ⊆ .Ioc a b := by
        have hJle := (Box.le_Ioc_iff hab _).mp (π.le_of_mem hJ)
        exact Set.Ioc_subset_Ioc hJle.1 hJle.2
      rw [inter_eq_right.mpr hJ_sub]
      simp [measureReal_def, StieltjesFunction.measure_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (g.mono J.lower_le_upper₁))]
    · exact fun J _ ↦ hindicator_int J
  have hsum_eq :
      ∑ J ∈ π.boxes, ((lsmul ℝ ℝ).flip (f (π.tag J 0)))
          ((g : ℝ → ℝ) J.upper₁ - (g : ℝ → ℝ) J.lower₁)
        = ∫ x in a..b, step x ∂g.measure := by
    simpa using hstep_integral.symm
  rw [hsum_eq]
  have hbound_ae : ∀ᵐ x ∂g.measure, x ∈ Set.Ioc a b → ‖step x - f x‖ ≤ η := by
    refine Filter.Eventually.of_forall fun x hx ↦ ?_
    simp only [step, Finset.sum_apply]
    obtain ⟨J, hJπ, hxJ⟩ := hpart (fun _ ↦ x) (by simpa [hab] using hx)
    have hxJ' : x ∈ J.toSet₁ := by simpa [Box.mem₁] using hxJ
    rw [Finset.sum_eq_single J _ (fun h ↦ absurd hJπ h)]
    rotate_left
    · intro K hK hKJ
      refine indicator_of_notMem (fun hxK ↦ hKJ ?_) _
      exact π.toPrepartition.eq_of_mem_of_mem hK hJπ (by simpa [Box.mem₁] using hxK) hxJ
    rw [J.toSet₁.indicator_of_mem hxJ']
    have htag : π.tag J 0 ∈ J.Icc₁ := by simpa [Box.mem_Icc₁] using hhen J hJπ
    have hmesh_J : J.upper₁ - J.lower₁ < δ := by
      have hmesh' : ∀ K ∈ π.boxes, K.upper₁ - K.lower₁ ≤ (δ' : ℝ) := by
        simpa [mesh_size_le_iff₁] using hmesh
      have := hmesh' J hJπ
      simp only [δ', NNReal.coe_mk] at this
      linarith
    have htag_x : |π.tag J 0 - x| < δ := by
      simp only [Box.toSet₁_def, Set.mem_Ioc] at hxJ'
      rw [abs_sub_lt_iff]
      refine ⟨?_, ?_⟩ <;> linarith [htag.1, htag.2, hxJ'.1.le, hxJ'.2]
    have htag_mem : π.tag J 0 ∈ Icc a b :=
      Icc_subset_of_box_le_Ioc hab (π.le_of_mem hJπ) htag
    exact (hδf _ htag_mem _ (Ioc_subset_Icc_self hx) htag_x).le
  calc
    dist (∫ x in a..b, step x ∂g.measure) (∫ x in a..b, f x ∂g.measure)
        = ‖∫ x in a..b, step x - f x ∂g.measure‖ := by
          rw [dist_eq_norm, ← intervalIntegral.integral_sub hstep_int hf_int]
    _ ≤ ∫ _ in a..b, η ∂g.measure :=
          intervalIntegral.norm_integral_le_of_norm_le hab.le hbound_ae intervalIntegrable_const
    _ = η * M := by
          rw [intervalIntegral.integral_of_le hab.le, setIntegral_const, smul_eq_mul, mul_comm]
    _ < ε := by
          change ε / (M + 1) * M < ε
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith

theorem StieltjesIntegrable.of_continuous_of_Stieltjes
    {f : ℝ → E} (hab : a < b)
    (hf : ContinuousOn f (.Icc a b)) (g : StieltjesFunction ℝ) :
    StieltjesIntegrable a b ((lsmul ℝ ℝ).flip) f (g : ℝ → ℝ) :=
  (HasStieltjesIntegral.of_continuous_of_Stieltjes hab hf g).stieltjesIntegrable

theorem stieltjesIntegral_of_continuous_of_Stieltjes
    {f : ℝ → E} (hab : a < b)
    (hf : ContinuousOn f (.Icc a b)) (g : StieltjesFunction ℝ) :
    ∫⟨(lsmul ℝ ℝ).flip⟩ x in a..b, f x ∂(g : ℝ → ℝ) = ∫ x in a..b, f x ∂g.measure :=
  (HasStieltjesIntegral.of_continuous_of_Stieltjes hab hf g).stieltjesIntegral_eq

end BoxIntegral
