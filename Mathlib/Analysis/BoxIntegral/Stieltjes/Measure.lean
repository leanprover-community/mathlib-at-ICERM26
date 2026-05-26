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
  let M := g.measure.real (Set.Ioc a b)
  let η := ε / (M + 1)
  have hM_nonneg : 0 ≤ M := measureReal_nonneg
  have hη_pos : 0 < η := by
    positivity
  obtain ⟨δ, hδ_pos, hδf⟩ := hf.metric_uniform η hη_pos
  let δ' : NNReal := NNReal.mk (δ / 2) (by positivity)
  have hδ'_pos : 0 < δ' := by
    rw [← NNReal.coe_lt_coe]
    exact half_pos hδ_pos
  use δ'
  constructor
  apply hδ'_pos
  intro π
  intro hhen
  intro hpart
  intro hmesh
  let step : ℝ → E :=
    ∑ J ∈ π.boxes, fun x => Set.indicator J.toSet₁ (fun _ ↦ f (π.tag J 0)) x
  have hindicator_int (J : Box (Fin 1)) :
      IntervalIntegrable (fun x ↦ Set.indicator J.toSet₁ (fun _ ↦ f (π.tag J 0)) x)
        g.measure a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    refine IntegrableOn.indicator ?_ ?_
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le ?_).mp ?_
    exact Std.le_of_lt hab
    refine (intervalIntegrable_const_iff ?_).mpr ?_
    exact enorm_ne_top
    right
    simp [uIoc_of_le hab.le, StieltjesFunction.measure_Ioc]
    apply measurableSet_Ioc
  have hstep_int :
      IntervalIntegrable step g.measure a b := by
    unfold step
    exact IntervalIntegrable.sum π.boxes (fun J hJ ↦ hindicator_int J)
  have hf_int : IntervalIntegrable f g.measure a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab.le hf
  have hstep_integral :
      ∫ x in a..b, step x ∂g.measure =
        ∑ J ∈ π.boxes, (g J.upper₁ - g J.lower₁) • f (π.tag J 0) := by
    unfold step
    simp only [Finset.sum_apply]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun J hJ ↦ ?_
      rw [intervalIntegral.integral_of_le hab.le]
      calc
        ∫ x in Set.Ioc a b, Set.indicator J.toSet₁ (fun _ ↦ f (π.tag J 0)) x ∂g.measure
            = ∫ x in Set.Ioc a b ∩ J.toSet₁, f (π.tag J 0) ∂g.measure := by
              refine setIntegral_indicator ?_
              apply measurableSet_Ioc
        _ = ∫ x in J.toSet₁, f (π.tag J 0) ∂g.measure := by
              have ha : Set.Ioc a b ∩ J.toSet₁ = J.toSet₁ := by
                have ha1 : Set.Ioc a b ∩ J.toSet₁ ⊆ J.toSet₁ := by exact inter_subset_right
                have ha2 : J.toSet₁ ⊆ Set.Ioc a b ∩ J.toSet₁ := by
                  have hb : J.toSet₁ ⊆ Set.Ioc a b := by
                    intro x hx
                    have hJle : a ≤ J.lower₁ ∧ J.upper₁ ≤ b := by
                      apply (Box.le_Ioc_iff hab J).mp
                      apply π.le_of_mem hJ
                    simp
                    simp at hx
                    constructor
                    apply hJle.1.trans_lt hx.1
                    apply hx.2.trans hJle.2
                  exact subset_inter hb fun ⦃a⦄ a_1 ↦ a_1
                exact Eq.symm (Subset.antisymm ha2 ha1)
              rw [ha]
        _ = (g.measure.real J.toSet₁) • f (π.tag J 0) := by
              simp
        _ = (g J.upper₁ - g J.lower₁) • f (π.tag J 0) := by
              have ha : g.measure.real J.toSet₁ = (g J.upper₁ - g J.lower₁) := by
                rw [Box.toSet₁_def]
                rw [measureReal_def]
                rw [StieltjesFunction.measure_Ioc]
                refine ENNReal.toReal_ofReal ?_
                refine sub_nonneg.mpr ?_
                apply g.mono J.lower_le_upper₁
              rw [ha]
    · exact fun J _ ↦ hindicator_int J
  have hsum_eq :
      (∑ J ∈ π.boxes,
        ((ContinuousLinearMap.lsmul ℝ ℝ).flip (f (π.tag J 0)))
          ((g : ℝ → ℝ) J.upper₁ - (g : ℝ → ℝ) J.lower₁))
        = ∫ x in a..b, step x ∂g.measure := by
    simpa using hstep_integral.symm
  rw [hsum_eq]
  have hbound_ae :
      ∀ᵐ x ∂g.measure, x ∈ Set.Ioc a b →
        ‖step x - f x‖ ≤ η := by
    refine Filter.Eventually.of_forall fun x hx ↦ ?_
    unfold step
    have h1 : ∃ J ∈ π.boxes, (fun (_ : Fin 1) => x) ∈ J := by
      have hxI : (fun (_ : Fin 1) => x) ∈ Ioc a b := by
        simpa [hab] using hx
      exact hpart (fun (_ : Fin 1) => x) hxI
    obtain ⟨ J, hJ⟩ := h1
    have h2 : x ∈ J.toSet₁ := by
      simpa [Box.mem₁] using hJ.2
    have h3 : (∑ J ∈ π.boxes, fun x ↦ J.toSet₁.indicator (fun x ↦ f (π.tag J 0)) x) x = f (π.tag J 0) := by
      simp only [Finset.sum_apply]
      rw [Finset.sum_eq_single J]
      · rw [Set.indicator_of_mem h2]
      · intro K hK hKJ
        rw [Set.indicator_of_notMem]
        intro hxK
        have h' : K = J := by
          exact π.toPrepartition.eq_of_mem_of_mem hK hJ.1
            (by simpa [Box.mem₁] using hxK) hJ.2
        exact hKJ h'
      intro h'
      by_contra
      apply h' hJ.1
    rw [h3]
    have h4 : |(π.tag J 0) - x| < δ := by
      have ha : π.tag J 0 ∈ J.Icc₁ := by
        simpa [Box.mem_Icc₁] using hhen J hJ.1
      have hb : J.upper₁ - J.lower₁ ≤ (δ' : ℝ) := by
        have hmesh' :
            ∀ K ∈ π.boxes, K.upper₁ - K.lower₁ ≤ (δ' : ℝ) := by
          simpa [mesh_size_le_iff₁] using hmesh
        exact hmesh' J hJ.1
      have hc : J.upper₁ - J.lower₁ < δ := by
        simp [δ'] at hb
        nlinarith
      have hd : |π.tag J 0 - x| ≤ J.upper₁ - J.lower₁ := by
        rw [abs_sub_le_iff]
        constructor
        linarith [ha.1, ha.2, h2.1.le, h2.2]
        linarith [ha.1, ha.2, h2.1.le, h2.2]
      exact lt_of_le_of_lt hd hc
    have h4a : (π.tag J 0) ∈ Icc a b := by
      have h4a1 : (π.tag J 0) ∈ J.Icc₁ := by
        simpa [Box.mem_Icc₁] using hhen J hJ.1
      have h4a2 : J.Icc₁ ⊆ Icc a b := by
        intro y hy
        have ha : J.lower₁ ≤ y ∧ y ≤ J.upper₁ := by
          exact hy
        have hb : a ≤ J.lower₁ ∧ J.upper₁ ≤ b := by
          simpa [Box.le_Ioc_iff hab] using π.le_of_mem hJ.1
        constructor
        simp [hb.1.trans ha.1]
        simp [ha.2.trans hb.2]
      exact h4a2 h4a1
    have h4b : x ∈ Icc a b := by
      simp
      constructor
      apply hx.1.le
      apply hx.2
    apply (hδf (π.tag J 0) h4a x h4b h4).le

  calc
    dist (∫ x in a..b, step x ∂g.measure) (∫ x in a..b, f x ∂g.measure)
        = ‖∫ x in a..b, step x - f x ∂g.measure‖ := by
          rw [dist_eq_norm]
          rw [← intervalIntegral.integral_sub hstep_int hf_int]
    _ ≤ ∫ _ in a..b, η ∂g.measure := by
          unfold step η
          refine intervalIntegral.norm_integral_le_of_norm_le ?_ hbound_ae ?_
          apply hab.le
          apply intervalIntegrable_const (μ := g.measure) (a := a) (b := b)
    _ = η * M := by
          unfold η M
          rw [measureReal_def]
          rw [intervalIntegral.integral_of_le hab.le, setIntegral_const]
          apply mul_comm
    _ < ε := by
          unfold η M
          have h1 : 0 ≤ g.measure.real (Set.Ioc a b) := by positivity
          field_simp
          simp
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
