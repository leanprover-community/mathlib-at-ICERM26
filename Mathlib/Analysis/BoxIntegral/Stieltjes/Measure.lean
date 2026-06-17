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
with the Stieltjes measure defined in `MeasureTheory.Measure.Stieltjes` when `g` is monotone.

When `g : StieltjesFunction ℝ` (which carries monotonicity and right-continuity), `g.measure`
is a regular Borel measure on `ℝ` with `g.measure (Ioc x y) = ENNReal.ofReal (g y - g x)`.
The main result here is that for a continuous integrand `f`, the Riemann–Stieltjes integral
of `f` against `g` (as a function via the bilinear form `(lsmul ℝ ℝ).flip`) coincides with
the Bochner integral of `f` against the Stieltjes measure `g.measure`.

## Main theorems

* `BoxIntegral.HasStieltjesIntegral.of_continuous_of_Stieltjes`: for `f` continuous on
  `uIcc a b` and `g : StieltjesFunction ℝ`, the Riemann–Stieltjes integral
  `∫⟨(lsmul ℝ ℝ).flip⟩ x in a..b, f x ∂g` exists and equals the Bochner integral
  `∫ x in a..b, f x ∂g.measure`. Holds for any `a, b : ℝ` (no ordering required).
* `BoxIntegral.StieltjesIntegrable.of_continuous_of_Stieltjes`: integrability corollary.
* `BoxIntegral.stieltjesIntegral_of_continuous_of_Stieltjes`: the integral-value identity.

## Implementation notes

The proof uses a step-function approximation: for any tagged partition `π` of `(a, b]` with
small mesh, the Riemann sum equals the Bochner integral of the step function
`∑ J ∈ π.boxes, J.toSet₁.indicator (fun _ ↦ f (π.tag J 0))`, which is uniformly close to
`f` by uniform continuity. Bounding `‖step - f‖ ≤ η` a.e. and using
`norm_integral_le_of_norm_le` then gives the result.

-/

@[expose] public section

namespace BoxIntegral

open ContinuousLinearMap MeasureTheory Set intervalIntegral StieltjesFunction

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {a b : ℝ} {f : ℝ → E} (g : StieltjesFunction ℝ)

theorem HasStieltjesIntegral.of_continuous_of_Stieltjes (hf : ContinuousOn f (.uIcc a b)) :
    HasStieltjesIntegral a b ((lsmul ℝ ℝ).flip) f g (∫ x in a..b, f x ∂g.measure) := by
  wlog hab : a ≤ b
  · rw [symm_iff, ← integral_symm]
    rw [Set.uIcc_comm] at hf
    exact this g hf (by order)
  obtain rfl | hab := hab.eq_or_lt
  · simp
  simp only [hasStieltjesIntegral_iff_lim_sum, Set.uIcc_of_lt, hab] at hf ⊢
  intro ε hε
  set μ := g.measure
  let M := μ.real (.Ioc a b)
  let η := ε / (M + 1)
  have hM_nonneg : 0 ≤ M := measureReal_nonneg
  have hη_pos : 0 < η := by positivity
  obtain ⟨δ, hδ_pos, hδf⟩ := hf.metric_uniform η hη_pos
  let δ' : NNReal := NNReal.mk (δ / 2) (by positivity)
  refine ⟨δ', show (0 : ℝ) < δ / 2 by positivity, fun π hhen hpart hmesh ↦ ?_⟩
  let step : ℝ → E := ∑ J ∈ π.boxes, (J.toSet₁.indicator (fun _ ↦ f (π.tag J 0)) ·)
  have hindicator_int (J : Box (Fin 1)) :
      IntervalIntegrable (J.toSet₁.indicator (fun _ ↦ f (π.tag J 0))) μ a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    refine .indicator ?_ measurableSet_Ioc
    simp [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
  have hstep_integral : ∫ x in a..b, step x ∂μ =
        ∑ J ∈ π.boxes, (g J.upper₁ - g J.lower₁) • f (π.tag J 0) := by
    simp only [step, Finset.sum_apply, μ]
    rw [intervalIntegral.integral_finsetSum (fun J _ ↦ hindicator_int J)]
    refine Finset.sum_congr rfl fun J hJ ↦ ?_
    rw [integral_of_le hab.le, Box.toSet₁_def, setIntegral_indicator measurableSet_Ioc]
    have hJ_sub : Set.Ioc J.lower₁ J.upper₁ ⊆ .Ioc a b := by
      have hJle := (J.le_Ioc_iff hab).mp (π.le_of_mem hJ)
      exact Set.Ioc_subset_Ioc hJle.1 hJle.2
    rw [inter_eq_right.mpr hJ_sub]
    simp [measureReal_def, measure_Ioc, μ,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (g.mono J.lower_le_upper₁))]
  simp only [Fin.isValue, lsmul_flip_apply, toSpanSingleton_apply, ← hstep_integral, gt_iff_lt]
  have hbound_ae : ∀ᵐ x ∂μ, x ∈ Set.Ioc a b → ‖step x - f x‖ ≤ η := by
    refine Filter.Eventually.of_forall fun x hx ↦ ?_
    simp only [step, Finset.sum_apply]
    obtain ⟨J, hJπ, hxJ⟩ := hpart (fun _ ↦ x) (by simpa [hab] using hx)
    have hxJ' : x ∈ J.toSet₁ := by simpa [Box.mem₁] using hxJ
    rw [Finset.sum_eq_single J (fun K hK hKJ ↦ ?_) (fun h ↦ absurd hJπ h)]; swap
    · refine indicator_of_notMem (fun hxK ↦ hKJ ?_) _
      exact π.toPrepartition.eq_of_mem_of_mem hK hJπ (by simpa [Box.mem₁] using hxK) hxJ
    rw [J.toSet₁.indicator_of_mem hxJ']
    have htag : π.tag J 0 ∈ J.Icc₁ := by simpa [Box.mem_Icc₁] using hhen J hJπ
    simp only [mesh_size_le_iff₁, δ', NNReal.coe_mk] at hmesh
    have htag_x : |π.tag J 0 - x| < δ := by
      simp only [Box.toSet₁_def, Set.mem_Ioc, abs_sub_lt_iff, Box.len] at hxJ' hmesh ⊢
      refine ⟨?_, ?_⟩ <;> linarith [htag.1, htag.2, hxJ'.1.le, hxJ'.2, hmesh J hJπ]
    have htag_mem := Icc_subset_of_box_le_Ioc hab (π.le_of_mem hJπ) htag
    exact (hδf _ htag_mem _ (Ioc_subset_Icc_self hx) htag_x).le
  rw [dist_eq_norm, ← intervalIntegral.integral_sub (.sum π.boxes (fun J _ ↦ hindicator_int J))
    (hf.intervalIntegrable_of_Icc hab.le)]
  calc
    _ ≤ ∫ _ in a..b, η ∂μ :=
          intervalIntegral.norm_integral_le_of_norm_le hab.le hbound_ae intervalIntegrable_const
    _ = M * (ε / (M + 1)) := by simp [integral_of_le hab.le, M, η]
    _ < ε := by field_simp; linarith

theorem StieltjesIntegrable.of_continuous_of_Stieltjes (hf : ContinuousOn f (.uIcc a b)) :
    StieltjesIntegrable a b ((lsmul ℝ ℝ).flip) f g :=
  (HasStieltjesIntegral.of_continuous_of_Stieltjes g hf).stieltjesIntegrable

theorem stieltjesIntegral_of_continuous_of_Stieltjes (hf : ContinuousOn f (.uIcc a b)) :
    ∫⟨(lsmul ℝ ℝ).flip⟩ x in a..b, f x ∂g = ∫ x in a..b, f x ∂g.measure :=
  (HasStieltjesIntegral.of_continuous_of_Stieltjes g hf).stieltjesIntegral_eq

theorem HasRiemannIntegral.of_continuous (hf : ContinuousOn f (.uIcc a b)) :
    HasRiemannIntegral a b f (∫ x in a..b, f x) := by
  convert HasStieltjesIntegral.of_continuous_of_Stieltjes (StieltjesFunction.id) hf
  exact Real.volume_eq_stieltjes_id

theorem RiemannIntegrable.of_continuous (hf : ContinuousOn f (.uIcc a b)) :
    RiemannIntegrable a b f :=
  (HasRiemannIntegral.of_continuous hf).riemannIntegrable

theorem riemannIntegral_of_continuous (hf : ContinuousOn f (.uIcc a b)) :
    riemannIntegral a b f = ∫ x in a..b, f x :=
  (HasRiemannIntegral.of_continuous hf).riemannIntegral_eq

end BoxIntegral
