/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.IntegrationByParts
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Fourier transform estimates via the Riemann–Stieltjes integral

In this file we obtain estimates on Fourier transforms via the Riemann–Stieltjes integral
`∫⟨B⟩ x in a..b, f x ∂g` defined in `Analysis.BoxIntegral.Stieltjes.Defs`.

-/

@[expose] public section

open BoxIntegral ContinuousLinearMap TaggedPrepartition Prepartition
open scoped FourierTransform
open Filter Complex MeasureTheory intervalIntegral

namespace BoundedVariationOn

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {f : ℝ → E}

lemma atTop_limUnder_of_integrable
    (hf1 : Integrable f) (hf2 : BoundedVariationOn f .univ) : atTop.limUnder f = 0 := by
  have hlim := hf2.tendsto_atTop_limUnder
  set L := atTop.limUnder f
  by_contra! hL
  have hpos : 0 < ‖L‖/2 := by positivity
  simp only [Metric.tendsto_nhds, gt_iff_lt, eventually_atTop, ge_iff_le] at hlim
  obtain ⟨R, hR⟩ := hlim (‖L‖/2) hpos
  have : Set.Ici R ⊆ {x | ‖L‖ / 2 < ‖f x‖} := by
    peel hR with x hx hR
    simp only [Set.mem_setOf_eq, dist_eq_norm] at hR ⊢
    linarith [norm_le_norm_add_norm_sub (f x) L]
  exact (hf1.measure_norm_gt_lt_top hpos).ne (measure_mono_top this (by simp))

lemma tendsto_zero_atTop_of_integrable
    (hf1 : Integrable f) (hf2 : BoundedVariationOn f .univ) : atTop.Tendsto f (nhds 0) :=
  (hf2.atTop_limUnder_of_integrable hf1) ▸ hf2.tendsto_atTop_limUnder

lemma atBot_limUnder_of_integrable
    (hf1 : Integrable f) (hf2 : BoundedVariationOn f .univ) : atBot.limUnder f = 0 := by
  have hlim := hf2.tendsto_atBot_limUnder
  set L := atBot.limUnder f
  by_contra! hL
  have hpos : 0 < ‖L‖/2 := by positivity
  simp only [Metric.tendsto_nhds, gt_iff_lt, eventually_atBot] at hlim
  obtain ⟨R, hR⟩ := hlim (‖L‖/2) hpos
  have : Set.Iic R ⊆ {x | ‖L‖ / 2 < ‖f x‖} := by
    peel hR with x hx hR
    simp only [Set.mem_setOf_eq, dist_eq_norm] at hR ⊢
    linarith [norm_le_norm_add_norm_sub (f x) L]
  exact (hf1.measure_norm_gt_lt_top hpos).ne (measure_mono_top this (by simp))

lemma tendsto_zero_atBot_of_integrable
    (hf1 : Integrable f) (hf2 : BoundedVariationOn f .univ) : atBot.Tendsto f (nhds 0) :=
  (hf2.atBot_limUnder_of_integrable hf1) ▸ hf2.tendsto_atBot_limUnder

end BoundedVariationOn

namespace FourierTransform

variable {a b : ℝ} (ξ x : ℝ) {g : ℝ → ℂ}

noncomputable def e : ℂ := exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * I)

noncomputable def E : ℂ := (-(2 * Real.pi * I * (ξ : ℂ)))⁻¹ * e ξ x

@[simp]
lemma norm_e : ‖e ξ x‖ = 1 := norm_exp_ofReal_mul_I _

@[fun_prop]
lemma continuous_e : Continuous (e ξ) := by unfold e; fun_prop

@[fun_prop]
lemma continuous_E : Continuous (E ξ) := by unfold E; fun_prop

lemma hasDerivAt_e : HasDerivAt (e ξ)
    (e ξ x * ((↑(-2 * Real.pi * ξ) : ℂ) * I)) x := by
  have ha : HasDerivAt (fun (x : ℝ) ↦ (-2 * Real.pi * x : ℝ)) (-2 * Real.pi : ℝ) x := by
    convert (hasDerivAt_const x ((-2 * Real.pi) : ℝ)).mul (hasDerivAt_id x) using 1
    simp
  have h1 : HasDerivAt (fun (x : ℝ) ↦ (-2 * Real.pi * x * ξ : ℝ)) (-2 * Real.pi * ξ : ℝ) x := by
    convert ha.mul (hasDerivAt_const x (ξ : ℝ)) using 1
    simp
  exact (HasDerivAt.mul_const h1.ofReal_comp I).cexp

lemma hasDerivAt_E {ξ : ℝ} (hξ : ξ ≠ 0) : HasDerivAt (E ξ) (e ξ x) x := by
  convert (hasDerivAt_const x _).mul (hasDerivAt_e ξ x) using 1
  field_simp [e, hξ, Real.pi_ne_zero, I_ne_zero]
  simp

@[simp]
lemma deriv_E {ξ : ℝ} (hξ : ξ ≠ 0) : deriv (E ξ) = e ξ := by ext; exact (hasDerivAt_E _ hξ).deriv

theorem intervalIntegral_e_eq_primitive_sub {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∫ x in a..b, e ξ x = E ξ b - E ξ a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hasDerivAt_E x hξ) ((continuous_e ξ).intervalIntegrable a b)

lemma isBoundedUnder_norm_E_atTop (φ : ℝ → ℝ) :
    atTop.IsBoundedUnder (· ≤ ·) (‖E ξ <| φ ·‖) := by
  refine Filter.isBoundedUnder_of_eventually_le (a := 1 / (2 * Real.pi * ‖ξ‖)) ?_
  filter_upwards; intro a
  simp [E, abs_of_nonneg, Real.pi_nonneg]

/-- Finite-interval Stieltjes estimate for the Fourier antiderivative. -/
theorem norm_stieltjesIntegral_E_le (hab : a < b) (hg : BoundedVariationOn g (.Icc a b)) :
    ‖∫⟨mul ℝ ℂ⟩ x in a..b, E ξ x ∂g‖ ≤ |ξ|⁻¹ * (Real.pi⁻¹ * 2⁻¹) *
      (eVariationOn g (.Icc a b)).toReal := by
  calc
    _ ≤ ‖mul ℝ ℂ‖ * (|ξ|⁻¹ * (Real.pi⁻¹ * 2⁻¹) * (eVariationOn g (.Icc a b)).toReal) := by
      apply stieltjesIntegral_le_integral_of_norm_of_variation hab.le
        (show BoundedVariationOn g (.uIcc a b) by rwa [Set.uIcc_of_lt hab])
        (StieltjesIntegrable.of_continuousOn_of_boundedVariationOn
          (show ContinuousOn (E ξ) (.uIcc a b) by fun_prop)
          (show BoundedVariationOn g (.uIcc a b) by rwa [Set.uIcc_of_lt hab])).hasStieltjesIntegral
      simp only [E, inv_neg, mul_inv_rev, inv_I, neg_mul, mul_neg, neg_neg, Complex.norm_mul,
        norm_inv, norm_real, Real.norm_eq_abs, norm_I, Real.pi_nonneg, abs_of_nonneg, norm_ofNat,
        one_mul, norm_e, mul_one]
      convert HasStieltjesIntegral.of_const
        (g := fun x ↦ (eVariationOn g (.Icc a x)).toReal) using 1
      simp
    _ ≤ _ := by grw [opNorm_mul_le ℝ ℂ]; simp

/-- If the integrator is the Fourier primitive, the Stieltjes integral is the ordinary integral
against its derivative, here specialized to the Fourier kernel. -/
theorem hasStieltjesIntegral_E {ξ : ℝ} (hξ : ξ ≠ 0) (hg : RiemannIntegrable a b g) :
    HasStieltjesIntegral a b (mul ℝ ℂ).flip g (E ξ) (∫ x in a..b, e ξ x * g x) := by
  have h (x : ℝ) := hasDerivAt_E x hξ
  convert HasStieltjesIntegral.of_contDiffOn ?_ hg using 3 with x
  · simp [(h x).deriv, mul_comm]
  refine (contDiff_one_iff_deriv.mpr ⟨fun x ↦ (h x).differentiableAt, ?_⟩).contDiffOn
  simp only [ne_eq, hξ, not_false_eq_true, deriv_E]
  fun_prop

/-- The ordinary Fourier integral over a finite interval is the Stieltjes integral against the
Fourier antiderivative, up to the boundary term supplied by integration by parts. -/
theorem interval_fourierIntegral_eq_boundary_sub_stieltjes
    (hab : a < b) {ξ : ℝ} (hξ : ξ ≠ 0) (hg : BoundedVariationOn g (.Icc a b)) :
    (∫ x in a..b, e ξ x * g x) = g b * E ξ b - g a * E ξ a - ∫⟨mul ℝ ℂ⟩ x in a..b, E ξ x ∂g := by
  have hInt : StieltjesIntegrable a b (mul ℝ ℂ) (E ξ) g := by
    rw [← Set.uIcc_of_lt hab] at hg
    exact .of_continuousOn_of_boundedVariationOn (by fun_prop) hg
  rw [(hasStieltjesIntegral_E hξ (hg.riemannIntegrable hab.le)).stieltjesIntegral_eq.symm,
      stieltjesIntegral.by_parts hInt]
  simp [mul_comm]

theorem tendsto_fourier_boundary_zero_of_tendsto
    (hg_top : atTop.Tendsto g (nhds 0)) (hg_bot : atBot.Tendsto g (nhds 0)) :
    atTop.Tendsto (fun R ↦ g R * E ξ R - g (-R) * E ξ (-R)) (nhds 0) := by
  simpa using (hg_top.zero_mul_isBoundedUnder_le
      (isBoundedUnder_norm_E_atTop ξ id)).sub
    ((hg_bot.comp tendsto_neg_atTop_atBot).zero_mul_isBoundedUnder_le
      (isBoundedUnder_norm_E_atTop ξ _))

theorem tendsto_fourier_boundary_zero (hg1 : MeasureTheory.Integrable g)
    (hg2 : BoundedVariationOn g .univ) :
    atTop.Tendsto (fun R ↦ g R * E ξ R - g (-R) * E ξ (-R)) (nhds 0) :=
  tendsto_fourier_boundary_zero_of_tendsto ξ (hg2.tendsto_zero_atTop_of_integrable hg1)
    (hg2.tendsto_zero_atBot_of_integrable hg1)

lemma integrable_e_mul (hg : Integrable g) : Integrable (fun x : ℝ ↦ e ξ x * g x) volume := by
  refine hg.congr' (AEStronglyMeasurable.mul (by fun_prop) hg.1) ?_
  filter_upwards with a
  simp only [e, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_mul]

theorem tendsto_interval_e_integral (hg1 : MeasureTheory.Integrable g) :
    atTop.Tendsto (fun R : ℝ ↦ ∫ x in (-R)..R, (e ξ x) * g x) (nhds (𝓕 g ξ)) := by
  have hb : 𝓕 g ξ = ∫ x : ℝ, e ξ x * g x := by
    simp [Real.fourier_real_eq_integral_exp_smul, e]
  simpa [hb] using intervalIntegral_tendsto_integral (integrable_e_mul ξ hg1)
      (tendsto_neg_atTop_atBot) fun ⦃_⦄ a ↦ a

theorem fourier_tendsto_stieltjesPrimitive_of_boundedVariation
    (hg1 : Integrable g) (hg2 : BoundedVariationOn g .univ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ L, atTop.Tendsto (fun R ↦ ∫⟨mul ℝ ℂ⟩ x in -R..R, (E ξ x) ∂g) (nhds L) ∧
      𝓕 g ξ = -L ∧
      ‖L‖ ≤ |ξ|⁻¹ * (Real.pi⁻¹ * 2⁻¹) * (eVariationOn g .univ).toReal := by
  use - 𝓕 g ξ
  have hb (R : ℝ) : BoundedVariationOn g (.Icc (-R) R) := .mono hg2 fun ⦃a⦄ a ↦ trivial
  have hS_eq : (fun R ↦ ∫⟨mul ℝ ℂ⟩ x in -R..R, (E ξ x) ∂g)
    =ᶠ[atTop] fun R ↦ g R * E ξ R
    - g (-R) * E ξ (-R) - ∫ x in (-R)..R, e ξ x * g x := by
    filter_upwards [eventually_ge_atTop 1] with R hR
    simp [interval_fourierIntegral_eq_boundary_sub_stieltjes (by simp; linarith) hξ (hb R)]
  have hS_tendsto := Tendsto.congr' hS_eq.symm (by simpa using
      (tendsto_fourier_boundary_zero ξ hg1 hg2).sub (tendsto_interval_e_integral ξ hg1))
  refine ⟨hS_tendsto, by simp,
    (isClosed_le continuous_norm continuous_const).mem_of_tendsto hS_tendsto ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
  grw [norm_stieltjesIntegral_E_le ξ (by linarith) (hb R),
    ENNReal.toReal_mono hg2 (eVariationOn.mono g fun ⦃_⦄ _ ↦ trivial)]

lemma fourier_bounded_variation (hg1 : Integrable g) (hg2 : BoundedVariationOn g .univ)
    {ξ : ℝ} (hξ : ξ ≠ 0) : ‖𝓕 g ξ‖ ≤ |ξ|⁻¹ * (Real.pi⁻¹ * 2⁻¹) * (eVariationOn g .univ).toReal
    := by
  obtain ⟨L, _, hb, hc⟩ := fourier_tendsto_stieltjesPrimitive_of_boundedVariation hg1 hg2 hξ
  simpa [hb] using hc

end FourierTransform
