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

/-! # Fourier transform estimates via the Riemann–Stieltjes integral

In this file we obtain estimates on Fourier transforms via the Riemann–Stieltjes integral
`∫⟨B⟩ x in a..b, f x ∂g` defined in `Analysis.BoxIntegral.Stieltjes.Defs`.

-/

@[expose] public section


-- TODO: find a namespace

section FourierStieltjes

open BoxIntegral ContinuousLinearMap TaggedPrepartition Prepartition
open scoped FourierTransform
open Filter Complex MeasureTheory intervalIntegral

variable {a b : ℝ} (ξ x : ℝ)

noncomputable def e : ℂ := exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * I)

noncomputable def E : ℂ := (-(2 * Real.pi * I * (ξ : ℂ)))⁻¹ * e ξ x

@[simp]
lemma norm_e : ‖e ξ x‖ = 1 := norm_exp_ofReal_mul_I _

@[fun_prop]
lemma continuous_e : Continuous (e ξ) := by unfold e; fun_prop

@[fun_prop]
lemma continuous_E : Continuous (E ξ) := by unfold E; fun_prop
noncomputable section

lemma hasDerivAt_e : HasDerivAt (e ξ)
    (e ξ x * ((↑(-2 * Real.pi * ξ) : ℂ) * I)) x := by
  have ha : HasDerivAt (fun (x:ℝ) ↦ (-2 * Real.pi * x :ℝ)) (-2 * Real.pi : ℝ) x := by
    convert (hasDerivAt_const x ((-2 * Real.pi) : ℝ)).mul (hasDerivAt_id x) using 1
    simp
  have h1 : HasDerivAt (fun (x:ℝ) ↦ (-2 * Real.pi * x * ξ :ℝ)) (-2 * Real.pi*ξ : ℝ) x := by
    convert ha.mul (hasDerivAt_const x (ξ:ℝ)) using 1
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
theorem norm_stieltjesIntegral_E_le
    {g : ℝ → ℂ} (hab : a < b) (hg : BoundedVariationOn g (.Icc a b)) :
    ‖stieltjesIntegral a b (mul ℝ ℂ) (E ξ) g‖ ≤
      |ξ|⁻¹ * (Real.pi⁻¹ * 2⁻¹) *
        (eVariationOn g (.Icc a b)).toReal := by
  calc
    _ ≤ ‖(mul ℝ ℂ)‖ * (|ξ|⁻¹ * (Real.pi⁻¹ * 2⁻¹) * (eVariationOn g (.Icc a b)).toReal) := by
      apply integral_le_integral_of_variation hab hg
        (StieltjesIntegrable.of_continuousOn_of_boundedVariationOn _
          hab (by fun_prop) hg).hasStieltjesIntegral
      simp only [E, inv_neg, mul_inv_rev, inv_I, neg_mul, mul_neg, neg_neg, Complex.norm_mul,
        norm_inv, norm_real, Real.norm_eq_abs, norm_I, Real.pi_nonneg, abs_of_nonneg, norm_ofNat,
        one_mul, norm_e, mul_one]
      convert HasStieltjesIntegral.of_const _ _
        (fun x ↦ (eVariationOn g (.Icc a x)).toReal) using 1
      simp
    _ ≤ _ := by grw [opNorm_mul_le ℝ ℂ]; simp

/-- If the integrator is the Fourier primitive, the Stieltjes integral is the ordinary integral
against its derivative, here specialized to the Fourier kernel. -/
theorem hasStieltjesIntegral_E
    {g : ℝ → ℂ} (hab : a < b) {ξ : ℝ} (hξ : ξ ≠ 0)
    (hg : RiemannIntegrable a b g) :
    HasStieltjesIntegral a b (mul ℝ ℂ).flip g (E ξ)
      (∫ x in a..b, e ξ x * g x) := by
      have h (x : ℝ) := hasDerivAt_E x hξ
      convert integral_of_derivative _ hab ?_ hg using 3 with x
      · simp [(h x).deriv, mul_comm]
      refine (contDiff_one_iff_deriv.mpr ⟨ fun x ↦ (h x).differentiableAt, ?_ ⟩).contDiffOn
      simp only [ne_eq, hξ, not_false_eq_true, deriv_E]
      fun_prop

/-- The ordinary Fourier integral over a finite interval is the Stieltjes integral against the
Fourier antiderivative, up to the boundary term supplied by integration by parts. -/
theorem interval_fourierIntegral_eq_boundary_sub_stieltjes
    {g : ℝ → ℂ} (hab : a < b) {ξ : ℝ} (hξ : ξ ≠ 0) (hg : BoundedVariationOn g (.Icc a b)) :
    (∫ x in a..b, e ξ x * g x) =
      g b * E ξ b -
        g a * E ξ a -
          ∫⟨mul ℝ ℂ⟩ x in a..b, E ξ x ∂g := by
  have hInt : StieltjesIntegrable a b (mul ℝ ℂ) (E ξ) g :=
    .of_continuousOn_of_boundedVariationOn _ hab (by fun_prop) hg
  rw [(hasStieltjesIntegral_E hab hξ (hg.riemannIntegrable hab.le)).stieltjesIntegral_eq.symm,
      stieltjesIntegral.by_parts hInt]
  simp [mul_comm]

theorem tendsto_fourier_boundary_zero_of_tendsto
    {g : ℝ → ℂ} (hg_top : atTop.Tendsto g (nhds 0)) (hg_bot : atBot.Tendsto g (nhds 0)) (ξ : ℝ) :
    atTop.Tendsto (fun R ↦ g R * E ξ R - g (-R) * E ξ (-R)) (nhds 0) := by
  simpa using (hg_top.zero_mul_isBoundedUnder_le
      (isBoundedUnder_norm_E_atTop ξ id)).sub
    ((hg_bot.comp tendsto_neg_atTop_atBot).zero_mul_isBoundedUnder_le
      (isBoundedUnder_norm_E_atTop ξ _))

-- TODO: generalized to arbitrary normed vector spaces (including both R and C) using the
-- existing BoundedVariation API on limits at infinity

lemma tendsto_zero_atTop_of_integrable_boundedVariationOn_real
    {f : ℝ → ℝ} (hf1 : Integrable f) (hf2 : BoundedVariationOn f .univ) :
    atTop.Tendsto f (nhds 0) := by
  let V : ℝ := (eVariationOn f .univ).toReal
  let p : ℝ → ℝ := fun x ↦ variationOnFromTo f .univ 0 x
  let q : ℝ → ℝ := fun x ↦ variationOnFromTo f .univ 0 x - f x
  have hloc : LocallyBoundedVariationOn f .univ := hf2.locallyBoundedVariationOn
  have hp_mono : Monotone p :=
    monotone_iff_forall_lt.mpr (fun _ _ _ ↦
    monotoneOn_univ.mp (variationOnFromTo.monotoneOn hloc trivial) (by linarith))
  have hq_mono : Monotone q :=
    monotoneOn_univ.mp (variationOnFromTo.sub_self_monotoneOn hloc trivial)
  have hp_bound_point : ∀ x, p x ≤ V := by
    intro x
    by_cases hx : 0 ≤ x
    · unfold p V
      rw [variationOnFromTo.eq_of_le f .univ hx]
      exact ENNReal.toReal_mono (by simpa using hf2) (eVariationOn.mono f (fun ⦃_⦄ _ ↦ trivial))
    · unfold p V
      push Not at hx
      simp only [variationOnFromTo.eq_of_ge f .univ hx.le, Set.univ_inter]
      have : 0 ≤ (eVariationOn f (.Icc x 0)).toReal := ENNReal.toReal_nonneg
      calc
         _ ≤ (eVariationOn f (.Icc x 0)).toReal := by linarith
         _ ≤ _ :=
          ENNReal.toReal_mono (by simpa using hf2) (eVariationOn.mono f (fun ⦃_⦄ _ ↦ trivial))
  have hp_tend : atTop.Tendsto p (nhds (⨆ x, p x)) :=
    tendsto_atTop_ciSup hp_mono ⟨ V, mem_upperBounds.mpr (by simpa using hp_bound_point) ⟩
  have hq_tend : atTop.Tendsto q (nhds (⨆ x, q x)) := by
    refine tendsto_atTop_ciSup hq_mono ⟨V + (V - f 0), ?_ ⟩
    rintro y ⟨x,rfl⟩
    unfold q
    have : f 0 - f x ≤ V := hf2.sub_le trivial trivial
    linarith [hp_bound_point x]
  have hf_tend : atTop.Tendsto f (nhds ((⨆ x, p x) - (⨆ x, q x))) := by
    convert hp_tend.sub hq_tend using 1
    ext; dsimp [p, q]; ring
  have hzero : ((⨆ x, p x) - (⨆ x, q x)) = 0 := by
    refine IntegrableAtFilter.eq_zero_of_tendsto (hf1.integrableAtFilter atTop) ?_ hf_tend
    intro s hs; rcases mem_atTop_sets.1 hs with ⟨b, hb⟩
    rw [← top_le_iff, ← Real.volume_Ici]
    exact measure_mono hb
  simpa [hzero] using hf_tend

lemma tendsto_zero_atBot_of_integrable_boundedVariationOn_real
    {f : ℝ → ℝ} (hf1 : Integrable f) (hf2 : BoundedVariationOn f .univ) :
    atBot.Tendsto f (nhds 0) := by
  have hcomp_bv : eVariationOn (f ∘ Neg.neg) .univ ≠ ⊤ := by
    rw [eVariationOn.comp_eq_of_antitoneOn f Neg.neg (fun x _ y _ hxy ↦ neg_le_neg hxy)]
    have himage : Set.range (Neg.neg : ℝ → ℝ) = .univ := by
      ext x; exact ⟨ fun _ ↦ trivial, fun _ ↦ ⟨-x, by simp⟩ ⟩
    simpa [himage] using hf2
  simpa [Function.comp_def] using (tendsto_zero_atTop_of_integrable_boundedVariationOn_real
    (((Measure.measurePreserving_neg volume).integrable_comp_emb measurableEmbedding_neg).2 hf1)
      hcomp_bv).comp tendsto_neg_atBot_atTop

lemma tendsto_complex_zero_of_re_im {ι : Type*} {l : Filter ι} {g : ι → ℂ}
    (hre : l.Tendsto (reCLM ∘ g) (nhds 0)) (him : l.Tendsto (imCLM ∘ g) (nhds 0)) :
    l.Tendsto g (nhds 0) := by
  simpa using (equivRealProdCLM.symm.continuous.tendsto' (0, 0) (equivRealProdCLM.symm (0, 0))
    rfl).comp (hre.prodMk_nhds him)

lemma tendsto_zero_atTop_of_integrable_boundedVariationOn_complex
    {g : ℝ → ℂ} (hg1 : Integrable g) (hg2 : BoundedVariationOn g .univ) :
    atTop.Tendsto g (nhds 0) :=
  tendsto_complex_zero_of_re_im
    (tendsto_zero_atTop_of_integrable_boundedVariationOn_real (reCLM.integrable_comp hg1)
      (reCLM.lipschitz.comp_boundedVariationOn hg2))
    (tendsto_zero_atTop_of_integrable_boundedVariationOn_real (imCLM.integrable_comp hg1)
      (imCLM.lipschitz.comp_boundedVariationOn hg2))

lemma tendsto_zero_atBot_of_integrable_boundedVariationOn_complex
    {g : ℝ → ℂ} (hg1 : Integrable g) (hg2 : BoundedVariationOn g .univ) :
    atBot.Tendsto g (nhds 0) :=
  tendsto_complex_zero_of_re_im
    (tendsto_zero_atBot_of_integrable_boundedVariationOn_real (reCLM.integrable_comp hg1)
      (reCLM.lipschitz.comp_boundedVariationOn hg2))
    (tendsto_zero_atBot_of_integrable_boundedVariationOn_real (imCLM.integrable_comp hg1)
      (imCLM.lipschitz.comp_boundedVariationOn hg2))

theorem tendsto_fourier_boundary_zero
    {g : ℝ → ℂ} (hg1 : MeasureTheory.Integrable g)
    (hg2 : BoundedVariationOn g .univ) (ξ : ℝ) :
    atTop.Tendsto
      (fun R ↦ g R * E ξ R - g (-R) * E ξ (-R))
      (nhds 0) :=
  tendsto_fourier_boundary_zero_of_tendsto
    (tendsto_zero_atTop_of_integrable_boundedVariationOn_complex hg1 hg2)
    (tendsto_zero_atBot_of_integrable_boundedVariationOn_complex hg1 hg2) ξ

lemma integrable_e_mul
    {g : ℝ → ℂ} (hg : Integrable g) (ξ : ℝ) :
    Integrable (fun x : ℝ ↦ e ξ x * g x) volume := by
    refine hg.congr' (AEStronglyMeasurable.mul (by fun_prop) hg.1) ?_
    filter_upwards with a
    simp only [e, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_mul]

theorem tendsto_interval_e_integral
    {g : ℝ → ℂ} (hg1 : MeasureTheory.Integrable g) (ξ : ℝ) :
    atTop.Tendsto (fun R : ℝ ↦ ∫ x in (-R)..R, (e ξ x) * g x)
      (nhds (𝓕 g ξ)) := by
  have hb : 𝓕 g ξ = ∫ x : ℝ, e ξ x * g x := by
    simp [Real.fourier_real_eq_integral_exp_smul, e]
  simpa [hb] using intervalIntegral_tendsto_integral (integrable_e_mul hg1 ξ)
      (tendsto_neg_atTop_atBot) fun ⦃_⦄ a ↦ a

theorem fourier_tendsto_stieltjesPrimitive_of_boundedVariation
    {g : ℝ → ℂ} (hg1 : Integrable g) (hg2 : BoundedVariationOn g .univ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ L, atTop.Tendsto (fun R ↦ ∫⟨mul ℝ ℂ⟩ x in -R..R, (E ξ x) ∂g)
        (nhds L) ∧
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
      (tendsto_fourier_boundary_zero hg1 hg2 ξ).sub (tendsto_interval_e_integral hg1 ξ))
  refine ⟨hS_tendsto, by simp,
    (isClosed_le continuous_norm continuous_const).mem_of_tendsto hS_tendsto ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
  grw [norm_stieltjesIntegral_E_le ξ (by linarith) (hb R),
    ENNReal.toReal_mono hg2 (eVariationOn.mono g fun ⦃_⦄ _ ↦ trivial)]

lemma fourier_bounded_variation
    {g : ℝ → ℂ} (hg1 : Integrable g) (hg2 : BoundedVariationOn g .univ) :
    ∀ (ξ : ℝ), ξ ≠ 0 →
      ‖𝓕 g ξ‖ ≤ |ξ|⁻¹ * (Real.pi⁻¹ * 2⁻¹) * (eVariationOn g .univ).toReal := by
  intro ξ hξ
  obtain ⟨L, _, hb, hc⟩ := fourier_tendsto_stieltjesPrimitive_of_boundedVariation hg1 hg2 hξ
  simpa [hb] using hc

end
end FourierStieltjes


-- The old proof of `hasStieltjesIntegral_E`, given below,
-- could be useful to prove `integral_of_derivative`.

-- lemma integrableOn_Icc_of_boundedVariationOn_real {f : ℝ → ℝ}
--     (hf : BoundedVariationOn f (.Icc a b)) : IntegrableOn f (.Icc a b) := by
--   rcases hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn with ⟨p, q, hp, hq, rfl⟩
--   exact (hp.integrableOn_isCompact isCompact_Icc).sub (hq.integrableOn_isCompact isCompact_Icc)

-- lemma integrableOn_Icc_of_boundedVariationOn_complex {g : ℝ → ℂ}
--     (hg : BoundedVariationOn g (.Icc a b)) : IntegrableOn g (.Icc a b) := by
--   unfold IntegrableOn; rw [← Integrable.re_im_iff]; constructor
--   · simpa using
--       integrableOn_Icc_of_boundedVariationOn_real (reCLM.lipschitz.comp_boundedVariationOn hg)
--   · simpa using
--       integrableOn_Icc_of_boundedVariationOn_real (imCLM.lipschitz.comp_boundedVariationOn hg)

-- lemma intervalIntegrable_e_mul_of_boundedVariationOn
--     (g : ℝ → ℂ) (hab : a ≤ b) (hg : BoundedVariationOn g (Set.Icc a b)) (ξ : ℝ) :
--     IntervalIntegrable (fun x : ℝ ↦ e ξ x * g x) volume a b := by
--   rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
--   exact (integrableOn_Icc_of_boundedVariationOn_complex hg).continuousOn_mul
--     (by unfold e; fun_prop) isCompact_Icc

-- lemma norm_fourier_stieltjes_subinterval_error_le
--     {g : ℝ → ℂ} {u v τ : ℝ} (huv : u ≤ v) (hτ : τ ∈ Set.Icc u v)
--     (hg : BoundedVariationOn g (.Icc u v)) {ξ : ℝ} (hξ : ξ ≠ 0) :
--     ‖(E ξ v - E ξ u) * g τ -
--         ∫ x in u..v, e ξ x * g x‖ ≤
--       (eVariationOn g (.Icc u v)).toReal * (v - u) := by
--   set V : ℝ := (eVariationOn g (.Icc u v)).toReal
--   have hKgint : IntervalIntegrable (fun x : ℝ ↦ e ξ x * g x) volume u v :=
--       intervalIntegrable_e_mul_of_boundedVariationOn g huv hg ξ
--   have hKconstint : IntervalIntegrable (fun x : ℝ ↦ e ξ x * g τ) volume u v :=
--       Continuous.intervalIntegrable (by fun_prop) u v
--   have hrewrite :
--       (E ξ v - E ξ u) * g τ -
--           ∫ x in u..v, e ξ x * g x =
--         ∫ x in u..v, e ξ x * (g τ - g x) := by
--     rw [← intervalIntegral_e_eq_primitive_sub hξ,
--       ← intervalIntegral.integral_mul_const, ← integral_sub hKconstint hKgint]
--     congr with x; ring
--   rw [hrewrite]
--   have hpoint : ∀ x ∈ Set.uIoc u v, ‖e ξ x * (g τ - g x)‖ ≤ V := by
--     intros
--     grw [norm_mul_le]
--     simpa [V, dist_eq_norm, norm_e] using BoundedVariationOn.dist_le hg hτ (by grind)
--   have habs : |v - u| = v - u := by simp [huv]
--   simpa [V, habs] using norm_integral_le_of_norm_le_const hpoint

-- lemma scalar_iUnion_boxes_eq_Ioc (hab : a < b)
--     {π : TaggedPrepartition (Ioc a b)} (hπ : π.IsPartition) :
--     ⋃ J ∈ π.boxes, J.toSet₁ = Set.Ioc a b := by
--   ext x; simp only [mem_boxes, mem_toPrepartition, Box.toSet₁_def, Set.mem_iUnion, Set.mem_Ioc,
--     exists_and_left, exists_prop]
--   refine ⟨ fun ⟨ J, _, hJ, _ ⟩ ↦ ?_, fun h ↦ ?_ ⟩
--   · have := π.le_of_mem hJ
--     simp [Box.le_iff₁, hab] at this; grind
--   obtain ⟨J, _, _⟩ := hπ (fun _ ↦ x) (by simpa [hab] using h)
--   use J; simp_all

-- lemma intervalIntegral_eq_sum_partition_integrals
--     {g : ℝ → ℂ} (hab : a < b) (hg : BoundedVariationOn g (Set.Icc a b))
--     (ξ : ℝ) {π : TaggedPrepartition (Ioc a b)} (hπ : π.IsPartition) :
--     (∫ x in a..b, e ξ x * g x) =
--       ∑ J ∈ π.boxes, ∫ x in J.lower₁..J.upper₁, e ξ x * g x := by
--   rw [intervalIntegral.integral_of_le hab.le, ← scalar_iUnion_boxes_eq_Ioc hab hπ,
--     integral_biUnion_finset _ (by measurability)]
--   · exact Finset.sum_congr rfl (fun x _ ↦
--       by simp [Box.toSet₁, ← intervalIntegral.integral_of_le x.lower_le_upper₁])
--   · exact fun J h1 K h3 h4 ↦ disjoint_Ioc_of_disjoint_box (π.disjoint_coe_of_mem h1 h3 h4)
--   intro J hJ
--   have : a ≤ J.lower₁ ∧ J.upper₁ ≤ b := by simpa [hab, Box.le_iff₁] using π.le_of_mem hJ
--   exact (intervalIntegrable_iff_integrableOn_Ioc_of_le J.lower_le_upper₁).1
--     (intervalIntegrable_e_mul_of_boundedVariationOn
--     g J.lower_le_upper₁ (hg.mono (by grind)) ξ)


-- theorem hasStieltjesIntegral_E
--     {g : ℝ → ℂ} (hab : a < b) {ξ : ℝ} (hξ : ξ ≠ 0)
--     (hg : RiemannIntegrable a b g) :
--     HasStieltjesIntegral a b (mul ℝ ℂ).flip g (E ξ)
--       (∫ x in a..b, e ξ x * g x) := by
  -- rw [HasStieltjesIntegral.of_lt _ _ _ _ hab]
  -- refine BoxIntegral.hasIntegral_iff.2 fun ε hε ↦ ?_
  -- let V : ℝ := (eVariationOn g (.Icc a b)).toReal
  -- let ρ : ℝ := ε / (4 * (V + 1))
  -- have hV_nonneg : 0 ≤ V := ENNReal.toReal_nonneg
  -- have hρ : 0 < ρ := by
  --   simp [hε, ρ]
  --   linarith
  -- let r : NNReal → (Fin 1 → ℝ) → (Set.Ioi (0 : ℝ)) :=
  --   fun (_ : NNReal) (_ : (Fin 1→ ℝ)) ↦ ⟨ρ, hρ⟩
  -- use r
  -- constructor
  -- · intro c hc' x
  --   rfl
  -- · intro c π hπ hpart
  --   let P : ℝ → ℂ := E ξ
  --   let K : ℝ → ℂ := e ξ
  --   let H : ℝ → ℂ := fun x ↦ K x * g x
  --   let vol : (Fin 1) →ᵇᵃ ℂ →L[ℝ] ℂ :=
  --     BoxAdditiveMap.ofDiff (fun x ↦ ((mul ℝ ℂ).flip).flip (P x))
  --   let term : Box (Fin 1) → ℂ := fun J ↦
  --     (P (J.upper 0) - P (J.lower 0)) * g ((π.tag J) 0) -
  --       ∫ x in J.lower 0..J.upper 0, H x
  --   have hsumInt :
  --       (∫ x in a..b, H x) =
  --         ∑ J ∈ π.boxes, ∫ x in J.lower 0..J.upper 0, H x := by
  --     simpa [H, K] using
  --       intervalIntegral_eq_sum_partition_integrals hab hg ξ hpart
  --   have hdiff :
  --       integralSum (fun x : Fin 1 → ℝ ↦ g (x 0)) vol π -
  --           ∫ x in a..b, H x =
  --         ∑ J ∈ π.boxes, term J := by
  --     unfold term integralSum H
  --     unfold vol
  --     simp only [flip_mul, BoxAdditiveMap.ofDiff_apply, Fin.isValue, coe_sub', Pi.sub_apply,
  --       mul_apply', Finset.sum_sub_distrib]
  --     rw [hsumInt]
  --     unfold H
  --     simp [sub_mul, Finset.sum_sub_distrib, Box.upper₁, Box.lower₁]
  --   have hlen : ∀ J ∈ π.boxes, J.upper 0 - J.lower 0 ≤ 2 * ρ := by
  --     intro J hJ
  --     have hJmem : J ∈ π := by
  --       apply hJ
  --     have ha : dist (J.lower) (π.tag J) ≤ ρ := by
  --       have hmem' : J.lower ∈ Metric.closedBall (π.tag J) ↑(r c (π.tag J)) :=
  --         hπ.isSubordinate J hJ (Box.lower_mem_Icc J)
  --       exact hmem'
  --     have hb : dist (π.tag J) (J.upper) ≤ ρ := by
  --       have hmem'' : J.upper ∈ Metric.closedBall (π.tag J) ↑(r c (π.tag J)):=
  --         hπ.isSubordinate J hJ (Box.upper_mem_Icc J)
  --       exact Metric.mem_closedBall'.mp hmem''
  --     have hc : dist (J.lower 0) ((π.tag J) 0) ≤ ρ := by
  --       exact le_of_max_le_left ha
  --     have hd : dist ((π.tag J) 0) (J.upper 0) ≤ ρ := by
  --       exact le_of_max_le_left hb
  --     have hdist : dist (J.lower 0) (J.upper 0) ≤ 2 * ρ := by
  --       calc
  --         dist (J.lower 0) (J.upper 0) ≤ (dist (J.lower 0) ((π.tag J) 0))
  --           + (dist ((π.tag J) 0) (J.upper 0)) := by apply dist_triangle _ _ _
  --         _ ≤ ρ + ρ := by linarith [hc, hd]
  --         _ = 2 * ρ := by ring
  --     calc
  --       (J.upper 0 - J.lower 0) ≤ |J.upper 0 - J.lower 0| := by
  --         exact le_abs_self (J.upper 0 - J.lower 0)
  --       _ ≤ dist (J.lower 0) (J.upper 0) := by
  --                   simp [Real.dist_eq, abs_sub_comm]
  --       _ ≤ 2 * ρ := by linarith [hdist]
  --   have hterm : ∀ J ∈ π.boxes,
  --       ‖term J‖ ≤
  --         2 * ρ * (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal := by
  --     intro J hJ
  --     have htagJ := hπ.isHenstock rfl J hJ
  --     have hτ : (π.tag J) 0 ∈ Set.Icc (J.lower 0) (J.upper 0) :=
  --       ⟨htagJ.1 0, htagJ.2 0⟩
  --     have hgJ : BoundedVariationOn g (Set.Icc (J.lower 0) (J.upper 0)) :=
  --       hg.mono (Icc_subset_of_box_le_Ioc hab (π.le_of_mem hJ))
  --     have hbase : ‖(E ξ (J.upper 0) -
  --       E ξ (J.lower 0)) * g (π.tag J 0) -
  --       ∫ (x : ℝ) in J.lower 0..J.upper 0, e ξ x * g x‖ ≤
  -- (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal * (J.upper 0 - J.lower 0)
  --   := norm_fourier_stieltjes_subinterval_error_le
  --       (g := g) (u := J.lower 0) (v := J.upper 0) (τ := (π.tag J) 0)
  --       (J.lower_le_upper 0) hτ hgJ hξ
  --     calc
  --       _ ≤ (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal *
  --             (J.upper 0 - J.lower 0) := by
  --         unfold term P H K
  --         apply hbase
  --       _ ≤ (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal * (2 * ρ) :=
  --           mul_le_mul_of_nonneg_left (hlen J hJ) ENNReal.toReal_nonneg
  --       _ = _ := by ring
  --   have hvarsum :
  --       ∑ J ∈ π.boxes, (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal ≤ V := by
  --     unfold V
  --     apply sum_eVariationOn_Icc_toReal_le_eVariationOn (a := a) (b := b) g hab hg
  --       π.toPrepartition
  --   have hv : 2 * ρ * V ≤ ε := by
  --     unfold ρ
  --     calc
  --       _ = ε * (1/2) * (V / (V + 1)) := by
  --         field_simp [show V + 1 ≠ 0 by linarith]
  --         ring
  --       _ ≤ ε * (V / (V + 1)) := by
  --         have hA : 0 ≤ (V / (V + 1)) := by positivity
  --         nlinarith [hA, hε]
  --       _ ≤ ε * 1 := by
  --         refine (mul_le_mul_iff_of_pos_left hε).mpr ?_
  --         have h' : 0 < V + 1 := by positivity
  --         rw [div_le_iff₀ h']
  --         simp
  --       _ = ε := by ring
  --   calc
  --     dist (integralSum (fun x : Fin 1 → ℝ ↦ g (x 0)) vol π)
  --         (∫ x in a..b, H x)
  --         = ‖∑ J ∈ π.boxes, term J‖ := by
  --       simp [dist_eq_norm, ← hdiff]
  --     _ ≤ ∑ J ∈ π.boxes, ‖term J‖ := norm_sum_le _ _
  --     _ ≤ ∑ J ∈ π.boxes,
  --         2 * ρ * (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal :=
  --       Finset.sum_le_sum hterm
  --     _ = 2 * ρ *
  --         (∑ J ∈ π.boxes, (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal) := by
  --       rw [Finset.mul_sum]
  --     _ ≤ 2 * ρ * V := by
  --         simp [hvarsum, hρ]
  --     _ ≤ ε := hv
