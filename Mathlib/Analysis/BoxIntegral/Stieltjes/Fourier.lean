/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Fourier transform estimates via the Riemann–Stieltjes integral

In this file we obtain estimates on Fourier transforms via the Riemann–Stieltjes integral
`∫⟨B⟩ x in a..b, f x ∂g` defined in `Analysis.BoxIntegral.Stieltjes.Defs`.

-/

@[expose] public section

open BoxIntegral
open ContinuousLinearMap TaggedPrepartition Metric
open Prepartition hiding mem_mk
open Finset hiding Ioc mem_mk
open Fin hiding zero_lt_one

-- TODO: find a namespace

section FourierStieltjes

open scoped FourierTransform
open Filter Complex
open MeasureTheory

variable {a b : ℝ}

noncomputable def fourierKernel (ξ : ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I)


noncomputable def fourierStieltjesPrimitive (ξ : ℝ) (x : ℝ) : ℂ :=
  (-(2 * Real.pi * Complex.I * (ξ : ℂ)))⁻¹ * fourierKernel ξ x

@[simp]
lemma norm_fourierKernel (ξ x : ℝ) : ‖fourierKernel ξ x‖ = 1 := by
  unfold fourierKernel
  apply Complex.norm_exp_ofReal_mul_I

@[fun_prop]
lemma continuous_fourierKernel (ξ : ℝ) : Continuous (fourierKernel ξ) := by
  unfold fourierKernel
  fun_prop

@[fun_prop]
lemma continuous_fourierStieltjesPrimitive (ξ : ℝ) :
    Continuous (fourierStieltjesPrimitive ξ) := by
  unfold fourierStieltjesPrimitive
  fun_prop

noncomputable section

lemma hasDerivAt_fourierKernel (ξ x : ℝ) :
    HasDerivAt (fourierKernel ξ) /-Note that fourierKernel ξ is a definition-/
      (fourierKernel ξ x * ((↑(-2 * Real.pi * ξ) : ℂ) * Complex.I)) x := by
  unfold fourierKernel
  have ha : HasDerivAt (fun (x:ℝ) => (-2 * Real.pi * x :ℝ)) (-2*Real.pi : ℝ) x := by
    convert (hasDerivAt_const x ((-2 * Real.pi):ℝ)).mul (hasDerivAt_id x) using 1
    simp
  have h1 : HasDerivAt (fun (x:ℝ) => (-2 * Real.pi * x * ξ :ℝ)) (-2*Real.pi*ξ : ℝ) x := by
    convert ha.mul (hasDerivAt_const x (ξ:ℝ)) using 1
    simp
  have h2 : HasDerivAt (fun (x:ℝ) => (((-2 * Real.pi * x * ξ) :ℝ):ℂ)) ((-2*Real.pi*ξ : ℝ) : ℂ) x := by
    exact HasDerivAt.ofReal_comp h1
  have h3 : HasDerivAt (fun y : ℝ => (↑(-2 * Real.pi * y * ξ) * Complex.I)) (↑(-2 * Real.pi * ξ) * Complex.I) x := by
    exact HasDerivAt.mul_const h2 I
  exact h3.cexp



lemma fourierStieltjes_den_ne_zero (ξ : ℝ) (hξ : ξ ≠ 0) :
    (-(2 * Real.pi * Complex.I * (ξ : ℂ)) : ℂ) ≠ 0 := by
  norm_num
  apply hξ

lemma hasDerivAt_fourierStieltjesPrimitive (ξ x : ℝ) (hξ : ξ ≠ 0) :
    HasDerivAt (fourierStieltjesPrimitive ξ) (fourierKernel ξ x) x := by
  unfold fourierStieltjesPrimitive
  convert (hasDerivAt_const x ((-(2 * ↑Real.pi * I * ↑ξ))⁻¹ : ℂ)).mul (hasDerivAt_fourierKernel ξ x) using 1
  unfold fourierKernel
  field_simp [hξ, Real.pi_ne_zero, Complex.I_ne_zero]
  simp





theorem intervalIntegral_fourierKernel_eq_primitive_sub (ξ : ℝ) (hξ : ξ ≠ 0) :
    (∫ x in a..b, fourierKernel ξ x) =
      fourierStieltjesPrimitive ξ b - fourierStieltjesPrimitive ξ a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
  intro x hx
  apply (hasDerivAt_fourierStieltjesPrimitive ξ x)
  apply hξ
  apply (continuous_fourierKernel ξ).intervalIntegrable a b

lemma norm_fourierStieltjesPrimitive (ξ x : ℝ) :
    ‖fourierStieltjesPrimitive ξ x‖ =
      ‖((2 * Real.pi * Complex.I * (ξ : ℂ))⁻¹ : ℂ)‖ := by
  unfold fourierStieltjesPrimitive
  simp


lemma norm_fourier_denominator (ξ : ℝ) :
    ‖(2 * Real.pi * Complex.I * (ξ : ℂ) : ℂ)‖ = 2 * Real.pi * ‖ξ‖ := by
  calc
    ‖(2 * Real.pi * Complex.I * (ξ : ℂ) : ℂ)‖ = 2 * ‖Real.pi‖ * 1 * ‖ξ‖ := by aesop
    _ = 2 * Real.pi * 1 * ‖ξ‖ := by simp [abs_of_pos Real.pi_pos]
    _ = 2 * Real.pi * ‖ξ‖ := by ring

lemma norm_fourierStieltjesPrimitive_eq_inv_freq (ξ x : ℝ) :
    ‖fourierStieltjesPrimitive ξ x‖ = 1 / (2 * Real.pi * ‖ξ‖) := by
  rw [norm_fourierStieltjesPrimitive]
  simp
  left
  exact Real.pi_nonneg

lemma isBoundedUnder_norm_fourierStieltjesPrimitive_atTop (ξ : ℝ) (hξ : ξ ≠ 0)
    (φ : ℝ → ℝ) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun R : ℝ => ‖fourierStieltjesPrimitive ξ (φ R)‖) := by
  refine Filter.isBoundedUnder_of_eventually_le
    (a := 1 / (2 * Real.pi * ‖ξ‖)) ?_
  filter_upwards
  intro a
  simp [norm_fourierStieltjesPrimitive_eq_inv_freq ξ (φ a)]


/-- Finite-interval Stieltjes estimate for the Fourier antiderivative. -/
theorem norm_stieltjesIntegral_fourierStieltjesPrimitive_le
    (g : ℝ → ℂ) (hab : a < b) (hg : BoundedVariationOn g (Set.Icc a b)) (ξ : ℝ) :
    ‖stieltjesIntegral a b (mul ℝ ℂ) (fourierStieltjesPrimitive ξ) g‖ ≤
      ‖((2 * Real.pi * Complex.I * (ξ : ℂ))⁻¹ : ℂ)‖ *
        (eVariationOn g (Set.Icc a b)).toReal := by
  let C : ℝ := ‖((2 * Real.pi * Complex.I * (ξ : ℂ))⁻¹ : ℂ)‖
  let V : ℝ := (eVariationOn g (Set.Icc a b)).toReal
  let integralUntil : ℝ → ℝ := fun x => (eVariationOn g (Set.Icc a x)).toReal
  have hInt : StieltjesIntegrable a b (mul ℝ ℂ) (fourierStieltjesPrimitive ξ) g := by
    exact exists_of_continuousOn_of_boundedVariationOn
      (B := mul ℝ ℂ) hab (continuous_fourierStieltjesPrimitive ξ).continuousOn hg
  have hfg :
      HasStieltjesIntegral a b (mul ℝ ℂ) (fourierStieltjesPrimitive ξ) g
        (stieltjesIntegral a b (mul ℝ ℂ) (fourierStieltjesPrimitive ξ) g) := by
    simpa [hInt.hasStieltjesIntegral.stieltjesIntegral_eq] using hInt.hasStieltjesIntegral
  have hintegralUntil_a : integralUntil a = 0 := by
    unfold integralUntil
    simp
  have hfabs :
      HasStieltjesIntegral a b (mul ℝ ℝ) (fun x ↦ ‖fourierStieltjesPrimitive ξ x‖)
        integralUntil (C * V) := by
    have hconst : HasStieltjesIntegral a b (mul ℝ ℝ) (fun _ : ℝ ↦ C) integralUntil
        ((mul ℝ ℝ) C (integralUntil b) - (mul ℝ ℝ) C (integralUntil a)) :=
      HasStieltjesIntegral.of_const (B := mul ℝ ℝ) (a := a) (b := b) C integralUntil
    convert hconst using 1
    unfold C fourierStieltjesPrimitive
    simp
    simp [C, V, integralUntil, hintegralUntil_a, mul_comm, mul_left_comm, mul_assoc]
  have hmain := by
    have h1' := integral_le_integral_of_variation (a := a) (b := b) (B := mul ℝ ℂ)
      (f := fourierStieltjesPrimitive ξ) (g := g)
      (L := stieltjesIntegral a b (mul ℝ ℂ) (fourierStieltjesPrimitive ξ) g)
      (L' := C * V)
    apply h1' hab hg hfg hfabs
  have hmul : ‖(mul ℝ ℂ)‖ ≤ (1 : ℝ) := by
    exact opNorm_mul_le ℝ ℂ
  have hCV_nonneg : 0 ≤ C * V := by
    have h1' : 0 ≤ C := norm_nonneg _
    have h2' : 0 ≤ V := ENNReal.toReal_nonneg
    apply mul_nonneg h1' h2'
  calc
    ‖stieltjesIntegral a b (mul ℝ ℂ) (fourierStieltjesPrimitive ξ) g‖
        ≤ ‖(mul ℝ ℂ)‖ * (C * V) := hmain
    _ ≤ 1 * (C * V) := mul_le_mul_of_nonneg_right hmul hCV_nonneg
    _ = C * V := by ring


lemma integrableOn_Icc_of_boundedVariationOn_real {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc a b)) :
    MeasureTheory.IntegrableOn f (Set.Icc a b) := by
  have ha : LocallyBoundedVariationOn f (Set.Icc a b) := hf.locallyBoundedVariationOn
  rcases ha.exists_monotoneOn_sub_monotoneOn with ⟨p, q, hp, hq, hpq⟩
  rw [hpq]
  have h1 : MeasureTheory.IntegrableOn p (Set.Icc a b) := by
    apply hp.integrableOn_isCompact isCompact_Icc
  have h2 : MeasureTheory.IntegrableOn q (Set.Icc a b) := by
    apply hq.integrableOn_isCompact isCompact_Icc
  apply h1.sub h2


lemma integrableOn_Icc_of_boundedVariationOn_complex {g : ℝ → ℂ}
    (hg : BoundedVariationOn g (Set.Icc a b)) :
    MeasureTheory.IntegrableOn g (Set.Icc a b) := by
  unfold MeasureTheory.IntegrableOn
  rw [← MeasureTheory.Integrable.re_im_iff]
  constructor
  · simpa using
      integrableOn_Icc_of_boundedVariationOn_real (a := a) (b := b)
        (f := Complex.reCLM ∘ g) (Complex.reCLM.lipschitz.comp_boundedVariationOn hg)
  · simpa using
      integrableOn_Icc_of_boundedVariationOn_real (a := a) (b := b)
        (f := Complex.imCLM ∘ g) (Complex.imCLM.lipschitz.comp_boundedVariationOn hg)





lemma intervalIntegrable_fourierKernel_mul_of_boundedVariationOn
    (g : ℝ → ℂ) (hab : a ≤ b) (hg : BoundedVariationOn g (Set.Icc a b)) (ξ : ℝ) :
    IntervalIntegrable (fun x : ℝ ↦ fourierKernel ξ x * g x)
      MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have ha : MeasureTheory.IntegrableOn g (Set.Icc a b) :=
    integrableOn_Icc_of_boundedVariationOn_complex (a := a) (b := b) hg
  refine ha.continuousOn_mul ?_ ?_
  unfold fourierKernel
  fun_prop
  exact isCompact_Icc


lemma norm_fourier_stieltjes_subinterval_error_le
    (g : ℝ → ℂ) {u v τ : ℝ} (huv : u ≤ v) (hτ : τ ∈ Set.Icc u v)
    (hg : BoundedVariationOn g (Set.Icc u v)) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖(fourierStieltjesPrimitive ξ v - fourierStieltjesPrimitive ξ u) * g τ -
        ∫ x in u..v, fourierKernel ξ x * g x‖ ≤
      (eVariationOn g (Set.Icc u v)).toReal * (v - u) := by
  let V : ℝ := (eVariationOn g (Set.Icc u v)).toReal
  have hKgint :
      IntervalIntegrable (fun x : ℝ ↦ fourierKernel ξ x * g x)
        MeasureTheory.volume u v := by apply
    intervalIntegrable_fourierKernel_mul_of_boundedVariationOn (a := u) (b := v) g huv hg ξ
  have hKconstint :
      IntervalIntegrable (fun x : ℝ ↦ fourierKernel ξ x * g τ)
        MeasureTheory.volume u v := by
      apply ((continuous_fourierKernel ξ).mul (continuous_const)).intervalIntegrable u v
  have hrewrite :
      (fourierStieltjesPrimitive ξ v - fourierStieltjesPrimitive ξ u) * g τ -
          ∫ x in u..v, fourierKernel ξ x * g x =
        ∫ x in u..v, fourierKernel ξ x * (g τ - g x) := by
    rw [← intervalIntegral_fourierKernel_eq_primitive_sub (a := u) (b := v) ξ hξ]
    rw [← intervalIntegral.integral_mul_const (r := g τ)
      (f := fun x : ℝ ↦ fourierKernel ξ x)]
    rw [← intervalIntegral.integral_sub hKconstint hKgint]
    congr with x
    ring
  rw [hrewrite]
  have hpoint : ∀ x ∈ Set.uIoc u v, ‖fourierKernel ξ x * (g τ - g x)‖ ≤ V := by
    intro x hx
    have hxIoc : x ∈ Set.Ioc u v := by
      rw[← Set.uIoc_of_le huv]
      apply hx
    have hxIcc : x ∈ Set.Icc u v := by
      unfold Set.Icc
      rcases hxIoc with ⟨hxIoc1,hxIoc2⟩
      constructor
      exact le_of_lt hxIoc1
      exact hxIoc2
    have hdist := BoundedVariationOn.dist_le hg hτ hxIcc
    calc
      ‖fourierKernel ξ x * (g τ - g x)‖ ≤ ‖fourierKernel ξ x‖ * ‖g τ - g x‖ :=
        norm_mul_le _ _
      _ = ‖g τ - g x‖ := by simp [norm_fourierKernel]
      _ ≤ V := by
        unfold V
        rw[dist_eq_norm] at hdist
        apply hdist
  have hbound : ‖∫ (x : ℝ) in u..v, (fun x ↦ fourierKernel ξ x * (g τ - g x)) x‖ ≤ V * |v - u|  :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := u) (b := v) (C := V)
      (f := fun x : ℝ ↦ fourierKernel ξ x * (g τ - g x)) hpoint
  have habs : |v - u| = v - u := by
    simp [huv]
  unfold V at hbound
  rw [habs] at hbound
  apply hbound

lemma scalar_iUnion_boxes_eq_Ioc (hab : a < b)
    (π : TaggedPrepartition (Ioc a b)) (hπ : π.IsPartition) :
    (⋃ J ∈ π.boxes, Set.Ioc (J.lower 0) (J.upper 0)) = Set.Ioc a b := by
  ext x
  constructor
  intro h
  refine Set.mem_Ioc.mpr ?_
  rcases Set.mem_iUnion.1 h with ⟨J,hJ⟩
  -- J is a one-dimensional interval
  rcases Set.mem_iUnion.1 hJ with ⟨h1,h2c⟩
  let J1 := J.lower 0
  let J2 := J.upper 0
  have h2 : x ∈ Set.Ioc J1 J2 := by
    simpa [J1,J2] using h2c
  -- J' is a re-interpretation of J as a subset of ℝ in some sense
  have h1' : (fun (_ : Fin 1) => x) ∈ (J : Set (Fin 1 → ℝ)) := by
    simp
    simpa [Box.mem_def, Fin.forall_fin_one] using h2c
  have h2' : (fun (_ : Fin 1) => x) ∈ (Ioc a b : Set (Fin 1 → ℝ)) := by
    have hint : (J : Set (Fin 1 → ℝ)) ⊆ (Ioc a b : Set (Fin 1 → ℝ)) := by
      simp
      refine π.le_of_mem ?_
      simp
      apply h1
    apply hint h1'
  have hc := by
    simpa [Box.mem_def, Fin.forall_fin_one, Ioc.lower hab, Ioc.upper hab] using h2'
  constructor
  apply hc.left
  apply hc.right
  intro h
  have h1 : (fun _ : Fin 1 => x) ∈ (Ioc a b : Set (Fin 1 → ℝ)) := by
    simp
    simpa [Box.mem_def, Fin.forall_fin_one, Ioc.lower hab, Ioc.upper hab]
  rcases hπ (fun _ : Fin 1 => x) h1 with ⟨w,ha,hb⟩
  simp at *
  use w
  have hbw : w.lower 0 < x ∧ x ≤ w.upper 0 := by
    simpa [Box.mem_def, Fin.forall_fin_one] using hb
  constructor
  apply hbw.1
  constructor
  apply ha
  apply hbw.2

lemma intervalIntegral_eq_sum_partition_integrals
    (g : ℝ → ℂ) (hab : a < b) (hg : BoundedVariationOn g (Set.Icc a b))
    (ξ : ℝ) (π : TaggedPrepartition (Ioc a b)) (hπ : π.IsPartition) :
    (∫ x in a..b, fourierKernel ξ x * g x) =
      ∑ J ∈ π.boxes, ∫ x in J.lower 0..J.upper 0, fourierKernel ξ x * g x := by
  have hpair :
      Set.Pairwise (↑π.boxes)
        (Function.onFun Disjoint fun J : Box (Fin 1) =>
          Set.Ioc (J.lower 0) (J.upper 0)) := by
          intro J h1 K h3 h4
          refine disjoint_Ioc_of_disjoint_box ?_
          apply (π.disjoint_coe_of_mem h1 h3 h4)
  have hint : ∀ J ∈ π.boxes,
      MeasureTheory.IntegrableOn (fun x : ℝ => fourierKernel ξ x * g x)
        (Set.Ioc (J.lower 0) (J.upper 0)) MeasureTheory.volume := by
    intro J hJ
    have hgJ : BoundedVariationOn g (Set.Icc (J.lower 0) (J.upper 0)) := by
      refine hg.mono ?_
      have ha' : a ≤ J.lower 0 ∧ J.upper 0 ≤ b := by
        have hJle : J ≤ Ioc a b := π.le_of_mem hJ
        constructor
        · simpa [Ioc.lower hab] using Box.antitone_lower hJle 0
        · simpa [Ioc.upper hab] using Box.monotone_upper hJle 0
      refine Set.Icc_subset_Icc ?_ ?_
      apply ha'.1
      apply ha'.2
    have hJint := intervalIntegrable_fourierKernel_mul_of_boundedVariationOn
      (a := J.lower 0) (b := J.upper 0) g (J.lower_le_upper 0) hgJ ξ
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (J.lower_le_upper 0)).1 hJint
  rw [intervalIntegral.integral_of_le hab.le]
  rw [← scalar_iUnion_boxes_eq_Ioc hab π hπ]
  rw [integral_biUnion_finset]
  refine Finset.sum_congr ?_ ?_
  rfl
  intro x hx
  rw[← intervalIntegral.integral_of_le]
  refine x.lower_le_upper 0
  intro i hi
  exact measurableSet_Ioc
  exact hpair
  exact hint


/-- If the integrator is the Fourier primitive, the Stieltjes integral is the ordinary integral
against its derivative, here specialized to the Fourier kernel. -/
theorem hasStieltjesIntegral_fourierStieltjesPrimitive
    (g : ℝ → ℂ) (hab : a < b) (ξ : ℝ) (hξ : ξ ≠ 0)
    (hg : BoundedVariationOn g (Set.Icc a b)) :
    HasStieltjesIntegral a b (mul ℝ ℂ).flip g (fourierStieltjesPrimitive ξ)
      (∫ x in a..b, fourierKernel ξ x * g x) := by
  rw [HasStieltjesIntegral.of_lt (B := (mul ℝ ℂ).flip) (f := g)
    (g := fourierStieltjesPrimitive ξ) (L := ∫ x in a..b, fourierKernel ξ x * g x) hab]
  unfold HasStieltjesIntegral'
  refine BoxIntegral.hasIntegral_iff.2 fun ε hε ↦ ?_
  let V : ℝ := (eVariationOn g (Set.Icc a b)).toReal
  let ρ : ℝ := ε / (4 * (V + 1))
  have hV_nonneg : 0 ≤ V := ENNReal.toReal_nonneg
  have hρ : 0 < ρ := by
    simp [hε, ρ]
    linarith
  let r : NNReal → (Fin 1 → ℝ) → (Set.Ioi (0 : ℝ)) :=
    fun (_ : NNReal) (_ : (Fin 1→ ℝ)) ↦ ⟨ρ, hρ⟩
  use r
  constructor
  · intro c hc' x
    rfl
  · intro c π hπ hpart
    let P : ℝ → ℂ := fourierStieltjesPrimitive ξ
    let K : ℝ → ℂ := fourierKernel ξ
    let H : ℝ → ℂ := fun x ↦ K x * g x
    let vol : (Fin 1) →ᵇᵃ ℂ →L[ℝ] ℂ :=
      BoxAdditiveMap.ofDiff (fun x ↦ ((mul ℝ ℂ).flip).flip (P x))
    let term : Box (Fin 1) → ℂ := fun J =>
      (P (J.upper 0) - P (J.lower 0)) * g ((π.tag J) 0) -
        ∫ x in J.lower 0..J.upper 0, H x
    have hsumInt :
        (∫ x in a..b, H x) =
          ∑ J ∈ π.boxes, ∫ x in J.lower 0..J.upper 0, H x := by
      simpa [H, K] using
        intervalIntegral_eq_sum_partition_integrals (a := a) (b := b) g hab hg ξ π hpart
    have hdiff :
        integralSum (fun x : Fin 1 → ℝ ↦ g (x 0)) vol π -
            ∫ x in a..b, H x =
          ∑ J ∈ π.boxes, term J := by
      unfold term integralSum H
      unfold vol
      simp
      rw[hsumInt]
      unfold H
      simp [sub_mul, Finset.sum_sub_distrib]
    have hlen : ∀ J ∈ π.boxes, J.upper 0 - J.lower 0 ≤ 2 * ρ := by
      intro J hJ
      have hJmem : J ∈ π := by
        apply hJ
      have ha : dist (J.lower) (π.tag J) ≤ ρ := by
        have hmem' : J.lower ∈ Metric.closedBall (π.tag J) ↑(r c (π.tag J)) := by
          refine hπ.isSubordinate J ?_ ?_
          apply hJ
          exact Box.lower_mem_Icc J
        exact hmem'
      have hb : dist (π.tag J) (J.upper) ≤ ρ := by
        have hmem'' : J.upper ∈ Metric.closedBall (π.tag J) ↑(r c (π.tag J)):= by
          refine hπ.isSubordinate J ?_ ?_
          apply hJmem
          exact Box.upper_mem_Icc J
        exact Metric.mem_closedBall'.mp hmem''
      have hc : dist (J.lower 0) ((π.tag J) 0) ≤ ρ := by
        exact le_of_max_le_left ha
      have hd : dist ((π.tag J) 0) (J.upper 0) ≤ ρ := by
        exact le_of_max_le_left hb
      have hdist : dist (J.lower 0) (J.upper 0) ≤ 2 * ρ := by
        calc
          dist (J.lower 0) (J.upper 0) ≤ (dist (J.lower 0) ((π.tag J) 0)) + (dist ((π.tag J) 0) (J.upper 0)) := by apply dist_triangle _ _ _
          _ ≤ ρ + ρ := by linarith [hc, hd]
          _ = 2 * ρ := by ring
      calc
        (J.upper 0 - J.lower 0) ≤ |J.upper 0 - J.lower 0| := by
          exact le_abs_self (J.upper 0 - J.lower 0)
        _ ≤ dist (J.lower 0) (J.upper 0) := by
                    simp [Real.dist_eq, abs_sub_comm]
        _ ≤ 2 * ρ := by linarith [hdist]
    have hterm : ∀ J ∈ π.boxes,
        ‖term J‖ ≤
          2 * ρ * (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal := by
      intro J hJ
      have htagJ := hπ.isHenstock rfl J hJ
      have hτ : (π.tag J) 0 ∈ Set.Icc (J.lower 0) (J.upper 0) :=
        ⟨htagJ.1 0, htagJ.2 0⟩
      have hgJ : BoundedVariationOn g (Set.Icc (J.lower 0) (J.upper 0)) :=
        hg.mono (Icc_subset_of_box_le_Ioc a b hab (π.le_of_mem hJ))
      have hbase : ‖(fourierStieltjesPrimitive ξ (J.upper 0) - fourierStieltjesPrimitive ξ (J.lower 0)) * g (π.tag J 0) -
      ∫ (x : ℝ) in J.lower 0..J.upper 0, fourierKernel ξ x * g x‖ ≤
  (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal * (J.upper 0 - J.lower 0) := norm_fourier_stieltjes_subinterval_error_le
        (g := g) (u := J.lower 0) (v := J.upper 0) (τ := (π.tag J) 0)
        (J.lower_le_upper 0) hτ hgJ ξ hξ
      calc
        ‖term J‖ ≤
            (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal *
              (J.upper 0 - J.lower 0) := by
          unfold term P H K
          apply hbase
        _ ≤ (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal * (2 * ρ) := by
            refine mul_le_mul_of_nonneg_left ?_ ?_
            apply hlen J
            exact hJ
            exact ENNReal.toReal_nonneg
        _ = 2 * ρ * (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal := by ring
    have hvarsum :
        ∑ J ∈ π.boxes, (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal ≤ V := by
      unfold V
      apply sum_eVariationOn_Icc_toReal_le_eVariationOn (a := a) (b := b) g hab hg π.toPrepartition
    have hv : 2 * ρ * V ≤ ε := by
      unfold ρ
      calc
        2 * (ε / (4 * (V + 1))) * V = ε * (1/2) * (V / (V + 1)) := by
          field_simp [show V + 1 ≠ 0 by linarith]
          ring
        _ ≤ ε * (V / (V + 1)) := by
          have hA : 0 ≤ (V / (V + 1)) := by positivity
          nlinarith [hA, hε]
        _ ≤ ε * 1 := by
          refine (mul_le_mul_iff_of_pos_left hε).mpr ?_
          have h' : 0 < V + 1 := by positivity
          rw [div_le_iff₀ h']
          simp
        _ = ε := by ring
    calc
      dist (integralSum (fun x : Fin 1 → ℝ ↦ g (x 0)) vol π)
          (∫ x in a..b, H x)
          = ‖∑ J ∈ π.boxes, term J‖ := by
        simp [dist_eq_norm, ← hdiff]
      _ ≤ ∑ J ∈ π.boxes, ‖term J‖ := norm_sum_le _ _
      _ ≤ ∑ J ∈ π.boxes,
          2 * ρ * (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal :=
        Finset.sum_le_sum hterm
      _ = 2 * ρ *
          (∑ J ∈ π.boxes, (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * ρ * V := by
          simp [hvarsum, hρ]
      _ ≤ ε := hv

/-- The ordinary Fourier integral over a finite interval is the Stieltjes integral against the
Fourier antiderivative, up to the boundary term supplied by integration by parts. -/
theorem interval_fourierIntegral_eq_boundary_sub_stieltjes
    (g : ℝ → ℂ) (hab : a < b) (ξ : ℝ) (hξ : ξ ≠ 0)
    (hg : BoundedVariationOn g (Set.Icc a b)) :
    (∫ x in a..b, fourierKernel ξ x * g x) =
      g b * fourierStieltjesPrimitive ξ b -
        g a * fourierStieltjesPrimitive ξ a -
          stieltjesIntegral a b (mul ℝ ℂ) (fourierStieltjesPrimitive ξ) g := by
  have hInt : StieltjesIntegrable a b (mul ℝ ℂ) (fourierStieltjesPrimitive ξ) g := by
    exact exists_of_continuousOn_of_boundedVariationOn
      (B := mul ℝ ℂ) hab (continuous_fourierStieltjesPrimitive ξ).continuousOn hg
  have hparts := stieltjesIntegral.by_parts (a := a) (b := b) (B := mul ℝ ℂ) hInt
  have hleft :
      (∫ x in a..b, fourierKernel ξ x * g x) =
        ∫⟨(mul ℝ ℂ).flip⟩ x in a..b, g x ∂ fourierStieltjesPrimitive ξ := by
    exact (hasStieltjesIntegral_fourierStieltjesPrimitive
      (a := a) (b := b) g hab ξ hξ hg).stieltjesIntegral_eq.symm
  rw [hleft]
  rw[hparts]
  simp [mul_comm]

theorem tendsto_fourier_boundary_zero_of_tendsto
    (g : ℝ → ℂ) (hg_top : Filter.Tendsto g Filter.atTop (nhds 0))
    (hg_bot : Filter.Tendsto g Filter.atBot (nhds 0)) (ξ : ℝ) (hξ : ξ ≠ 0) :
    Filter.Tendsto
      (fun R : ℝ =>
        g R * fourierStieltjesPrimitive ξ R -
          g (-R) * fourierStieltjesPrimitive ξ (-R))
      Filter.atTop (nhds 0) := by
  have htop :
      Filter.Tendsto (fun R : ℝ => g R * fourierStieltjesPrimitive ξ R)
        Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.zero_mul_isBoundedUnder_le hg_top ?_
    apply isBoundedUnder_norm_fourierStieltjesPrimitive_atTop ξ hξ id
  have hbot_zero : Filter.Tendsto (fun R : ℝ => g (-R)) Filter.atTop (nhds 0) :=
    hg_bot.comp Filter.tendsto_neg_atTop_atBot
  have hbot :
      Filter.Tendsto (fun R : ℝ => g (-R) * fourierStieltjesPrimitive ξ (-R))
        Filter.atTop (nhds 0) := by
    refine hbot_zero.zero_mul_isBoundedUnder_le ?_
    apply isBoundedUnder_norm_fourierStieltjesPrimitive_atTop ξ hξ
  simpa using htop.sub hbot

lemma tendsto_zero_atTop_of_integrable_boundedVariationOn_real
    (f : ℝ → ℝ) (hf1 : MeasureTheory.Integrable f)
    (hf2 : BoundedVariationOn f Set.univ) :
    Tendsto f atTop (nhds 0) := by
  let V : ℝ := (eVariationOn f Set.univ).toReal
  let p : ℝ → ℝ := fun x => variationOnFromTo f Set.univ 0 x
  let q : ℝ → ℝ := fun x => variationOnFromTo f Set.univ 0 x - f x
  have hloc : LocallyBoundedVariationOn f Set.univ := hf2.locallyBoundedVariationOn
  have hp_mono : Monotone p := by
    refine monotone_iff_forall_lt.mpr ?_
    intro a b h
    unfold p
    refine monotoneOn_univ.mp (variationOnFromTo.monotoneOn ?_ (?_)) ?_
    exact hloc
    exact trivial
    linarith
  have hq_mono : Monotone q := by
    refine monotoneOn_univ.mp (variationOnFromTo.sub_self_monotoneOn ?_ (?_))
    apply hloc
    exact trivial
  have hp_bound_point : ∀ x, p x ≤ V := by
    intro x
    by_cases hx : 0 ≤ x
    · unfold p V
      rw [variationOnFromTo.eq_of_le f Set.univ hx]
      refine ENNReal.toReal_mono ?_ (eVariationOn.mono f (?_))
      -- ⊤ here referes to infinity
      simpa using hf2
      exact fun ⦃a⦄ a ↦ trivial
    · unfold p V
      push_neg at hx
      have hx' : x ≤ 0 := by exact le_of_lt hx
      rw [variationOnFromTo.eq_of_ge f Set.univ hx']
      simp
      have ha : -(eVariationOn f (Set.Icc x 0)).toReal ≤ (eVariationOn f (Set.Icc x 0)).toReal := by
        have ha' : 0 ≤ (eVariationOn f (Set.Icc x 0)).toReal := by apply ENNReal.toReal_nonneg
        linarith
      calc
         -(eVariationOn f (Set.Icc x 0)).toReal ≤ (eVariationOn f (Set.Icc x 0)).toReal := by apply ha
         _ ≤ (eVariationOn f Set.univ).toReal := by
          refine ENNReal.toReal_mono ?_ (eVariationOn.mono f (?_))
          simpa using hf2
          exact fun ⦃a⦄ a ↦ trivial
  have hp_bdd : BddAbove (Set.range p) := by
    use V
    refine mem_upperBounds.mpr ?_
    simpa using hp_bound_point
  have hq_bdd : BddAbove (Set.range q) := by
    use V + (V - f 0)
    rintro y ⟨x,rfl⟩
    unfold q
    have hp : p x ≤ V := hp_bound_point x
    have hf : f 0 - f x ≤ V := by
      refine hf2.sub_le (?_) (?_)
      exact trivial
      exact trivial
    linarith
  have hp_tend : Filter.Tendsto p Filter.atTop (nhds (⨆ x, p x)) :=
    tendsto_atTop_ciSup hp_mono hp_bdd
  have hq_tend : Filter.Tendsto q Filter.atTop (nhds (⨆ x, q x)) :=
    tendsto_atTop_ciSup hq_mono hq_bdd
  have hf_tend : Filter.Tendsto f Filter.atTop (nhds ((⨆ x, p x) - (⨆ x, q x))) := by
    have hsub := hp_tend.sub hq_tend
    convert hsub using 1
    · ext x
      dsimp [p, q]
      ring
  have hzero : ((⨆ x, p x) - (⨆ x, q x)) = 0 := by
    refine MeasureTheory.IntegrableAtFilter.eq_zero_of_tendsto
        (hf1.integrableAtFilter Filter.atTop) ?_ ?_
    intro s hs
    rcases Filter.mem_atTop_sets.1 hs with ⟨b, hb⟩
    rw [← top_le_iff]
    rw[← Real.volume_Ici]
    exact MeasureTheory.measure_mono hb
    apply hf_tend
  simpa [hzero] using hf_tend

lemma tendsto_zero_atBot_of_integrable_boundedVariationOn_real
    (f : ℝ → ℝ) (hf1 : MeasureTheory.Integrable f)
    (hf2 : BoundedVariationOn f Set.univ) :
    Filter.Tendsto f Filter.atBot (nhds 0) := by
  have hcomp_int : MeasureTheory.Integrable (f ∘ Neg.neg) := by
    have hmp := MeasureTheory.Measure.measurePreserving_neg
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)
    exact (hmp.integrable_comp_emb measurableEmbedding_neg).2 hf1
  have hcomp_bv : BoundedVariationOn (f ∘ Neg.neg) Set.univ := by
    change eVariationOn (f ∘ Neg.neg) Set.univ ≠ ⊤
    rw [eVariationOn.comp_eq_of_antitoneOn f Neg.neg]
    · have himage : Set.range (Neg.neg : ℝ → ℝ) = (Set.univ : Set ℝ) := by
        ext x
        constructor
        · intro _
          trivial
        · intro _
          exact ⟨-x, by simp⟩
      simpa [himage] using hf2
    · intro x _ y _ hxy
      exact neg_le_neg hxy
  have ht := tendsto_zero_atTop_of_integrable_boundedVariationOn_real
    (f ∘ Neg.neg) hcomp_int hcomp_bv
  simpa [Function.comp_def] using ht.comp Filter.tendsto_neg_atBot_atTop

lemma tendsto_complex_zero_of_re_im {ι : Type*} {l : Filter ι} {g : ι → ℂ}
    (hre : Filter.Tendsto (Complex.reCLM ∘ g) l (nhds 0))
    (him : Filter.Tendsto (Complex.imCLM ∘ g) l (nhds 0)) :
    Filter.Tendsto g l (nhds 0) := by
  have hpair : Filter.Tendsto (fun x => Complex.equivRealProdCLM (g x))
      l (nhds ((0, 0) : ℝ × ℝ)) := by
    simpa using hre.prodMk_nhds him
  have h : Tendsto (⇑equivRealProdCLM.symm) (nhds (0, 0)) (nhds (equivRealProdCLM.symm (0, 0))) := by
    refine Continuous.tendsto' ?_ (0, 0) (equivRealProdCLM.symm (0, 0)) rfl
    exact ContinuousLinearEquiv.continuous equivRealProdCLM.symm
  simpa using h.comp hpair

lemma tendsto_zero_atTop_of_integrable_boundedVariationOn_complex
    (g : ℝ → ℂ) (hg1 : MeasureTheory.Integrable g)
    (hg2 : BoundedVariationOn g Set.univ) :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
    refine tendsto_complex_zero_of_re_im ?_ ?_
    refine tendsto_zero_atTop_of_integrable_boundedVariationOn_real (⇑Complex.reCLM ∘ g) ?_ ?_
    apply reCLM.integrable_comp hg1
    apply reCLM.lipschitz.comp_boundedVariationOn hg2
    refine tendsto_zero_atTop_of_integrable_boundedVariationOn_real (⇑Complex.imCLM ∘ g) ?_ ?_
    apply imCLM.integrable_comp hg1
    apply imCLM.lipschitz.comp_boundedVariationOn hg2



lemma tendsto_zero_atBot_of_integrable_boundedVariationOn_complex
    (g : ℝ → ℂ) (hg1 : MeasureTheory.Integrable g)
    (hg2 : BoundedVariationOn g Set.univ) :
    Filter.Tendsto g Filter.atBot (nhds 0) := by
    refine tendsto_complex_zero_of_re_im ?_ ?_
    refine tendsto_zero_atBot_of_integrable_boundedVariationOn_real (⇑Complex.reCLM ∘ g) ?_ ?_
    apply reCLM.integrable_comp hg1
    apply reCLM.lipschitz.comp_boundedVariationOn hg2
    refine tendsto_zero_atBot_of_integrable_boundedVariationOn_real (⇑Complex.imCLM ∘ g) ?_ ?_
    apply imCLM.integrable_comp hg1
    apply imCLM.lipschitz.comp_boundedVariationOn hg2



theorem tendsto_fourier_boundary_zero
    (g : ℝ → ℂ) (hg1 : MeasureTheory.Integrable g)
    (hg2 : BoundedVariationOn g Set.univ) (ξ : ℝ) (hξ : ξ ≠ 0) :
    Filter.Tendsto
      (fun R : ℝ =>
        g R * fourierStieltjesPrimitive ξ R -
          g (-R) * fourierStieltjesPrimitive ξ (-R))
      Filter.atTop (nhds 0) := by
  exact tendsto_fourier_boundary_zero_of_tendsto g
    (tendsto_zero_atTop_of_integrable_boundedVariationOn_complex g hg1 hg2)
    (tendsto_zero_atBot_of_integrable_boundedVariationOn_complex g hg1 hg2) ξ hξ

lemma integrable_fourierKernel_mul
    (g : ℝ → ℂ) (hg : MeasureTheory.Integrable g) (ξ : ℝ) :
    MeasureTheory.Integrable (fun x : ℝ => fourierKernel ξ x * g x) volume := by
    have h1 : AEStronglyMeasurable (fourierKernel ξ) volume := by
      apply (continuous_fourierKernel ξ).aestronglyMeasurable
    have h2 : AEStronglyMeasurable g := by apply hg.1
    refine hg.congr' (h1.mul h2) ?_
    filter_upwards
    intro a
    calc
      ‖g a‖ = 1 * ‖g a‖ := by ring
      _ = ‖fourierKernel ξ a‖ * ‖g a‖ := by
        unfold fourierKernel
        rw[Complex.norm_exp_ofReal_mul_I]
      _ = ‖fourierKernel ξ a * g a‖ := by
        exact Eq.symm (Complex.norm_mul (fourierKernel ξ a) (g a))



theorem tendsto_interval_fourierKernel_integral
    (g : ℝ → ℂ) (hg1 : MeasureTheory.Integrable g) (ξ : ℝ) :
    Filter.Tendsto
      (fun R : ℝ => ∫ x in (-R)..R, (fourierKernel ξ x) * g x)
      Filter.atTop (nhds (𝓕 g ξ)) := by
  have ha :
      Filter.Tendsto (fun R : ℝ => ∫ x in (-R)..R, fourierKernel ξ x * g x)
        Filter.atTop (nhds (∫ x : ℝ, fourierKernel ξ x * g x)) := by
    refine intervalIntegral_tendsto_integral ?_ ?_ fun ⦃U⦄ a ↦ a
    exact integrable_fourierKernel_mul g hg1 ξ
    exact tendsto_neg_atTop_atBot
  have hb : 𝓕 g ξ = ∫ x : ℝ, fourierKernel ξ x * g x := by
    rw[Real.fourier_real_eq_integral_exp_smul]
    unfold fourierKernel
    simp
  simpa [hb] using ha

theorem fourier_tendsto_stieltjesPrimitive_of_boundedVariation
    (g : ℝ → ℂ) (hg1 : MeasureTheory.Integrable g)
    (hg2 : BoundedVariationOn g Set.univ) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ∃ L : ℂ,
      Filter.Tendsto
        (fun R : ℝ =>
          stieltjesIntegral (-R) R (mul ℝ ℂ) (fourierStieltjesPrimitive ξ) g)
        Filter.atTop (nhds L) ∧
      𝓕 g ξ = -L ∧
      ‖L‖ ≤ ‖((2 * Real.pi * Complex.I * (ξ : ℂ))⁻¹)‖ *
        (eVariationOn g Set.univ).toReal := by
  use - 𝓕 g ξ
  let S : ℝ → ℂ := fun R =>
    stieltjesIntegral (-R) R (mul ℝ ℂ) (fourierStieltjesPrimitive ξ) g
  let I : ℝ → ℂ := fun R => ∫ x in (-R)..R, fourierKernel ξ x * g x
  let boundary : ℝ → ℂ := fun R =>
    g R * fourierStieltjesPrimitive ξ R -
      g (-R) * fourierStieltjesPrimitive ξ (-R)
  have hS_eq : S =ᶠ[Filter.atTop] fun R => boundary R - I R := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
    unfold S boundary I
    have ha : -R < R := by linarith
    have hb : BoundedVariationOn g (Set.Icc (-R) R) := by
      exact BoundedVariationOn.mono hg2 fun ⦃a⦄ a ↦ trivial
    have hc : ∫ (x : ℝ) in -R..R, fourierKernel ξ x * g x =
    g R * fourierStieltjesPrimitive ξ R - g (-R) * fourierStieltjesPrimitive ξ (-R) -
      stieltjesIntegral (-R) R (mul ℝ ℂ) (fourierStieltjesPrimitive ξ) g := by
          refine interval_fourierIntegral_eq_boundary_sub_stieltjes (a := -R) (b := R) g ?_ ξ hξ ?_
          simp
          linarith
          exact hb
    simp [hc]
  have hI_tendsto : Filter.Tendsto I Filter.atTop (nhds (𝓕 g ξ)) := by
    unfold I
    exact tendsto_interval_fourierKernel_integral g hg1 ξ
  have hboundary_tendsto : Filter.Tendsto boundary Filter.atTop (nhds 0) := by
    unfold boundary
    exact tendsto_fourier_boundary_zero g hg1 hg2 ξ hξ
  have hS_tendsto : Filter.Tendsto S Filter.atTop (nhds (-𝓕 g ξ)) := by
    unfold S
    refine Filter.Tendsto.congr' hS_eq.symm ?_
    simpa using hboundary_tendsto.sub hI_tendsto
  refine ⟨?_,by simp, ?_⟩
  apply hS_tendsto
  let C : ℝ := ‖((2 * Real.pi * Complex.I * (ξ : ℂ))⁻¹ : ℂ)‖
  let V : ℝ := (eVariationOn g Set.univ).toReal
  have hS_bound_eventually : ∀ᶠ R in Filter.atTop, ‖S R‖ ≤ C * V := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
    unfold S C V
    have ha : -R < R := by linarith
    have hb : BoundedVariationOn g (Set.Icc (-R) R) := by
      exact BoundedVariationOn.mono hg2 fun ⦃a⦄ a ↦ trivial
    have hc : (eVariationOn g (Set.Icc (-R) R)).toReal ≤ (eVariationOn g Set.univ).toReal := by
      refine ENNReal.toReal_mono hg2 ?_
      exact eVariationOn.mono g fun ⦃a⦄ a ↦ trivial
    have hd : ‖stieltjesIntegral (-R) R (mul ℝ ℂ) (fourierStieltjesPrimitive ξ) g‖ ≤
  ‖(2 * ↑Real.pi * Complex.I * ↑ξ)⁻¹‖ * (eVariationOn g (Set.Icc (-R) R)).toReal :=
      norm_stieltjesIntegral_fourierStieltjesPrimitive_le (a := -R) (b := R) g ha hb ξ
    refine hd.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ ?_
    apply hc
    apply norm_nonneg
  have hclosed : IsClosed {z : ℂ | ‖z‖ ≤ C * V} :=
    isClosed_le continuous_norm continuous_const
  have hf : ‖(-𝓕 g ξ)‖ ≤ C * V := by
    refine hclosed.mem_of_tendsto hS_tendsto ?_
    apply hS_bound_eventually
  unfold C V at hf
  exact hf

lemma fourier_bounded_variation
    (g : ℝ → ℂ) (hg1 : MeasureTheory.Integrable g)
    (hg2 : BoundedVariationOn g Set.univ) :
    ∀ (ξ : ℝ), ξ ≠ 0 →
      ‖𝓕 g ξ‖ ≤ ‖(2 * ↑Real.pi * Complex.I * ↑ξ)⁻¹‖ * (eVariationOn g Set.univ).toReal := by
  intro ξ hξ
  obtain ⟨L, ha, hb, hc⟩ := fourier_tendsto_stieltjesPrimitive_of_boundedVariation g hg1 hg2 ξ hξ
  calc
    ‖𝓕 g ξ‖ = ‖L‖ := by simp[hb]
    _ ≤ ‖(2 * ↑Real.pi * Complex.I * ↑ξ)⁻¹‖ * (eVariationOn g Set.univ).toReal := by apply hc


end
end FourierStieltjes
