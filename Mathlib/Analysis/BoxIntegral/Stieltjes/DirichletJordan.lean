/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.Fourier
public import Mathlib.Analysis.Fourier.Fejer

/-! # The Dirichlet–Jordan theorem

We follow Chapter 12 of Wheeden–Zygmund, *Measure and Integral* (1977). Let `f : ℝ → ℂ` be
`2π`-periodic and of bounded variation over a period, and let `V` be its total variation over
the closed interval of periodicity `[-π, π]`.

## Main results

* `FourierSeries.two_pi_mul_coeff_eq_stieltjesIntegral`: the integration by parts in the proof
  of (12.24), `2π c_k = (ik)⁻¹ ∫_{-π}^{π} e^{-ikx} df(x)` for `k ≠ 0`, where the integral on the
  right is a Riemann–Stieltjes integral.
* `FourierSeries.norm_coeff_le_of_boundedVariationOn`: (12.24), `|c_k| ≤ V / (2π|k|)` for
  `k ≠ 0`. Hence the terms `u_k = c_k e^{ikx} + c_{-k} e^{-ikx}` of `S[f]` satisfy
  `|u_k| ≤ (V/π)/k` (`norm_term_le_of_boundedVariationOn`).
* `FourierSeries.boundedVariationOn_Icc_of_periodic`: `f` is of bounded variation on every compact
  interval. In particular `f` has one-sided limits everywhere
  (`tendsto_rightLim_of_periodic`, `tendsto_leftLim_of_periodic`), and `f` is bounded
  (`norm_le_of_boundedVariationOn`).
* `FourierSeries.tendsto_partialSum_of_boundedVariationOn`: **Dirichlet–Jordan theorem**
  (12.50)(a): `S[f]` converges to `(f(x+) + f(x-))/2` at every `x`, hence to `f(x)` at every point
  of continuity (`tendsto_partialSum_of_boundedVariationOn_of_continuousAt`).
* `FourierSeries.tendstoUniformlyOn_partialSum_of_boundedVariationOn`: (12.50)(b): the
  convergence is uniform over every closed interval of continuity of `f` (and uniform everywhere
  if `f` is continuous: `tendstoUniformly_partialSum_of_boundedVariationOn`).
* `FourierSeries.norm_partialSum_le_of_boundedVariationOn`: (12.50)(c): the partial sums of `S[f]`
  are uniformly bounded, `|s_n(x)| ≤ |f(-π)| + V + V/π`.

As in Wheeden–Zygmund, parts (a) and (b) follow from Fejér's theorem (12.47) and Hardy's Tauberian
theorem (12.45), since the terms of `S[f]` are `O(1/k)` by (12.24); part (c) follows from
(12.48)(a) and the remark preceding (12.45).

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Finset Filter Topology MeasureTheory intervalIntegral BoxIntegral

namespace FourierSeries

variable {f : ℝ → ℂ}

/-! ### Fourier coefficients of functions of bounded variation: (12.24) -/

/-- For `ξ = k / (2π)`, the kernel `FourierTransform.e ξ` is `x ↦ e^{-ikx}`. -/
theorem fourierTransform_e_eq (k : ℤ) (x : ℝ) :
    FourierTransform.e (k / (2 * π)) x = Complex.exp (-(k * x) * Complex.I) := by
  have h : -2 * π * x * ((k : ℝ) / (2 * π)) = -(k * x) := by
    field_simp
  rw [FourierTransform.e, h]
  push_cast
  rfl

/-- Integration by parts for the Fourier coefficients of a periodic function of bounded
variation: the boundary terms cancel by periodicity, so that
`∫_{-π}^{π} f(x) e^{-ikx} dx = -∫_{-π}^{π} E(x) df(x)`, where `E = FourierTransform.E (k/(2π))`
is the primitive `x ↦ (-ik)⁻¹ e^{-ikx}` of `x ↦ e^{-ikx}`. -/
theorem integral_eq_neg_stieltjesIntegral_E (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) {k : ℤ} (hk : k ≠ 0) :
    ∫ x in -π..π, f x * Complex.exp (-(k * x) * Complex.I) =
      -∫⟨ContinuousLinearMap.mul ℝ ℂ⟩ x in -π..π, FourierTransform.E (k / (2 * π)) x ∂f := by
  have hξ : (k : ℝ) / (2 * π) ≠ 0 := div_ne_zero (Int.cast_ne_zero.2 hk) two_pi_pos.ne'
  have h := FourierTransform.interval_fourierIntegral_eq_boundary_sub_stieltjes
    (neg_lt_self pi_pos) hξ hbv
  have h₁ : f π = f (-π) := by simpa [show -π + 2 * π = π by ring] using hf (-π)
  have h₂ : FourierTransform.E (k / (2 * π)) π = FourierTransform.E (k / (2 * π)) (-π) := by
    simp only [FourierTransform.E, fourierTransform_e_eq]
    congr 1
    exact Complex.exp_eq_exp_iff_exists_int.2 ⟨-k, by push_cast; ring⟩
  rw [h₁, h₂, sub_self, zero_sub] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun x _ ↦ ?_
  rw [fourierTransform_e_eq]
  ring

/-- The integration by parts in the proof of (12.24) (Wheeden–Zygmund, p. 222): for `k ≠ 0`,
`2π c_k = (ik)⁻¹ ∫_{-π}^{π} e^{-ikx} df(x)`, a Riemann–Stieltjes integral. -/
theorem two_pi_mul_coeff_eq_stieltjesIntegral (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) {k : ℤ} (hk : k ≠ 0) :
    2 * π * coeff f k = (Complex.I * k)⁻¹ *
      ∫⟨ContinuousLinearMap.mul ℝ ℂ⟩ x in -π..π, Complex.exp (-(k * x) * Complex.I) ∂f := by
  set c : ℂ := -(Complex.I * k) with hc_def
  have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.2 hk
  have hIk : Complex.I * k ≠ 0 := mul_ne_zero Complex.I_ne_zero hk'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 pi_ne_zero
  have hInt : StieltjesIntegrable (-π) π (ContinuousLinearMap.mul ℝ ℂ)
      (FourierTransform.E (k / (2 * π))) f := by
    have hbv' : BoundedVariationOn f (Set.uIcc (-π) π) := by
      rwa [Set.uIcc_of_le (neg_le_self pi_pos.le)]
    exact .of_continuousOn_of_boundedVariationOn (by fun_prop) hbv'
  have hmap := stieltjesIntegral_map (φ := ContinuousLinearMap.mul ℝ ℂ c)
    (ψ := ContinuousLinearMap.id ℝ ℂ) (Ψ := ContinuousLinearMap.mul ℝ ℂ c)
    (B' := ContinuousLinearMap.mul ℝ ℂ)
    (fun e y ↦ by simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.id_apply]; ring)
    hInt
  have hfun : (fun x ↦ ContinuousLinearMap.mul ℝ ℂ c (FourierTransform.E (k / (2 * π)) x)) =
      fun x : ℝ ↦ Complex.exp (-(k * x) * Complex.I) := by
    funext x
    rw [ContinuousLinearMap.mul_apply', FourierTransform.E, fourierTransform_e_eq, ← mul_assoc]
    convert one_mul _
    rw [hc_def]
    push_cast
    field_simp
  have hid : (ContinuousLinearMap.id ℝ ℂ ∘ f) = f := rfl
  rw [hfun, hid, ContinuousLinearMap.mul_apply'] at hmap
  rw [hmap, coeff, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero two_ne_zero hπ), one_mul,
    integral_eq_neg_stieltjesIntegral_E hf hbv hk, hc_def, ← mul_assoc, mul_neg,
    inv_mul_cancel₀ hIk, neg_one_mul]

/-- **(12.24)** (Wheeden–Zygmund): if a periodic `f` is of bounded variation over a period, then
`|c_k| ≤ V / (2π|k|)` for `k ≠ 0`, where `V` is the total variation of `f` over the closed
interval of periodicity `[-π, π]`. -/
theorem norm_coeff_le_of_boundedVariationOn (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) {k : ℤ} (hk : k ≠ 0) :
    ‖coeff f k‖ ≤ (eVariationOn f (Set.Icc (-π) π)).toReal / (2 * π * |(k : ℝ)|) := by
  have hk' : |(k : ℝ)| ≠ 0 := abs_ne_zero.2 (Int.cast_ne_zero.2 hk)
  have hE := FourierTransform.norm_stieltjesIntegral_E_le ((k : ℝ) / (2 * π))
    (neg_lt_self pi_pos) hbv
  have h2π : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg pi_pos.le]
    norm_num
  rw [coeff, integral_eq_neg_stieltjesIntegral_E hf hbv hk, norm_mul, norm_neg, h2π]
  calc _ ≤ (2 * π)⁻¹ * (|(k : ℝ) / (2 * π)|⁻¹ * (π⁻¹ * 2⁻¹) *
        (eVariationOn f (Set.Icc (-π) π)).toReal) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = _ := by
      rw [abs_div, abs_of_pos two_pi_pos]
      field_simp

/-- The terms of `S[f]` are `O(1/k)`: `|c_k e^{ikx} + c_{-k} e^{-ikx}| ≤ (V/π)/k` for `k ≥ 1`. -/
theorem norm_term_le_of_boundedVariationOn (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) (x : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ‖term f x n‖ ≤ (eVariationOn f (Set.Icc (-π) π)).toReal / π / n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  set V := (eVariationOn f (Set.Icc (-π) π)).toReal
  have h₁ := norm_coeff_le_of_boundedVariationOn hf hbv (k := (k + 1 : ℤ)) (by omega)
  have h₂ := norm_coeff_le_of_boundedVariationOn hf hbv (k := -(k + 1 : ℤ)) (by omega)
  have hk₁ : |((k + 1 : ℤ) : ℝ)| = (k : ℝ) + 1 := by
    push_cast
    exact abs_of_pos (by positivity)
  have hk₂ : |((-(k + 1) : ℤ) : ℝ)| = (k : ℝ) + 1 := by
    push_cast
    rw [abs_neg]
    exact abs_of_pos (by positivity)
  rw [hk₁] at h₁
  rw [hk₂] at h₂
  have e₁ : ‖Complex.exp (((k : ℂ) + 1) * x * Complex.I)‖ = 1 := by
    rw [show ((k : ℂ) + 1) * x * Complex.I = (((k + 1) * x : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have e₂ : ‖Complex.exp (-(((k : ℂ) + 1) * x) * Complex.I)‖ = 1 := by
    rw [show -(((k : ℂ) + 1) * x) * Complex.I = ((-((k + 1) * x) : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  simp only [term]
  calc _ ≤ ‖coeff f (k + 1)‖ + ‖coeff f (-(k + 1))‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, e₁, e₂, mul_one, mul_one]
    _ ≤ V / (2 * π * ((k : ℝ) + 1)) + V / (2 * π * ((k : ℝ) + 1)) := add_le_add h₁ h₂
    _ = V / π / ((k + 1 : ℕ) : ℝ) := by
      push_cast
      field_simp
      ring

/-! ### Periodic functions of bounded variation -/

/-- The variation over an interval is invariant under translation by a period. -/
theorem eVariationOn_Icc_add_eq {E : Type*} [PseudoEMetricSpace E] {g : ℝ → E} {c : ℝ}
    (hc : ∀ x, g (x + c) = g x) (a b : ℝ) :
    eVariationOn g (Set.Icc (a + c) (b + c)) = eVariationOn g (Set.Icc a b) := by
  have hφ : MonotoneOn (fun x : ℝ ↦ x + c) (Set.Icc a b) :=
    fun x _ y _ hxy ↦ add_le_add hxy le_rfl
  have h := eVariationOn.comp_eq_of_monotoneOn g (fun x : ℝ ↦ x + c) hφ
  rw [Set.image_add_const_Icc] at h
  rw [← h]
  congr 1
  funext x
  exact hc x

/-- A `2π`-periodic function of bounded variation over `[-π, π]` is of bounded variation on every
compact interval. -/
theorem boundedVariationOn_Icc_of_periodic (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) (a b : ℝ) :
    BoundedVariationOn f (Set.Icc a b) := by
  have hshift : ∀ (m : ℤ) {c d : ℝ}, c = -π + m * (2 * π) → d = π + m * (2 * π) →
      eVariationOn f (Set.Icc c d) = eVariationOn f (Set.Icc (-π) π) := by
    rintro m c d rfl rfl
    exact eVariationOn_Icc_add_eq (hf.int_mul m) (-π) π
  have key : ∀ n : ℕ, BoundedVariationOn f (Set.Icc (-π - n * (2 * π)) (π + n * (2 * π))) := by
    intro n
    induction n with
    | zero => simpa using hbv
    | succ n ih =>
      have hπ := pi_pos
      have hn : (0 : ℝ) ≤ n := n.cast_nonneg
      have h₁ : -π - ((n : ℝ) + 1) * (2 * π) ≤ -π - n * (2 * π) := by nlinarith
      have h₂ : -π - n * (2 * π) ≤ π + n * (2 * π) := by nlinarith
      have h₃ : π + n * (2 * π) ≤ π + ((n : ℝ) + 1) * (2 * π) := by nlinarith
      have hL := hshift (-(n + 1 : ℤ)) (c := -π - ((n : ℝ) + 1) * (2 * π))
        (d := -π - n * (2 * π)) (by push_cast; ring) (by push_cast; ring)
      have hR := hshift (n + 1 : ℤ) (c := π + n * (2 * π))
        (d := π + ((n : ℝ) + 1) * (2 * π)) (by push_cast; ring) (by push_cast; ring)
      have s₁ := eVariationOn.Icc_add_Icc f h₁ h₂ (Set.mem_univ _)
      have s₂ := eVariationOn.Icc_add_Icc f (h₁.trans h₂) h₃ (Set.mem_univ _)
      simp only [Set.univ_inter] at s₁ s₂
      push_cast
      unfold BoundedVariationOn at hbv ih ⊢
      rw [← s₂, ← s₁, hL, hR]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hbv, ih⟩, hbv⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ((|a| + |b|) / (2 * π))
  rw [div_le_iff₀ two_pi_pos] at hn
  refine (key n).mono (Set.Icc_subset_Icc ?_ ?_)
  · linarith [neg_abs_le a, abs_nonneg b, pi_pos]
  · linarith [le_abs_self b, abs_nonneg a, pi_pos]

/-- A `2π`-periodic function of bounded variation over `[-π, π]` is locally of bounded
variation. -/
theorem locallyBoundedVariationOn_of_periodic (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) : LocallyBoundedVariationOn f Set.univ :=
  fun a b _ _ ↦ by simpa using boundedVariationOn_Icc_of_periodic hf hbv a b

/-- A `2π`-periodic function of bounded variation over `[-π, π]` has a limit from the right
at every point. -/
theorem tendsto_rightLim_of_periodic (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) (x : ℝ) :
    Tendsto f (𝓝[>] x) (𝓝 (Function.rightLim f x)) := by
  refine tendsto_rightLim_of_tendsto ?_
  obtain ⟨l, hl⟩ :=
    (boundedVariationOn_Icc_of_periodic hf hbv (x - 1) (x + 1)).exists_tendsto_right x
  refine ⟨l, ?_⟩
  rwa [nhdsWithin_inter_of_mem
    (mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)))] at hl

/-- A `2π`-periodic function of bounded variation over `[-π, π]` has a limit from the left
at every point. -/
theorem tendsto_leftLim_of_periodic (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) (x : ℝ) :
    Tendsto f (𝓝[<] x) (𝓝 (Function.leftLim f x)) := by
  refine tendsto_leftLim_of_tendsto ?_
  obtain ⟨l, hl⟩ :=
    (boundedVariationOn_Icc_of_periodic hf hbv (x - 1) (x + 1)).exists_tendsto_left x
  refine ⟨l, ?_⟩
  rwa [nhdsWithin_inter_of_mem
    (mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)))] at hl

/-- A `2π`-periodic function of bounded variation over `[-π, π]` is bounded:
`|f(x)| ≤ |f(-π)| + V`. -/
theorem norm_le_of_boundedVariationOn (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) (x : ℝ) :
    ‖f x‖ ≤ ‖f (-π)‖ + (eVariationOn f (Set.Icc (-π) π)).toReal := by
  obtain ⟨y, hy, hxy⟩ := hf.exists_mem_Ico two_pi_pos x (-π)
  have hy' : y ∈ Set.Icc (-π) π := ⟨hy.1, by linarith [hy.2]⟩
  have h := hbv.dist_le hy' (Set.left_mem_Icc.2 (neg_le_self pi_pos.le))
  rw [hxy]
  calc ‖f y‖ = ‖f (-π) + (f y - f (-π))‖ := by rw [add_sub_cancel]
    _ ≤ ‖f (-π)‖ + dist (f y) (f (-π)) := by rw [dist_eq_norm]; exact norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl h

/-- A function of bounded variation over `[-π, π]` is integrable over `[-π, π]`. -/
theorem intervalIntegrable_of_boundedVariationOn
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) : IntervalIntegrable f volume (-π) π :=
  (riemannIntegral_eq_intervalIntegral
    (BoxIntegral.BoundedVariationOn.riemannIntegrable (neg_le_self pi_pos.le) hbv)).1

/-! ### The Dirichlet–Jordan theorem (12.50) -/

/-- (12.50)(a) at a point where the one-sided limits `f(x+) = l₁` and `f(x-) = l₂` are given:
`S[f]` converges to `(l₁ + l₂)/2` at `x`. -/
theorem tendsto_partialSum_of_tendsto (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) {x : ℝ} {l₁ l₂ : ℂ}
    (h₁ : Tendsto f (𝓝[>] x) (𝓝 l₁)) (h₂ : Tendsto f (𝓝[<] x) (𝓝 l₂)) :
    Tendsto (fun n ↦ partialSum f n x) atTop (𝓝 ((l₁ + l₂) / 2)) :=
  tendsto_sum_range_of_tendsto_cesaroMean
    (fun _ hn ↦ norm_term_le_of_boundedVariationOn hf hbv x hn)
    (tendsto_fejerMean_of_tendsto hf (intervalIntegrable_of_boundedVariationOn hbv) h₁ h₂)

/-- **Dirichlet–Jordan theorem** (Wheeden–Zygmund (12.50)(a)): if `f` is periodic and of bounded
variation, then `S[f]` converges to `(f(x+) + f(x-))/2` at every point `x`. -/
theorem tendsto_partialSum_of_boundedVariationOn (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) (x : ℝ) :
    Tendsto (fun n ↦ partialSum f n x) atTop
      (𝓝 ((Function.rightLim f x + Function.leftLim f x) / 2)) :=
  tendsto_partialSum_of_tendsto hf hbv (tendsto_rightLim_of_periodic hf hbv x)
    (tendsto_leftLim_of_periodic hf hbv x)

/-- **Dirichlet–Jordan theorem** (12.50)(a) at a point of continuity: `S[f]` converges to
`f(x)`. -/
theorem tendsto_partialSum_of_boundedVariationOn_of_continuousAt
    (hf : Function.Periodic f (2 * π)) (hbv : BoundedVariationOn f (Set.Icc (-π) π)) {x : ℝ}
    (hx : ContinuousAt f x) : Tendsto (fun n ↦ partialSum f n x) atTop (𝓝 (f x)) := by
  have := tendsto_partialSum_of_tendsto hf hbv (hx.tendsto.mono_left nhdsWithin_le_nhds)
    (hx.tendsto.mono_left nhdsWithin_le_nhds)
  rwa [add_self_div_two] at this

/-- **Dirichlet–Jordan theorem** (Wheeden–Zygmund (12.50)(b)): if `f` is periodic and of bounded
variation, the convergence of `S[f]` is uniform over every closed interval of continuity of `f`. -/
theorem tendstoUniformlyOn_partialSum_of_boundedVariationOn (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) {a b : ℝ}
    (hcont : ∀ x ∈ Set.Icc a b, ContinuousAt f x) :
    TendstoUniformlyOn (fun n x ↦ partialSum f n x) f atTop (Set.Icc a b) :=
  tendstoUniformlyOn_sum_range_of_tendstoUniformlyOn_cesaroMean (u := fun x ↦ term f x)
    (fun x _ _ hn ↦ norm_term_le_of_boundedVariationOn hf hbv x hn)
    (tendstoUniformlyOn_fejerMean hf (intervalIntegrable_of_boundedVariationOn hbv) hcont)

/-- (12.50)(b) for continuous `f`: the convergence of `S[f]` is uniform everywhere. -/
theorem tendstoUniformly_partialSum_of_boundedVariationOn (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) (hcont : Continuous f) :
    TendstoUniformly (fun n x ↦ partialSum f n x) f atTop :=
  tendstoUniformly_of_periodic (periodic_partialSum f) hf
    (tendstoUniformlyOn_partialSum_of_boundedVariationOn hf hbv fun _ _ ↦ hcont.continuousAt)

/-- **Dirichlet–Jordan theorem** (Wheeden–Zygmund (12.50)(c)): if `f` is periodic and of bounded
variation, the partial sums of `S[f]` are uniformly bounded:
`|s_n(x)| ≤ |f(-π)| + V + V/π`. -/
theorem norm_partialSum_le_of_boundedVariationOn (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) (n : ℕ) (x : ℝ) :
    ‖partialSum f n x‖ ≤ ‖f (-π)‖ + (eVariationOn f (Set.Icc (-π) π)).toReal +
      (eVariationOn f (Set.Icc (-π) π)).toReal / π :=
  norm_sum_range_le_of_norm_cesaroMean_le
    (fun _ hk ↦ norm_term_le_of_boundedVariationOn hf hbv x hk)
    (fun m ↦ norm_fejerMean_le hf (intervalIntegrable_of_boundedVariationOn hbv)
      (norm_le_of_boundedVariationOn hf hbv) m x) n

/-- (12.50)(c): the partial sums of `S[f]` are uniformly bounded. -/
theorem exists_norm_partialSum_le_of_boundedVariationOn (hf : Function.Periodic f (2 * π))
    (hbv : BoundedVariationOn f (Set.Icc (-π) π)) : ∃ C, ∀ n x, ‖partialSum f n x‖ ≤ C :=
  ⟨_, norm_partialSum_le_of_boundedVariationOn hf hbv⟩

end FourierSeries
