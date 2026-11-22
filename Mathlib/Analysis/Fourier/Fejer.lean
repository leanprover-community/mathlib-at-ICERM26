/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.Fourier.FejerKernel
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Fourier series of periodic functions and Fejér's theorem

We follow §§12.1, 12.3 and 12.6 of Wheeden–Zygmund, *Measure and Integral* (1977). Throughout,
`f : ℝ → ℂ` is `2π`-periodic and integrable over a period.

## Main definitions

* `FourierSeries.coeff f k`: the Fourier coefficient `c_k = (2π)⁻¹ ∫_{-π}^{π} f(x) e^{-ikx} dx`.
  It agrees with Mathlib's `fourierCoeffOn` (`coeff_eq_fourierCoeffOn`).
* `FourierSeries.term f x k`: the terms `u_0 = c_0`, `u_k = c_k e^{ikx} + c_{-k} e^{-ikx}` of
  `S[f]` at `x`.
* `FourierSeries.partialSum f n x`: the partial sum `s_n(x) = ∑_{|k| ≤ n} c_k e^{ikx}`
  (`partialSum_eq_sum_Icc`).
* `FourierSeries.fejerMean f n x`: the arithmetic mean `σ_n(x) = (s_0(x) + ⋯ + s_n(x)) / (n + 1)`.

## Main results

* `partialSum_eq_integral`, `fejerMean_eq_integral`: `s_n(x) = π⁻¹ ∫_{-π}^{π} f(x + t) D_n(t) dt`
  (p. 222–223) and `σ_n(x) = π⁻¹ ∫_{-π}^{π} f(x + t) K_n(t) dt` (p. 235).
* `tendsto_fejerMean_of_tendsto`: **Fejér's theorem** (12.47) at a point where `f` has one-sided
  limits: `σ_n(x) → (f(x+) + f(x-))/2`; in particular `σ_n(x) → f(x)` where `f` is continuous
  (`tendsto_fejerMean_of_continuousAt`).
* `tendstoUniformlyOn_fejerMean`: (12.47), the convergence is uniform on every closed interval of
  continuity of `f`, and uniform everywhere if `f` is continuous (`tendstoUniformly_fejerMean`).
* `norm_fejerMean_le`: (12.48)(a), `|f| ≤ M` implies `|σ_n| ≤ M`.

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Finset Filter Topology MeasureTheory intervalIntegral

namespace FourierSeries

variable {f : ℝ → ℂ}

/-! ### Fourier coefficients, partial sums and Fejér means -/

/-- The Fourier coefficient `c_k = (2π)⁻¹ ∫_{-π}^{π} f(x) e^{-ikx} dx` of a `2π`-periodic
function (Wheeden–Zygmund (12.4), with `Q = [-π, π]`). -/
noncomputable def coeff (f : ℝ → ℂ) (k : ℤ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ x in -π..π, f x * Complex.exp (-(k * x) * Complex.I)

/-- The coefficients `coeff` are those of Mathlib's `fourierCoeffOn` on `[-π, π]`. -/
theorem coeff_eq_fourierCoeffOn (f : ℝ → ℂ) (k : ℤ) :
    coeff f k = fourierCoeffOn (neg_lt_self pi_pos) f k := by
  rw [fourierCoeffOn_eq_integral f k (neg_lt_self pi_pos), coeff, Complex.real_smul]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  congr 1
  · push_cast; ring
  · refine intervalIntegral.integral_congr fun x _ ↦ ?_
    simp only [fourier_coe_apply, smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    field_simp
    ring

/-- The terms of the Fourier series `S[f]` at `x`, with the terms of index `±k` grouped together:
`u_0 = c_0` and `u_k = c_k e^{ikx} + c_{-k} e^{-ikx}` for `k ≥ 1`. -/
noncomputable def term (f : ℝ → ℂ) (x : ℝ) : ℕ → ℂ
  | 0 => coeff f 0
  | k + 1 => coeff f (k + 1) * Complex.exp ((k + 1) * x * Complex.I) +
      coeff f (-(k + 1)) * Complex.exp (-((k + 1) * x) * Complex.I)

/-- The partial sum `s_n(x) = ∑_{|k| ≤ n} c_k e^{ikx}` of the Fourier series
`S[f] = ∑_{k = -∞}^{∞} c_k e^{ikx}` of `f` (Wheeden–Zygmund (12.5)); see `partialSum_eq_sum_Icc`. -/
noncomputable def partialSum (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), term f x k

/-- The Fejér mean `σ_n(x) = (s_0(x) + ⋯ + s_n(x)) / (n + 1)` of the Fourier series of `f`. -/
noncomputable def fejerMean (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  cesaroMean (term f x) n

theorem fejerMean_eq (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    fejerMean f n x = ((n : ℂ) + 1)⁻¹ * ∑ j ∈ range (n + 1), partialSum f j x := by
  rw [fejerMean, cesaroMean, Complex.real_smul]
  push_cast
  rfl

/-- `s_n(x) = ∑_{k=-n}^{n} c_k e^{ikx}`. -/
theorem partialSum_eq_sum_Icc (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    partialSum f n x =
      ∑ k ∈ Finset.Icc (-(n : ℤ)) n, coeff f k * Complex.exp (k * x * Complex.I) := by
  induction n with
  | zero => simp [partialSum, term]
  | succ n ih =>
    have hI : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert (-((n : ℤ) + 1)) (insert ((n : ℤ) + 1) (Finset.Icc (-(n : ℤ)) n)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    simp only [partialSum] at ih ⊢
    rw [Finset.sum_range_succ, ih, hI, Finset.sum_insert (by simp; omega),
      Finset.sum_insert (by simp), term]
    push_cast
    simp only [neg_mul]
    ring

/-- The terms of `S[f]` are `2π`-periodic in `x`. -/
theorem term_add_two_pi (f : ℝ → ℂ) (x : ℝ) (k : ℕ) : term f (x + 2 * π) k = term f x k := by
  cases k with
  | zero => rfl
  | succ k =>
    have h₁ : Complex.exp (((k : ℂ) + 1) * ((x + 2 * π : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((k : ℂ) + 1) * x * Complex.I) :=
      Complex.exp_eq_exp_iff_exists_int.2 ⟨k + 1, by push_cast; ring⟩
    have h₂ : Complex.exp (-(((k : ℂ) + 1) * ((x + 2 * π : ℝ) : ℂ)) * Complex.I) =
        Complex.exp (-(((k : ℂ) + 1) * x) * Complex.I) :=
      Complex.exp_eq_exp_iff_exists_int.2 ⟨-(k + 1), by push_cast; ring⟩
    simp only [term, h₁, h₂]

theorem periodic_partialSum (f : ℝ → ℂ) (n : ℕ) : Function.Periodic (partialSum f n) (2 * π) :=
  fun x ↦ by simp only [partialSum, term_add_two_pi]

theorem periodic_fejerMean (f : ℝ → ℂ) (n : ℕ) : Function.Periodic (fejerMean f n) (2 * π) :=
  fun x ↦ by rw [fejerMean, fejerMean, funext (term_add_two_pi f x)]

/-! ### The partial sums and the Fejér means as integrals against the kernels -/

/-- `c_j e^{ijx} = (2π)⁻¹ ∫_{-π}^{π} f(y) e^{ij(x - y)} dy`. -/
theorem coeff_mul_exp (f : ℝ → ℂ) (j : ℤ) (x : ℝ) :
    coeff f j * Complex.exp (j * x * Complex.I) =
      (2 * π : ℂ)⁻¹ * ∫ y in -π..π, f y * Complex.exp (j * (x - y) * Complex.I) := by
  rw [coeff, mul_assoc, ← intervalIntegral.integral_mul_const]
  congr 1
  refine intervalIntegral.integral_congr fun y _ ↦ ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem term_eq_integral (hint : IntervalIntegrable f volume (-π) π) (x : ℝ) (k : ℕ) :
    term f x k = (π : ℂ)⁻¹ * ∫ y in -π..π, f y * dirichletTerm k (x - y) := by
  cases k with
  | zero =>
    simp only [term, coeff, dirichletTerm_zero, Int.cast_zero, zero_mul, neg_zero, zero_mul,
      Complex.exp_zero, mul_one]
    rw [intervalIntegral.integral_mul_const]
    push_cast
    field_simp
  | succ k =>
    have hI : ∀ j : ℤ, IntervalIntegrable
        (fun y ↦ f y * Complex.exp (j * (x - y) * Complex.I)) volume (-π) π := fun j ↦
      hint.mul_continuousOn (by fun_prop)
    have hj : term f x (k + 1) =
        coeff f ((k : ℤ) + 1) * Complex.exp (((k : ℤ) + 1 : ℤ) * x * Complex.I) +
          coeff f (-((k : ℤ) + 1)) * Complex.exp ((-((k : ℤ) + 1) : ℤ) * x * Complex.I) := by
      simp only [term]
      push_cast
      ring_nf
    rw [hj, coeff_mul_exp, coeff_mul_exp, ← mul_add,
      ← intervalIntegral.integral_add (hI _) (hI _)]
    have h2 : (π : ℂ)⁻¹ * ∫ y in -π..π, f y * dirichletTerm (k + 1) (x - y) =
        (2 * π : ℂ)⁻¹ * ∫ y in -π..π, 2 * (f y * dirichletTerm (k + 1) (x - y)) := by
      rw [intervalIntegral.integral_const_mul]
      field_simp
    rw [h2]
    congr 1
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    simp only [dirichletTerm_succ]
    rw [Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf

theorem partialSum_eq_integral_sub (hint : IntervalIntegrable f volume (-π) π) (n : ℕ)
    (x : ℝ) : partialSum f n x = (π : ℂ)⁻¹ * ∫ y in -π..π, f y * dirichletKernel n (x - y) := by
  simp only [partialSum, term_eq_integral hint, ← mul_sum]
  rw [← intervalIntegral.integral_finsetSum fun k _ ↦ hint.mul_continuousOn (by fun_prop)]
  congr 1
  refine intervalIntegral.integral_congr fun y _ ↦ ?_
  simp [dirichletKernel, mul_sum]

/-- For `2π`-periodic `g` and an even `2π`-periodic `h`,
`∫_{-π}^{π} g(y) h(x - y) dy = ∫_{-π}^{π} g(x + t) h(t) dt`. -/
theorem integral_mul_sub_eq_integral_add_mul {g : ℝ → ℂ} {h : ℝ → ℝ}
    (hg : Function.Periodic g (2 * π)) (hh_neg : ∀ t, h (-t) = h t)
    (hh_per : ∀ t, h (t + 2 * π) = h t) (x : ℝ) :
    ∫ y in -π..π, g y * h (x - y) = ∫ t in -π..π, g (x + t) * h t := by
  have h1 : ∫ y in -π..π, g y * h (x - y) = ∫ t in (-π - x)..(π - x), g (x + t) * h t := by
    have := intervalIntegral.integral_comp_add_left (a := -π - x) (b := π - x)
      (fun y ↦ g y * (h (x - y) : ℂ)) x
    simp only [sub_add_cancel_left, hh_neg] at this
    rw [show x + (-π - x) = -π by ring, show x + (π - x) = π by ring] at this
    exact this.symm
  have hG : Function.Periodic (fun t ↦ g (x + t) * (h t : ℂ)) (2 * π) := fun t ↦ by
    simp only [← add_assoc, hg (x + t), hh_per t]
  have h2 := hG.intervalIntegral_add_eq (-π - x) (-π)
  rw [show -π - x + 2 * π = π - x by ring, show -π + 2 * π = π by ring] at h2
  rw [h1, h2]

/-- The partial sums as integrals against the Dirichlet kernel (Wheeden–Zygmund, p. 223):
`s_n(x) = π⁻¹ ∫_{-π}^{π} f(x + t) D_n(t) dt`. -/
theorem partialSum_eq_integral (hf : Function.Periodic f (2 * π))
    (hint : IntervalIntegrable f volume (-π) π) (n : ℕ) (x : ℝ) :
    partialSum f n x = (π : ℂ)⁻¹ * ∫ t in -π..π, f (x + t) * dirichletKernel n t := by
  rw [partialSum_eq_integral_sub hint, integral_mul_sub_eq_integral_add_mul hf
    (dirichletKernel_neg n) (dirichletKernel_add_two_pi n)]

/-- `f` is interval integrable over every interval. -/
theorem intervalIntegrable_of_periodic (hf : Function.Periodic f (2 * π))
    (hint : IntervalIntegrable f volume (-π) π) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  hf.intervalIntegrable two_pi_pos.ne' (by rwa [show -π + 2 * π = π by ring]) a b

/-- `t ↦ f (x + t)` is interval integrable over every interval. -/
theorem intervalIntegrable_comp_add (hf : Function.Periodic f (2 * π))
    (hint : IntervalIntegrable f volume (-π) π) (x a b : ℝ) :
    IntervalIntegrable (fun t ↦ f (x + t)) volume a b := by
  have := (intervalIntegrable_of_periodic hf hint (x + a) (x + b)).comp_add_left x
  simpa using this

/-- The Fejér means as integrals against the Fejér kernel (Wheeden–Zygmund, p. 235):
`σ_n(x) = π⁻¹ ∫_{-π}^{π} f(x + t) K_n(t) dt`. -/
theorem fejerMean_eq_integral (hf : Function.Periodic f (2 * π))
    (hint : IntervalIntegrable f volume (-π) π) (n : ℕ) (x : ℝ) :
    fejerMean f n x = (π : ℂ)⁻¹ * ∫ t in -π..π, f (x + t) * fejerKernel n t := by
  have hI : ∀ j : ℕ, IntervalIntegrable (fun t ↦ f (x + t) * (dirichletKernel j t : ℂ))
      volume (-π) π := fun j ↦
    (intervalIntegrable_comp_add hf hint x _ _).mul_continuousOn (by fun_prop)
  rw [fejerMean_eq]
  simp only [partialSum_eq_integral hf hint, ← mul_sum]
  rw [← intervalIntegral.integral_finsetSum fun j _ ↦ hI j, mul_left_comm,
    ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [fejerKernel_eq_mean, ← mul_sum]
  push_cast
  ring

/-! ### Fejér's theorem -/

/-- `∫_{-π}^{π} ‖f(x + t)‖ dt = ∫_{-π}^{π} ‖f(t)‖ dt` for `2π`-periodic `f`. -/
theorem integral_norm_comp_add (hf : Function.Periodic f (2 * π)) (x : ℝ) :
    ∫ t in -π..π, ‖f (x + t)‖ = ∫ t in -π..π, ‖f t‖ := by
  have hg : Function.Periodic (fun t ↦ ‖f t‖) (2 * π) := fun t ↦ by simp only [hf t]
  rw [intervalIntegral.integral_comp_add_left (fun t ↦ ‖f t‖) x]
  have := hg.intervalIntegral_add_eq (x + -π) (-π)
  rwa [show x + -π + 2 * π = x + π by ring, show -π + 2 * π = π by ring] at this

/-- **Fejér's theorem** (Wheeden–Zygmund (12.47)) at a point where `f` has one-sided limits `l₁`
on the right and `l₂` on the left: `σ_n(x) → (l₁ + l₂) / 2`. -/
theorem tendsto_fejerMean_of_tendsto (hf : Function.Periodic f (2 * π))
    (hint : IntervalIntegrable f volume (-π) π) {x : ℝ} {l₁ l₂ : ℂ}
    (h₁ : Tendsto f (𝓝[>] x) (𝓝 l₁)) (h₂ : Tendsto f (𝓝[<] x) (𝓝 l₂)) :
    Tendsto (fun n ↦ fejerMean f n x) atTop (𝓝 ((l₁ + l₂) / 2)) := by
  have hfx : ∀ a b, IntervalIntegrable (fun t ↦ f (x + t)) volume a b :=
    intervalIntegrable_comp_add hf hint x
  have hfx' : ∀ a b, IntervalIntegrable (fun t ↦ f (x - t)) volume a b := fun a b ↦ by
    have := (intervalIntegrable_of_periodic hf hint (x - a) (x - b)).comp_sub_left x
    simpa using this
  have hK : ∀ n, Continuous fun t ↦ (fejerKernel n t : ℂ) := fun n ↦ by fun_prop
  -- `σ_n(x) - (l₁ + l₂)/2 = π⁻¹ (∫_0^π (f(x+t) - l₁) K_n + ∫_0^π (f(x-t) - l₂) K_n)`.
  have hsplit : ∀ n, fejerMean f n x - (l₁ + l₂) / 2 = (π : ℂ)⁻¹ *
      ((∫ t in (0 : ℝ)..π, (f (x + t) - l₁) * fejerKernel n t) +
        ∫ t in (0 : ℝ)..π, (f (x - t) - l₂) * fejerKernel n t) := fun n ↦ by
    have hneg : ∫ t in -π..0, f (x + t) * fejerKernel n t =
        ∫ t in (0 : ℝ)..π, f (x - t) * fejerKernel n t := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := π)
        (fun t ↦ f (x + t) * (fejerKernel n t : ℂ))
      simp only [neg_zero, fejerKernel_neg, ← sub_eq_add_neg] at this
      exact this.symm
    have hKπ : ∫ t in (0 : ℝ)..π, (fejerKernel n t : ℂ) = π / 2 := by
      rw [intervalIntegral.integral_ofReal, integral_fejerKernel_zero_pi]
      push_cast; ring
    rw [fejerMean_eq_integral hf hint,
      ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
        ((hfx _ _).mul_continuousOn (hK n).continuousOn)
        ((hfx _ _).mul_continuousOn (hK n).continuousOn), hneg]
    simp only [sub_mul]
    rw [intervalIntegral.integral_sub ((hfx _ _).mul_continuousOn (hK n).continuousOn)
        ((hK n).intervalIntegrable _ _ |>.const_mul l₁),
      intervalIntegral.integral_sub ((hfx' _ _).mul_continuousOn (hK n).continuousOn)
        ((hK n).intervalIntegrable _ _ |>.const_mul l₂),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hKπ]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    field_simp
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  -- Choose `δ` so that `f(x ± t)` is within `ε/2` of `l₁`, `l₂` for `0 < t < δ`.
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.tendsto_nhdsWithin_nhds.1 h₁ (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.tendsto_nhdsWithin_nhds.1 h₂ (ε / 2) (by positivity)
  set δ := min (min δ₁ δ₂) π with hδ
  have hδpos : 0 < δ := lt_min (lt_min hδ₁ hδ₂) pi_pos
  have hc₁ : ∀ t ∈ Set.Ioo (0 : ℝ) π, |t| < δ → ‖f (x + t) - l₁‖ ≤ ε / 2 := by
    intro t ht htδ
    rw [abs_of_pos ht.1] at htδ
    have := hδ₁' (x := x + t) (by simp [ht.1]) (by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos ht.1]
      exact htδ.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
    rw [dist_eq_norm] at this
    exact this.le
  have hc₂ : ∀ t ∈ Set.Ioo (0 : ℝ) π, |t| < δ → ‖f (x - t) - l₂‖ ≤ ε / 2 := by
    intro t ht htδ
    rw [abs_of_pos ht.1] at htδ
    have := hδ₂' (x := x - t) (by simp [ht.1]) (by
      rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos ht.1]
      exact htδ.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
    rw [dist_eq_norm] at this
    exact this.le
  set C := (∫ t in (0 : ℝ)..π, (‖f (x + t)‖ + ‖l₁‖)) + ∫ t in (0 : ℝ)..π, (‖f (x - t)‖ + ‖l₂‖)
    with hC
  have hC0 : 0 ≤ C := add_nonneg
    (intervalIntegral.integral_nonneg pi_pos.le fun t _ ↦ by positivity)
    (intervalIntegral.integral_nonneg pi_pos.le fun t _ ↦ by positivity)
  -- The bound `ε/2 + π² C / (2 π (n+1) δ²)` is eventually `< ε`.
  have hlim : Tendsto (fun n : ℕ ↦ ε / 2 + π ^ 2 / (2 * δ ^ 2) * C / π * (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (ε / 2)) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
      (π ^ 2 / (2 * δ ^ 2) * C / π)).const_add (ε / 2)
    rwa [mul_zero, add_zero] at this
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (by linarith : ε / 2 < ε)))
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_zero_right, norm_norm, hsplit n, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg pi_pos.le]
  have e₁ := norm_integral_sub_mul_fejerKernel_le n pi_pos.le (by linarith [pi_pos]) le_rfl
    (by positivity) hδpos (hfx 0 π) hc₁
  have e₂ := norm_integral_sub_mul_fejerKernel_le n pi_pos.le (by linarith [pi_pos]) le_rfl
    (by positivity) hδpos (hfx' 0 π) hc₂
  rw [integral_fejerKernel_zero_pi] at e₁ e₂
  calc π⁻¹ * ‖(∫ t in (0 : ℝ)..π, (f (x + t) - l₁) * fejerKernel n t) +
        ∫ t in (0 : ℝ)..π, (f (x - t) - l₂) * fejerKernel n t‖
      ≤ π⁻¹ * ((ε / 2 * (π / 2) + π ^ 2 / (2 * (n + 1) * δ ^ 2) *
          (∫ t in (0 : ℝ)..π, (‖f (x + t)‖ + ‖l₁‖))) +
        (ε / 2 * (π / 2) + π ^ 2 / (2 * (n + 1) * δ ^ 2) *
          (∫ t in (0 : ℝ)..π, (‖f (x - t)‖ + ‖l₂‖)))) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add e₁ e₂)
    _ = ε / 2 + π ^ 2 / (2 * δ ^ 2) * C / π * (1 / ((n : ℝ) + 1)) := by
        rw [hC]
        field_simp
        ring
    _ < ε := hN n hn

/-- **Fejér's theorem** (12.47) at a point of continuity: `σ_n(x) → f(x)`. -/
theorem tendsto_fejerMean_of_continuousAt (hf : Function.Periodic f (2 * π))
    (hint : IntervalIntegrable f volume (-π) π) {x : ℝ} (hx : ContinuousAt f x) :
    Tendsto (fun n ↦ fejerMean f n x) atTop (𝓝 (f x)) := by
  have := tendsto_fejerMean_of_tendsto hf hint (hx.tendsto.mono_left nhdsWithin_le_nhds)
    (hx.tendsto.mono_left nhdsWithin_le_nhds)
  rwa [← two_mul, mul_div_cancel_left₀ _ two_ne_zero] at this

/-- **Fejér's theorem** (12.47), uniform version: `σ_n → f` uniformly on every closed interval at
each point of which `f` is continuous. -/
theorem tendstoUniformlyOn_fejerMean (hf : Function.Periodic f (2 * π))
    (hint : IntervalIntegrable f volume (-π) π) {a b : ℝ}
    (hcont : ∀ x ∈ Set.Icc a b, ContinuousAt f x) :
    TendstoUniformlyOn (fun n x ↦ fejerMean f n x) f atTop (Set.Icc a b) := by
  rcases (Set.Icc a b).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
  · rw [he]; exact tendstoUniformlyOn_empty
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Uniform continuity of `f` at the points of `[a, b]`.
  have hU := isCompact_Icc.uniformContinuousAt_of_continuousAt f hcont
    (Metric.dist_mem_uniformity (by positivity : 0 < ε / 2))
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.mem_uniformity_dist.1 hU
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun x hx ↦ (hcont x hx).continuousWithinAt)
  set δ := min δ₀ π with hδ
  have hδpos : 0 < δ := lt_min hδ₀ pi_pos
  set C := (∫ t in -π..π, ‖f t‖) + 2 * π * M with hC
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ hx₀)
  have hC0 : 0 ≤ C := add_nonneg
    (intervalIntegral.integral_nonneg (by linarith [pi_pos]) fun t _ ↦ norm_nonneg _)
    (by positivity)
  have hlim : Tendsto (fun n : ℕ ↦ ε / 2 + π ^ 2 / (2 * δ ^ 2) * C / π * (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (ε / 2)) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
      (π ^ 2 / (2 * δ ^ 2) * C / π)).const_add (ε / 2)
    rwa [mul_zero, add_zero] at this
  filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : ε / 2 < ε))] with n hn x hx
  have hfx := intervalIntegrable_comp_add hf hint x
  have hKint : ∫ t in -π..π, (fejerKernel n t : ℂ) = π := by
    rw [intervalIntegral.integral_ofReal, integral_fejerKernel]
  -- `σ_n(x) - f(x) = π⁻¹ ∫_{-π}^{π} (f(x + t) - f(x)) K_n(t) dt`.
  have hdiff : fejerMean f n x - f x =
      (π : ℂ)⁻¹ * ∫ t in -π..π, (f (x + t) - f x) * fejerKernel n t := by
    rw [fejerMean_eq_integral hf hint]
    simp only [sub_mul]
    have hKc : Continuous fun t ↦ (fejerKernel n t : ℂ) := by fun_prop
    rw [intervalIntegral.integral_sub ((hfx _ _).mul_continuousOn hKc.continuousOn)
      ((hKc.intervalIntegrable (-π) π).const_mul (f x)),
      intervalIntegral.integral_const_mul, hKint]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    field_simp
  have hc : ∀ t ∈ Set.Ioo (-π) π, |t| < δ → ‖f (x + t) - f x‖ ≤ ε / 2 := by
    intro t _ htδ
    have h1 := hδ₀' (a := x) (b := x + t) (by
      rw [Real.dist_eq, sub_add_cancel_left, abs_neg]
      exact htδ.trans_le (min_le_left _ _))
    have h2 : dist (f x) (f (x + t)) < ε / 2 := h1 hx
    rw [dist_eq_norm, ← norm_neg, neg_sub] at h2
    exact h2.le
  have e := norm_integral_sub_mul_fejerKernel_le n (by linarith [pi_pos]) le_rfl le_rfl
    (by positivity) hδpos (hfx (-π) π) hc
  rw [integral_fejerKernel] at e
  have hbound : ∫ t in -π..π, (‖f (x + t)‖ + ‖f x‖) ≤ C := by
    rw [intervalIntegral.integral_add (hfx _ _).norm intervalIntegral.intervalIntegrable_const,
      integral_norm_comp_add hf x, intervalIntegral.integral_const, smul_eq_mul, hC]
    have := hM x hx
    nlinarith [pi_pos]
  rw [dist_eq_norm, ← norm_neg, neg_sub, hdiff, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg pi_pos.le]
  calc π⁻¹ * ‖∫ t in -π..π, (f (x + t) - f x) * fejerKernel n t‖
      ≤ π⁻¹ * (ε / 2 * π + π ^ 2 / (2 * (n + 1) * δ ^ 2) * C) := by
        gcongr
        exact e.trans (by gcongr)
    _ = ε / 2 + π ^ 2 / (2 * δ ^ 2) * C / π * (1 / ((n : ℝ) + 1)) := by
        field_simp
    _ < ε := hn

/-- For `2π`-periodic functions, uniform convergence on `[-π, π]` implies uniform convergence
on `ℝ`. -/
theorem tendstoUniformly_of_periodic {ι : Type*} {p : Filter ι} {F : ι → ℝ → ℂ} {g : ℝ → ℂ}
    (hF : ∀ i, Function.Periodic (F i) (2 * π)) (hg : Function.Periodic g (2 * π))
    (h : TendstoUniformlyOn F g p (Set.Icc (-π) π)) : TendstoUniformly F g p := by
  rw [Metric.tendstoUniformly_iff]
  rw [Metric.tendstoUniformlyOn_iff] at h
  intro ε hε
  filter_upwards [h ε hε] with i hi x
  have hper : Function.Periodic (fun y ↦ dist (g y) (F i y)) (2 * π) := fun y ↦ by
    simp only [hg y, hF i y]
  obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico two_pi_pos x (-π)
  rw [hxy]
  exact hi y ⟨hy.1, by linarith [hy.2]⟩

/-- **Fejér's theorem** (12.47): if `f` is continuous everywhere, then `σ_n → f` uniformly
everywhere. -/
theorem tendstoUniformly_fejerMean (hf : Function.Periodic f (2 * π))
    (hint : IntervalIntegrable f volume (-π) π) (hcont : Continuous f) :
    TendstoUniformly (fun n x ↦ fejerMean f n x) f atTop :=
  tendstoUniformly_of_periodic (periodic_fejerMean f) hf
    (tendstoUniformlyOn_fejerMean hf hint fun _ _ ↦ hcont.continuousAt)

/-- (12.48)(a): if `‖f‖ ≤ M` everywhere, then `‖σ_n‖ ≤ M`. -/
theorem norm_fejerMean_le (hf : Function.Periodic f (2 * π))
    (hint : IntervalIntegrable f volume (-π) π) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (n : ℕ) (x : ℝ) :
    ‖fejerMean f n x‖ ≤ M := by
  have hfx := intervalIntegrable_comp_add hf hint x
  rw [fejerMean_eq_integral hf hint, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg pi_pos.le]
  have h : ‖∫ t in -π..π, f (x + t) * fejerKernel n t‖ ≤ ∫ t in -π..π, M * fejerKernel n t := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith [pi_pos])).trans ?_
    refine intervalIntegral.integral_mono_on (by linarith [pi_pos])
      ((hfx _ _).mul_continuousOn (by fun_prop)).norm
      ((continuous_fejerKernel n).intervalIntegrable _ _ |>.const_mul M) fun t _ ↦ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg n t)]
    exact mul_le_mul_of_nonneg_right (hM _) (fejerKernel_nonneg n t)
  rw [intervalIntegral.integral_const_mul, integral_fejerKernel] at h
  calc π⁻¹ * ‖∫ t in -π..π, f (x + t) * fejerKernel n t‖ ≤ π⁻¹ * (M * π) := by gcongr
    _ = M := by field_simp

end FourierSeries
