/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Cesaro

/-! # The Dirichlet and Fejér kernels

We follow §§12.3 and 12.6 of Wheeden–Zygmund, *Measure and Integral* (1977), with their
normalization: the `n`th partial sum and the `n`th Fejér mean of the Fourier series of a
`2π`-periodic `f` are `π⁻¹ ∫_{-π}^{π} f(x + t) D_n(t) dt` and `π⁻¹ ∫_{-π}^{π} f(x + t) K_n(t) dt`.

## Main definitions

* `FourierSeries.dirichletKernel n t`: `D_n(t) = 1/2 + ∑_{k=1}^n cos kt`.
* `FourierSeries.fejerKernel n t`: `K_n(t) = (D_0(t) + ⋯ + D_n(t)) / (n + 1)`, defined as the
  arithmetic mean (`cesaroMean`) of the partial sums of `1/2 + cos t + cos 2t + ⋯`.

## Main results

* `integral_dirichletKernel`: (12.25), `π⁻¹ ∫_{-π}^{π} D_n = 1`.
* `dirichletKernel_mul_two_sin`, `dirichletKernel_eq_div`: (12.26),
  `D_n(t) = sin((n + 1/2)t) / (2 sin(t/2))`.
* `fejerKernel_mul_two_sin_sq`, `fejerKernel_eq_sq`: (12.46),
  `K_n(t) = (1 - cos (n+1)t) / ((n+1)(2 sin(t/2))²) = (2/(n+1)) (sin((n+1)t/2) / (2 sin(t/2)))²`.
* `fejerKernel_eq_sum_cos`: `K_n(t) = 1/2 + ∑_{m=1}^n (1 - m/(n+1)) cos mt`.
* Properties (a)–(c') of `K_n` on p. 236: `fejerKernel_nonneg`, `fejerKernel_neg` (a);
  `integral_fejerKernel` (b); `fejerKernel_le`, `fejerKernel_le_div_sq` (c), with the constant
  `A = π²/2`; `tendsto_integral_fejerKernel` (c').
* `norm_integral_sub_mul_fejerKernel_le`: the estimate behind the proof of Fejér's theorem (12.47).

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Real Finset Filter Topology MeasureTheory intervalIntegral

namespace FourierSeries

/-! ### The Dirichlet kernel -/

/-- The terms `1/2, cos t, cos 2t, …` of the Dirichlet kernel. -/
noncomputable def dirichletTerm : ℕ → ℝ → ℝ
  | 0, _ => 1 / 2
  | k + 1, t => cos ((k + 1) * t)

@[simp]
theorem dirichletTerm_zero (t : ℝ) : dirichletTerm 0 t = 1 / 2 := rfl

@[simp]
theorem dirichletTerm_succ (k : ℕ) (t : ℝ) : dirichletTerm (k + 1) t = cos ((k + 1) * t) := rfl

theorem dirichletTerm_neg (k : ℕ) (t : ℝ) : dirichletTerm k (-t) = dirichletTerm k t := by
  cases k <;> simp [mul_neg]

theorem dirichletTerm_add_two_pi (k : ℕ) (t : ℝ) :
    dirichletTerm k (t + 2 * π) = dirichletTerm k t := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [dirichletTerm_succ]
    rw [mul_add, show ((k : ℝ) + 1) * (2 * π) = ((k + 1 : ℕ) : ℝ) * (2 * π) by push_cast; ring,
      cos_add_nat_mul_two_pi]

@[fun_prop]
theorem continuous_dirichletTerm (k : ℕ) : Continuous (dirichletTerm k) := by
  cases k with
  | zero => exact continuous_const
  | succ k => exact Real.continuous_cos.comp (continuous_const.mul continuous_id)

theorem integral_dirichletTerm (k : ℕ) :
    ∫ t in -π..π, dirichletTerm k t = if k = 0 then π else 0 := by
  cases k with
  | zero => simp; ring
  | succ k =>
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    simp only [dirichletTerm_succ, Nat.succ_ne_zero, if_false]
    rw [intervalIntegral.integral_comp_mul_left (fun t ↦ cos t) hk, integral_cos, mul_neg,
      sin_neg, show ((k : ℝ) + 1) * π = ((k + 1 : ℕ) : ℝ) * π by push_cast; ring, sin_nat_mul_pi]
    simp

/-- The Dirichlet kernel `D_n(t) = 1/2 + ∑_{k=1}^n cos kt` (Wheeden–Zygmund, p. 222). -/
noncomputable def dirichletKernel (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), dirichletTerm k t

@[simp]
theorem dirichletKernel_zero (t : ℝ) : dirichletKernel 0 t = 1 / 2 := by
  simp [dirichletKernel]

theorem dirichletKernel_succ (n : ℕ) (t : ℝ) :
    dirichletKernel (n + 1) t = dirichletKernel n t + cos ((n + 1) * t) := by
  simp only [dirichletKernel, sum_range_succ, dirichletTerm_succ]

theorem dirichletKernel_eq (n : ℕ) (t : ℝ) :
    dirichletKernel n t = 1 / 2 + ∑ k ∈ Icc 1 n, cos (k * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [dirichletKernel_succ, ih, sum_Icc_succ_top (by omega)]
    push_cast
    ring

theorem dirichletKernel_neg (n : ℕ) (t : ℝ) : dirichletKernel n (-t) = dirichletKernel n t := by
  simp only [dirichletKernel, dirichletTerm_neg]

theorem dirichletKernel_add_two_pi (n : ℕ) (t : ℝ) :
    dirichletKernel n (t + 2 * π) = dirichletKernel n t := by
  simp only [dirichletKernel, dirichletTerm_add_two_pi]

@[fun_prop]
theorem continuous_dirichletKernel (n : ℕ) : Continuous (dirichletKernel n) :=
  continuous_finsetSum _ fun k _ ↦ continuous_dirichletTerm k

theorem abs_dirichletKernel_le (n : ℕ) (t : ℝ) : |dirichletKernel n t| ≤ n + 1 / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [dirichletKernel_succ]
    calc |dirichletKernel n t + cos ((n + 1) * t)|
        ≤ |dirichletKernel n t| + |cos ((n + 1) * t)| := abs_add_le _ _
      _ ≤ (n + 1 / 2) + 1 := add_le_add ih (abs_cos_le_one _)
      _ = ((n + 1 : ℕ) : ℝ) + 1 / 2 := by push_cast; ring

/-- (12.25): `π⁻¹ ∫_{-π}^{π} D_n(t) dt = 1`. -/
theorem integral_dirichletKernel (n : ℕ) : ∫ t in -π..π, dirichletKernel n t = π := by
  simp only [dirichletKernel]
  rw [intervalIntegral.integral_finsetSum
    fun k _ ↦ (continuous_dirichletTerm k).intervalIntegrable _ _]
  simp [integral_dirichletTerm]

/-- (12.26), multiplied out: `D_n(t) · 2 sin(t/2) = sin((n + 1/2) t)`. -/
theorem dirichletKernel_mul_two_sin (n : ℕ) (t : ℝ) :
    dirichletKernel n t * (2 * sin (t / 2)) = sin ((n + 1 / 2) * t) := by
  induction n with
  | zero => simp; ring_nf
  | succ n ih =>
    rw [dirichletKernel_succ, add_mul, ih,
      show ((n : ℝ) + 1 / 2) * t = (n + 1) * t - t / 2 by ring,
      show (((n + 1 : ℕ) : ℝ) + 1 / 2) * t = (n + 1) * t + t / 2 by push_cast; ring,
      sin_sub, sin_add]
    ring

/-- (12.26): `D_n(t) = sin((n + 1/2) t) / (2 sin(t/2))`. -/
theorem dirichletKernel_eq_div (n : ℕ) {t : ℝ} (ht : sin (t / 2) ≠ 0) :
    dirichletKernel n t = sin ((n + 1 / 2) * t) / (2 * sin (t / 2)) := by
  rw [eq_div_iff (mul_ne_zero two_ne_zero ht), dirichletKernel_mul_two_sin]

/-! ### The Fejér kernel -/

/-- The Fejér kernel `K_n = (D_0 + ⋯ + D_n)/(n + 1)` (Wheeden–Zygmund, p. 235): the arithmetic
mean of the partial sums of `1/2 + cos t + cos 2t + ⋯`. -/
noncomputable def fejerKernel (n : ℕ) (t : ℝ) : ℝ :=
  cesaroMean (fun k ↦ dirichletTerm k t) n

theorem fejerKernel_eq_mean (n : ℕ) (t : ℝ) :
    fejerKernel n t = ((n : ℝ) + 1)⁻¹ * ∑ j ∈ range (n + 1), dirichletKernel j t :=
  rfl

/-- `K_n(t) = 1/2 + ∑_{m=1}^n (1 - m/(n+1)) cos mt`, an instance of (12.39). -/
theorem fejerKernel_eq_sum_cos (n : ℕ) (t : ℝ) :
    fejerKernel n t = 1 / 2 + ∑ m ∈ range n, (1 - (m + 1) / (n + 1)) * cos ((m + 1) * t) := by
  rw [fejerKernel, cesaroMean_eq_sum, sum_range_succ']
  simp only [smul_eq_mul, dirichletTerm_succ, dirichletTerm_zero, Nat.cast_zero, zero_div,
    sub_zero, one_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem fejerKernel_neg (n : ℕ) (t : ℝ) : fejerKernel n (-t) = fejerKernel n t := by
  simp only [fejerKernel_eq_mean, dirichletKernel_neg]

theorem fejerKernel_add_two_pi (n : ℕ) (t : ℝ) :
    fejerKernel n (t + 2 * π) = fejerKernel n t := by
  simp only [fejerKernel_eq_mean, dirichletKernel_add_two_pi]

@[fun_prop]
theorem continuous_fejerKernel (n : ℕ) : Continuous (fejerKernel n) := by
  simp only [funext (fejerKernel_eq_mean n)]
  fun_prop

/-- (12.46), multiplied out: `K_n(t) · (n + 1)(2 sin(t/2))² = 1 - cos (n+1)t`. -/
theorem fejerKernel_mul_two_sin_sq (n : ℕ) (t : ℝ) :
    fejerKernel n t * ((n + 1) * (2 * sin (t / 2)) ^ 2) = 1 - cos ((n + 1) * t) := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hterm : ∀ j : ℕ, dirichletKernel j t * (2 * sin (t / 2)) * (2 * sin (t / 2)) =
      cos ((j : ℕ) * t) - cos (((j + 1 : ℕ) : ℝ) * t) := fun j ↦ by
    rw [dirichletKernel_mul_two_sin,
      show ((j : ℝ)) * t = (j + 1 / 2) * t - t / 2 by ring,
      show ((j + 1 : ℕ) : ℝ) * t = (j + 1 / 2) * t + t / 2 by push_cast; ring,
      cos_sub, cos_add]
    ring
  calc fejerKernel n t * ((n + 1) * (2 * sin (t / 2)) ^ 2)
      = ∑ j ∈ range (n + 1), dirichletKernel j t * (2 * sin (t / 2)) * (2 * sin (t / 2)) := by
        rw [fejerKernel_eq_mean, show ∀ a b c : ℝ, (a⁻¹ * b) * (a * c) = b * c * (a⁻¹ * a) from
          fun a b c ↦ by ring, inv_mul_cancel₀ hn, mul_one, sum_mul]
        exact sum_congr rfl fun j _ ↦ by ring
    _ = ∑ j ∈ range (n + 1), (cos ((j : ℕ) * t) - cos (((j + 1 : ℕ) : ℝ) * t)) :=
        sum_congr rfl fun j _ ↦ hterm j
    _ = 1 - cos ((n + 1) * t) := by
        rw [sum_range_sub' (fun j : ℕ ↦ cos ((j : ℝ) * t))]
        push_cast
        simp

/-- (12.46): `K_n(t) = (2/(n+1)) (sin((n+1)t/2) / (2 sin(t/2)))²`. -/
theorem fejerKernel_eq_sq (n : ℕ) {t : ℝ} (ht : sin (t / 2) ≠ 0) :
    fejerKernel n t = 2 / (n + 1) * (sin ((n + 1) * t / 2) / (2 * sin (t / 2))) ^ 2 := by
  have h2 : (2 * sin (t / 2)) ≠ 0 := mul_ne_zero two_ne_zero ht
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hcos : cos ((n + 1) * t) = 1 - 2 * sin ((n + 1) * t / 2) ^ 2 := by
    have h := cos_two_mul ((n + 1) * t / 2)
    rw [show 2 * (((n : ℝ) + 1) * t / 2) = (n + 1) * t by ring] at h
    rw [h]
    nlinarith [sin_sq_add_cos_sq ((n + 1) * t / 2)]
  have hP : ((n : ℝ) + 1) * (2 * sin (t / 2)) ^ 2 ≠ 0 := mul_ne_zero hn (pow_ne_zero 2 h2)
  have hK : fejerKernel n t =
      (1 - cos ((n + 1) * t)) / (((n : ℝ) + 1) * (2 * sin (t / 2)) ^ 2) := by
    rw [eq_div_iff hP, fejerKernel_mul_two_sin_sq]
  rw [hK, hcos, div_pow]
  set θ := ((n : ℝ) + 1) * t / 2
  set σ := 2 * sin (t / 2)
  field_simp
  ring

/-- Property (a) of `K_n`: the Fejér kernel is nonnegative. -/
theorem fejerKernel_nonneg (n : ℕ) (t : ℝ) : 0 ≤ fejerKernel n t := by
  by_cases h : sin (t / 2) = 0
  · -- `t ∈ 2πℤ`, where every `cos kt` equals `1`.
    obtain ⟨m, hm⟩ := sin_eq_zero_iff.1 h
    have ht : t = 2 * (m * π) := by linarith
    have hcos : ∀ k : ℕ, cos ((k + 1) * t) = 1 := fun k ↦ by
      rw [show ((k : ℝ) + 1) * t = (((k + 1 : ℕ) * m : ℤ) : ℝ) * (2 * π) by
        rw [ht]; push_cast; ring]
      exact cos_int_mul_two_pi _
    rw [fejerKernel_eq_mean]
    refine mul_nonneg (by positivity) (sum_nonneg fun j _ ↦ sum_nonneg fun k _ ↦ ?_)
    cases k with
    | zero => norm_num
    | succ k => simp [hcos k]
  · have hP : 0 < ((n : ℝ) + 1) * (2 * sin (t / 2)) ^ 2 :=
      mul_pos (by positivity) (lt_of_le_of_ne (sq_nonneg _)
        (Ne.symm (pow_ne_zero 2 (mul_ne_zero two_ne_zero h))))
    have h1 : 0 ≤ fejerKernel n t * ((n + 1) * (2 * sin (t / 2)) ^ 2) := by
      rw [fejerKernel_mul_two_sin_sq]
      linarith [cos_le_one ((n + 1) * t)]
    exact (mul_nonneg_iff_of_pos_right hP).1 h1

/-- Property (b) of `K_n`: `π⁻¹ ∫_{-π}^{π} K_n(t) dt = 1`. -/
theorem integral_fejerKernel (n : ℕ) : ∫ t in -π..π, fejerKernel n t = π := by
  simp only [fejerKernel_eq_mean]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    fun j _ ↦ (continuous_dirichletKernel j).intervalIntegrable _ _]
  simp only [integral_dirichletKernel, sum_const, card_range, nsmul_eq_mul]
  push_cast
  field_simp

/-- `∫_0^π K_n(t) dt = π/2`. -/
theorem integral_fejerKernel_zero_pi (n : ℕ) : ∫ t in (0 : ℝ)..π, fejerKernel n t = π / 2 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fejerKernel n) volume a b := fun a b ↦
    (continuous_fejerKernel n).intervalIntegrable a b
  have hsym : ∫ t in -π..0, fejerKernel n t = ∫ t in (0 : ℝ)..π, fejerKernel n t := by
    have := intervalIntegral.integral_comp_neg (f := fejerKernel n) (a := -π) (b := 0)
    simpa only [neg_zero, neg_neg, fejerKernel_neg] using this
  have h := integral_add_adjacent_intervals (hint (-π) 0) (hint 0 π)
  rw [integral_fejerKernel, hsym] at h
  linarith

theorem sum_range_add_half (n : ℕ) : ∑ j ∈ range (n + 1), ((j : ℝ) + 1 / 2) = (n + 1) ^ 2 / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- First half of property (c) of `K_n`: `K_n(t) ≤ (n + 1)/2`. -/
theorem fejerKernel_le (n : ℕ) (t : ℝ) : fejerKernel n t ≤ (n + 1) / 2 := by
  rw [fejerKernel_eq_mean]
  have h : ∑ j ∈ range (n + 1), dirichletKernel j t ≤ ∑ j ∈ range (n + 1), ((j : ℝ) + 1 / 2) :=
    sum_le_sum fun j _ ↦ (le_abs_self _).trans (abs_dirichletKernel_le j t)
  rw [sum_range_add_half] at h
  calc ((n : ℝ) + 1)⁻¹ * ∑ j ∈ range (n + 1), dirichletKernel j t
      ≤ ((n : ℝ) + 1)⁻¹ * ((n + 1) ^ 2 / 2) := by gcongr
    _ = (n + 1) / 2 := by field_simp

/-- Second half of property (c) of `K_n`: `K_n(t) ≤ A / ((n + 1) t²)` for `0 < |t| ≤ π`, with
`A = π²/2`. -/
theorem fejerKernel_le_div_sq (n : ℕ) {t : ℝ} (ht : t ≠ 0) (htπ : |t| ≤ π) :
    fejerKernel n t ≤ π ^ 2 / (2 * (n + 1) * t ^ 2) := by
  have key : ∀ t : ℝ, 0 < t → t ≤ π → fejerKernel n t ≤ π ^ 2 / (2 * (n + 1) * t ^ 2) := by
    intro t ht htπ
    have hs : t / π ≤ sin (t / 2) := by
      have := mul_le_sin (by linarith : 0 ≤ t / 2) (by linarith : t / 2 ≤ π / 2)
      calc t / π = 2 / π * (t / 2) := by field_simp
        _ ≤ _ := this
    have htπ0 : 0 < t / π := by positivity
    have hsin : 0 < sin (t / 2) := htπ0.trans_le hs
    have hP : 0 < ((n : ℝ) + 1) * (2 * sin (t / 2)) ^ 2 := by positivity
    have hle : fejerKernel n t * (((n : ℝ) + 1) * (2 * sin (t / 2)) ^ 2) ≤ 2 := by
      rw [fejerKernel_mul_two_sin_sq]; linarith [neg_one_le_cos ((n + 1) * t)]
    calc fejerKernel n t ≤ 2 / (((n : ℝ) + 1) * (2 * sin (t / 2)) ^ 2) := by
          rw [le_div_iff₀ hP]; exact hle
      _ ≤ 2 / (((n : ℝ) + 1) * (2 * (t / π)) ^ 2) := by gcongr
      _ = π ^ 2 / (2 * (n + 1) * t ^ 2) := by field_simp
  rcases lt_or_gt_of_ne ht with h | h
  · rw [← fejerKernel_neg, show t ^ 2 = (-t) ^ 2 by ring]
    exact key (-t) (by linarith) (by rw [abs_of_neg h] at htπ; linarith)
  · exact key t h (by rwa [abs_of_pos h] at htπ)

/-- Property (c) in the form used in the proof of (12.47): `K_n(t) ≤ π² / (2 (n+1) δ²)` for
`δ ≤ |t| ≤ π`. -/
theorem fejerKernel_le_of_le_abs (n : ℕ) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ |t|) (htπ : |t| ≤ π) :
    fejerKernel n t ≤ π ^ 2 / (2 * (n + 1) * δ ^ 2) := by
  have ht : t ≠ 0 := by rintro rfl; simp at hδt; linarith
  refine (fejerKernel_le_div_sq n ht htπ).trans ?_
  have : δ ^ 2 ≤ t ^ 2 := by rw [← sq_abs t]; gcongr
  gcongr

/-- Property (c') of `K_n`: `∫_δ^π K_n → 0` for `0 < δ ≤ π`. -/
theorem tendsto_integral_fejerKernel {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    Tendsto (fun n ↦ ∫ t in δ..π, fejerKernel n t) atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ, ∫ t in δ..π, fejerKernel n t ≤
      (π - δ) * (π ^ 2 / (2 * δ ^ 2)) * (1 / ((n : ℝ) + 1)) := fun n ↦ by
    calc ∫ t in δ..π, fejerKernel n t ≤ ∫ _t in δ..π, π ^ 2 / (2 * (n + 1) * δ ^ 2) := by
          refine intervalIntegral.integral_mono_on hδπ
            ((continuous_fejerKernel n).intervalIntegrable _ _)
            intervalIntegral.intervalIntegrable_const
            fun t ht ↦ fejerKernel_le_of_le_abs n hδ ?_ ?_
          · rw [abs_of_pos (hδ.trans_le ht.1)]; exact ht.1
          · rw [abs_of_pos (hδ.trans_le ht.1)]; exact ht.2
      _ = (π - δ) * (π ^ 2 / (2 * δ ^ 2)) * (1 / ((n : ℝ) + 1)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; field_simp
  have hlim : Tendsto (fun n : ℕ ↦ (π - δ) * (π ^ 2 / (2 * δ ^ 2)) * (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((π - δ) * (π ^ 2 / (2 * δ ^ 2)))
    rwa [mul_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n ↦ ?_) hbound
  exact intervalIntegral.integral_nonneg hδπ fun t _ ↦ fejerKernel_nonneg n t

/-! ### The basic estimate behind Fejér's theorem -/

/-- The estimate in the proof of Fejér's theorem (12.47): if `‖g(t) - L‖ ≤ ε` for `|t| < δ`, then
`‖∫_α^β (g(t) - L) K_n(t) dt‖ ≤ ε ∫_α^β K_n + (π² / (2(n+1)δ²)) ∫_α^β (‖g‖ + ‖L‖)`, since
`K_n ≤ π² / (2(n+1)δ²)` for `δ ≤ |t| ≤ π`. -/
theorem norm_integral_sub_mul_fejerKernel_le {g : ℝ → ℂ} {L : ℂ} {α β ε δ : ℝ} (n : ℕ)
    (hαβ : α ≤ β) (hα : -π ≤ α) (hβ : β ≤ π) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hg : IntervalIntegrable g volume α β) (hgL : ∀ t ∈ Set.Ioo α β, |t| < δ → ‖g t - L‖ ≤ ε) :
    ‖∫ t in α..β, (g t - L) * fejerKernel n t‖ ≤
      ε * (∫ t in α..β, fejerKernel n t) +
        π ^ 2 / (2 * (n + 1) * δ ^ 2) * ∫ t in α..β, (‖g t‖ + ‖L‖) := by
  set κ := π ^ 2 / (2 * (n + 1) * δ ^ 2)
  have hκ : 0 ≤ κ := by positivity
  have hK : Continuous (fejerKernel n) := continuous_fejerKernel n
  have hKint : IntervalIntegrable (fejerKernel n) volume α β := hK.intervalIntegrable _ _
  have hgn : IntervalIntegrable (fun t ↦ ‖g t‖ + ‖L‖) volume α β :=
    hg.norm.add (continuous_const.intervalIntegrable α β)
  calc ‖∫ t in α..β, (g t - L) * fejerKernel n t‖
      ≤ ∫ t in α..β, ‖(g t - L) * fejerKernel n t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hαβ
    _ ≤ ∫ t in α..β, (ε * fejerKernel n t + κ * (‖g t‖ + ‖L‖)) := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo hαβ ?_ ?_ fun t ht ↦ ?_
        · exact ((hg.sub (continuous_const.intervalIntegrable α β)).mul_continuousOn
            (Complex.continuous_ofReal.comp hK).continuousOn).norm
        · exact (hKint.const_mul ε).add (hgn.const_mul κ)
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg n t)]
          have hK0 := fejerKernel_nonneg n t
          by_cases htδ : |t| < δ
          · have h1 : ‖g t - L‖ * fejerKernel n t ≤ ε * fejerKernel n t :=
              mul_le_mul_of_nonneg_right (hgL t ht htδ) hK0
            have h2 : 0 ≤ κ * (‖g t‖ + ‖L‖) := by positivity
            linarith
          · replace htδ : δ ≤ |t| := not_lt.1 htδ
            have hKt : fejerKernel n t ≤ κ :=
              fejerKernel_le_of_le_abs n hδ htδ (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)
            have h2 : ‖g t - L‖ * fejerKernel n t ≤ κ * (‖g t‖ + ‖L‖) := by
              rw [mul_comm κ]
              exact mul_le_mul (norm_sub_le _ _) hKt hK0 (by positivity)
            have h3 : 0 ≤ ε * fejerKernel n t := mul_nonneg hε hK0
            linarith
    _ = ε * (∫ t in α..β, fejerKernel n t) + κ * ∫ t in α..β, (‖g t‖ + ‖L‖) := by
        rw [intervalIntegral.integral_add (hKint.const_mul ε) (hgn.const_mul κ),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

end FourierSeries
