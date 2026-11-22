/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harald Helfgott
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Tactic.Module

/-! # Cesàro means and Hardy's Tauberian theorem

We follow §12.5 ("Summability of Sequences and Series") of Wheeden–Zygmund, *Measure and
Integral* (1977). For a series `∑ u_n` with partial sums `s_n = u_0 + ⋯ + u_n`, the arithmetic
(Cesàro) means are `σ_m = (s_0 + ⋯ + s_m) / (m + 1)`.

## Main results

* `cesaroMean_eq_sum`, `sum_range_sub_cesaroMean`: the two identities (12.39),
  `σ_m = ∑_{k ≤ m} (1 - k/(m+1)) u_k` and `s_m - σ_m = (m+1)⁻¹ ∑_{k ≤ m} k u_k`.
* `norm_sum_range_sub_cesaroMean_le`, `norm_sum_range_le_of_norm_cesaroMean_le`: the remark
  preceding (12.45): if `|u_n| ≤ A/n` for `n ≥ 1`, then `|s_m - σ_m| ≤ A`, so bounded arithmetic
  means give bounded partial sums.
* `norm_sum_range_sub_le`: the estimate behind Hardy's theorem, via the delayed arithmetic means
  `σ_{n,k} = (s_{n+1} + ⋯ + s_{n+k}) / k`.
* `tendsto_sum_range_of_tendsto_cesaroMean`: Hardy's Tauberian theorem (12.45). If `∑ u_n` is
  summable by arithmetic means to `s` and `|u_n| ≤ A/n` for `n ≥ 1`, then `∑ u_n` converges to `s`.
* `tendstoUniformlyOn_sum_range_of_tendstoUniformlyOn_cesaroMean`: the uniform version of (12.45),
  for series depending on a parameter, as used in part (b) of the Dirichlet–Jordan theorem (12.50).

## AI usage

This file was written by Claude (Anthropic) in November 2026. It compiles, but has not been
reviewed by a human.
-/

@[expose] public section

open Filter Finset Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The arithmetic (Cesàro) mean `σ_m = (s_0 + ⋯ + s_m) / (m + 1)` of the partial sums
`s_n = u_0 + ⋯ + u_n` of the series `∑ u_n` (Wheeden–Zygmund, §12.5(a)). -/
noncomputable def cesaroMean (u : ℕ → E) (m : ℕ) : E :=
  ((m : ℝ) + 1)⁻¹ • ∑ n ∈ range (m + 1), ∑ k ∈ range (n + 1), u k

/-- `(m + 1) s_m - (s_0 + ⋯ + s_m) = ∑_{k ≤ m} k u_k`. -/
theorem add_one_smul_sum_range_sub_sum_range (u : ℕ → E) (m : ℕ) :
    ((m : ℝ) + 1) • ∑ k ∈ range (m + 1), u k -
        ∑ n ∈ range (m + 1), ∑ k ∈ range (n + 1), u k =
      ∑ k ∈ range (m + 1), (k : ℝ) • u k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ (fun n ↦ ∑ k ∈ range (n + 1), u k), sum_range_succ u (m + 1),
      sum_range_succ (fun k ↦ (k : ℝ) • u k), ← ih]
    push_cast
    module

/-- The second identity in (12.39): `s_m - σ_m = (m + 1)⁻¹ ∑_{k ≤ m} k u_k`. -/
theorem sum_range_sub_cesaroMean (u : ℕ → E) (m : ℕ) :
    ∑ k ∈ range (m + 1), u k - cesaroMean u m =
      ((m : ℝ) + 1)⁻¹ • ∑ k ∈ range (m + 1), (k : ℝ) • u k := by
  rw [← add_one_smul_sum_range_sub_sum_range, smul_sub, smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul, cesaroMean]

/-- The first identity in (12.39): `σ_m = ∑_{k ≤ m} (1 - k/(m+1)) u_k`. -/
theorem cesaroMean_eq_sum (u : ℕ → E) (m : ℕ) :
    cesaroMean u m = ∑ k ∈ range (m + 1), (1 - (k : ℝ) / (m + 1)) • u k := by
  have h : cesaroMean u m = ∑ k ∈ range (m + 1), u k -
      ((m : ℝ) + 1)⁻¹ • ∑ k ∈ range (m + 1), (k : ℝ) • u k := by
    rw [← sum_range_sub_cesaroMean, sub_sub_cancel]
  rw [h, smul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [smul_smul, sub_smul, one_smul, div_eq_inv_mul]

/-- The remark preceding (12.45): if `|u_n| ≤ A/n` for `n ≥ 1`, the partial sums differ from
their arithmetic means by at most `A`. -/
theorem norm_sum_range_sub_cesaroMean_le {u : ℕ → E} {A : ℝ}
    (hu : ∀ n, 1 ≤ n → ‖u n‖ ≤ A / n) (m : ℕ) :
    ‖∑ k ∈ range (m + 1), u k - cesaroMean u m‖ ≤ A := by
  have hA : 0 ≤ A := by simpa using (norm_nonneg _).trans (hu 1 le_rfl)
  have h1 : ‖∑ k ∈ range (m + 1), (k : ℝ) • u k‖ ≤ ((m : ℝ) + 1) * A := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ range (m + 1), ‖(k : ℝ) • u k‖ ≤ ∑ _k ∈ range (m + 1), A := by
          refine sum_le_sum fun k _ ↦ ?_
          rw [norm_smul, Real.norm_natCast]
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simpa using hA
          · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
            calc (k : ℝ) * ‖u k‖ ≤ k * (A / k) := by gcongr; exact hu k hk
              _ = A := by field_simp
      _ = ((m : ℝ) + 1) * A := by simp
  rw [sum_range_sub_cesaroMean, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
  calc ((m : ℝ) + 1)⁻¹ * ‖∑ k ∈ range (m + 1), (k : ℝ) • u k‖
      ≤ ((m : ℝ) + 1)⁻¹ * (((m : ℝ) + 1) * A) := by gcongr
    _ = A := by field_simp

/-- If the arithmetic means of `∑ u_n` are bounded by `M` and `|u_n| ≤ A/n` for `n ≥ 1`, then the
partial sums are bounded by `M + A` (the remark preceding (12.45)). -/
theorem norm_sum_range_le_of_norm_cesaroMean_le {u : ℕ → E} {A M : ℝ}
    (hu : ∀ n, 1 ≤ n → ‖u n‖ ≤ A / n) (hσ : ∀ m, ‖cesaroMean u m‖ ≤ M) (m : ℕ) :
    ‖∑ k ∈ range (m + 1), u k‖ ≤ M + A :=
  calc ‖∑ k ∈ range (m + 1), u k‖
      = ‖cesaroMean u m + (∑ k ∈ range (m + 1), u k - cesaroMean u m)‖ := by
        rw [add_sub_cancel]
    _ ≤ ‖cesaroMean u m‖ + ‖∑ k ∈ range (m + 1), u k - cesaroMean u m‖ := norm_add_le _ _
    _ ≤ M + A := add_le_add (hσ m) (norm_sum_range_sub_cesaroMean_le hu m)

/-- The estimate behind Hardy's theorem (12.45). Comparing `s_n` with the delayed arithmetic mean
`σ_{n,k} = (s_{n+1} + ⋯ + s_{n+k}) / k`, which is close to `s_n` when `|u_j| ≤ A/j`, gives
`|s_n - s| ≤ ((n+k+1)/k) |σ_{n+k} - s| + ((n+1)/k) |σ_n - s| + k A / (n + 1)`.

The proof uses `σ_{n,k} = ((n+k+1)/k) σ_{n+k} - ((n+1)/k) σ_n`, since `s_0 + ⋯ + s_m = (m+1) σ_m`.
(The display on p. 235 of Wheeden–Zygmund has `n/k` in place of `(n+1)/k`; this does not affect
the argument.) -/
theorem norm_sum_range_sub_le {u : ℕ → E} {A : ℝ} (hu : ∀ n, 1 ≤ n → ‖u n‖ ≤ A / n) (s : E)
    (n : ℕ) {k : ℕ} (hk : 0 < k) :
    ‖∑ j ∈ range (n + 1), u j - s‖ ≤
      (n + k + 1) / k * ‖cesaroMean u (n + k) - s‖ + (n + 1) / k * ‖cesaroMean u n - s‖ +
        k * A / (n + 1) := by
  have hA : 0 ≤ A := by simpa using (norm_nonneg _).trans (hu 1 le_rfl)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set S : ℕ → E := fun m ↦ ∑ j ∈ range (m + 1), u j with hS
  set T : ℕ → E := fun m ↦ ∑ j ∈ range (m + 1), S j with hT
  have hTσ : ∀ m, T m = ((m : ℝ) + 1) • cesaroMean u m := fun m ↦ by
    rw [cesaroMean, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  -- `S (n + 1 + j) - S n` is a sum of `j + 1 ≤ k` terms of size at most `A / (n + 1)`.
  have hstep : ∀ j < k, ‖S (n + 1 + j) - S n‖ ≤ k * A / (n + 1) := by
    intro j hj
    have hsplit : S (n + 1 + j) - S n = ∑ i ∈ range (j + 1), u (n + 1 + i) := by
      simp only [hS]
      rw [show n + 1 + j + 1 = (n + 1) + (j + 1) by ring, sum_range_add, add_sub_cancel_left]
    rw [hsplit]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ range (j + 1), ‖u (n + 1 + i)‖ ≤ ∑ _i ∈ range (j + 1), A / (n + 1) := by
          refine sum_le_sum fun i _ ↦ (hu _ (by omega)).trans ?_
          gcongr
          push_cast
          linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      _ = (j + 1) * (A / (n + 1)) := by simp
      _ ≤ k * A / (n + 1) := by
          rw [mul_div_assoc]
          gcongr
          exact_mod_cast hj
  have hdelay : ‖T (n + k) - T n - (k : ℝ) • S n‖ ≤ k * (k * A / (n + 1)) := by
    have : T (n + k) - T n - (k : ℝ) • S n = ∑ j ∈ range k, (S (n + 1 + j) - S n) := by
      simp only [hT]
      rw [show n + k + 1 = (n + 1) + k by ring, sum_range_add, add_sub_cancel_left,
        sum_sub_distrib, sum_const, card_range, Nat.cast_smul_eq_nsmul]
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ range k, ‖S (n + 1 + j) - S n‖ ≤ ∑ _j ∈ range k, k * A / (n + 1) :=
          sum_le_sum fun j hj ↦ hstep j (mem_range.1 hj)
      _ = k * (k * A / (n + 1)) := by simp
  -- `k (s_n - s) = (n + k + 1)(σ_{n+k} - s) - (n + 1)(σ_n - s) - (T_{n+k} - T_n - k s_n)`.
  have hkey : (k : ℝ) • (S n - s) =
      ((n : ℝ) + k + 1) • (cesaroMean u (n + k) - s) - ((n : ℝ) + 1) • (cesaroMean u n - s) -
        (T (n + k) - T n - (k : ℝ) • S n) := by
    rw [hTσ, hTσ]
    push_cast
    module
  have hmain : (k : ℝ) * ‖S n - s‖ ≤
      ((n : ℝ) + k + 1) * ‖cesaroMean u (n + k) - s‖ + ((n : ℝ) + 1) * ‖cesaroMean u n - s‖ +
        k * (k * A / (n + 1)) := by
    calc (k : ℝ) * ‖S n - s‖ = ‖(k : ℝ) • (S n - s)‖ := by
          rw [norm_smul, Real.norm_natCast]
      _ ≤ ‖((n : ℝ) + k + 1) • (cesaroMean u (n + k) - s)‖ +
            ‖((n : ℝ) + 1) • (cesaroMean u n - s)‖ + ‖T (n + k) - T n - (k : ℝ) • S n‖ := by
          rw [hkey]
          exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
            Real.norm_of_nonneg (by positivity)]
          exact add_le_add le_rfl hdelay
  rw [← mul_le_mul_iff_of_pos_left hk']
  calc (k : ℝ) * ‖S n - s‖ ≤ _ := hmain
    _ = (k : ℝ) * ((n + k + 1) / k * ‖cesaroMean u (n + k) - s‖ +
          (n + 1) / k * ‖cesaroMean u n - s‖ + k * A / (n + 1)) := by
        field_simp

/-- **Hardy's Tauberian theorem**, uniform version: if the arithmetic means of the series
`∑_n u i n` converge to `s i` uniformly for `i ∈ S`, and `|u i n| ≤ A/n` for `n ≥ 1` and `i ∈ S`,
then the series converge to `s i` uniformly for `i ∈ S`. -/
theorem tendstoUniformlyOn_sum_range_of_tendstoUniformlyOn_cesaroMean {ι : Type*}
    {u : ι → ℕ → E} {s : ι → E} {S : Set ι} {A : ℝ}
    (hu : ∀ i ∈ S, ∀ n, 1 ≤ n → ‖u i n‖ ≤ A / n)
    (hσ : TendstoUniformlyOn (fun m i ↦ cesaroMean (u i) m) s atTop S) :
    TendstoUniformlyOn (fun n i ↦ ∑ k ∈ range (n + 1), u i k) s atTop S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · exact tendstoUniformlyOn_empty
  have hA : 0 ≤ A := by simpa using (norm_nonneg _).trans (hu i₀ hi₀ 1 le_rfl)
  rw [Metric.tendstoUniformlyOn_iff] at hσ ⊢
  intro δ hδ
  -- `k_n = ⌊ε (n + 1)⌋ + 1` with `ε A < δ / 4`.
  set ε : ℝ := δ / (4 * (A + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hεA : ε * A < δ / 4 := by
    rw [hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set η : ℝ := δ / (4 * (2 / ε + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hηbound : (2 / ε + 1) * η = δ / 4 := by
    rw [hη]; field_simp
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hσ η hηpos)
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, A / (N₂ + 1) < δ / 4 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (4 * A / δ)
    refine ⟨N, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with n hn i hi
  set k : ℕ := ⌊ε * (n + 1)⌋₊ + 1 with hk
  have hkpos : 0 < k := Nat.succ_pos _
  have hk' : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hk_lt : ε * (n + 1) < k := by
    rw [hk]; push_cast; exact Nat.lt_floor_add_one _
  have hk_le : (k : ℝ) ≤ ε * (n + 1) + 1 := by
    rw [hk]; push_cast; linarith [Nat.floor_le (by positivity : 0 ≤ ε * (n + 1))]
  have hratio : ((n : ℝ) + 1) / k ≤ 1 / ε := by
    rw [div_le_div_iff₀ hk' hεpos]; linarith
  have hratio' : ((n : ℝ) + k + 1) / k ≤ 1 / ε + 1 := by
    have : ((n : ℝ) + k + 1) / k = (n + 1) / k + 1 := by field_simp; ring
    rw [this]; linarith
  have hkA : k * A / (n + 1) ≤ ε * A + A / (n + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have : (ε * A + A / (n + 1)) * (n + 1) = ε * (n + 1) * A + A := by field_simp
    rw [this]; nlinarith
  have h1 : ‖cesaroMean (u i) (n + k) - s i‖ < η := by
    rw [← dist_eq_norm, dist_comm]; exact hN₁ _ (by omega) i hi
  have h2 : ‖cesaroMean (u i) n - s i‖ < η := by
    rw [← dist_eq_norm, dist_comm]; exact hN₁ _ (le_of_max_le_left hn) i hi
  have h3 : A / (n + 1) < δ / 4 := by
    refine lt_of_le_of_lt ?_ hN₂
    gcongr
    exact_mod_cast le_of_max_le_right hn
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  calc ‖∑ k ∈ range (n + 1), u i k - s i‖
      ≤ (n + k + 1) / k * ‖cesaroMean (u i) (n + k) - s i‖ +
          (n + 1) / k * ‖cesaroMean (u i) n - s i‖ + k * A / (n + 1) :=
        norm_sum_range_sub_le (hu i hi) (s i) n hkpos
    _ ≤ (1 / ε + 1) * η + 1 / ε * η + (ε * A + A / (n + 1)) := by
        gcongr
    _ = (2 / ε + 1) * η + ε * A + A / (n + 1) := by ring
    _ < δ := by linarith

/-- **Hardy's Tauberian theorem** (Wheeden–Zygmund (12.45)): if `∑ u_n` is summable by the method
of arithmetic means to `s`, and `|u_n| ≤ A/n` for `n ≥ 1`, then `∑ u_n` converges to `s`. -/
theorem tendsto_sum_range_of_tendsto_cesaroMean {u : ℕ → E} {s : E} {A : ℝ}
    (hu : ∀ n, 1 ≤ n → ‖u n‖ ≤ A / n) (hσ : Tendsto (cesaroMean u) atTop (𝓝 s)) :
    Tendsto (fun n ↦ ∑ k ∈ range (n + 1), u k) atTop (𝓝 s) := by
  have h := tendstoUniformlyOn_sum_range_of_tendstoUniformlyOn_cesaroMean (ι := Unit)
    (u := fun _ ↦ u) (s := fun _ ↦ s) (S := {()}) (A := A) (fun _ _ ↦ hu)
    (tendstoUniformlyOn_singleton_iff_tendsto.2 hσ)
  exact tendstoUniformlyOn_singleton_iff_tendsto.1 h
