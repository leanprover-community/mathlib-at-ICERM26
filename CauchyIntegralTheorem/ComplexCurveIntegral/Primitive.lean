/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module

public import ComplexCurveIntegral.Basic
public import PiecewiseC1.Adapter
public import Mathlib.Analysis.Complex.HasPrimitives

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

/--
Fundamental theorem of calculus for complex curve integrals, stated with an explicit derivative
of `F ∘ γ` and an explicit integrability hypothesis.
-/
lemma complexCurveIntegral_eq_sub_of_hasDerivAt_comp
    {a b : ℂ} (f F : ℂ → ℂ) (γ : Path a b)
    (hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt
        (fun t : ℝ => F (γ.extend t))
        (f (γ.extend t) * deriv (⇑γ.extend) t)
        t)
    (hint : IntervalIntegrable
      (fun t : ℝ => f (γ.extend t) * deriv (⇑γ.extend) t)
      volume 0 1) :
    complexCurveIntegral f γ = F b - F a := by
  rw [complexCurveIntegral, curveIntegral_eq_intervalIntegral_deriv]
  simp [fdzForm]
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa using hFTC

/--
If `F` is a primitive for `f` along a differentiable path, then the complex curve integral of
`f` is `F b - F a`. This low-level form keeps differentiability and integrability hypotheses
explicit.
-/
theorem complexCurveIntegral_eq_sub_of_hasPrimitiveOn
    {a b : ℂ} {U : Set ℂ} {f F : ℂ → ℂ} {γ : Path a b}
    (hγU : ∀ t ∈ Set.uIcc (0 : ℝ) 1, γ.extend t ∈ U)
    (hF : ∀ z ∈ U,
      HasFDerivAt F ((fdzForm f z).restrictScalars ℝ) z)
    (hγderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt γ.extend (deriv (⇑γ.extend) t) t)
    (hint : IntervalIntegrable
      (fun t : ℝ => f (γ.extend t) * deriv (⇑γ.extend) t)
      volume 0 1) :
    complexCurveIntegral f γ = F b - F a := by
  refine complexCurveIntegral_eq_sub_of_hasDerivAt_comp f F γ ?_ hint
  intro t ht
  have hcomp :=
    (hF (γ.extend t) (hγU t ht)).comp_hasDerivAt t (hγderiv t ht)
  simpa [fdzForm] using hcomp

/--
Auxiliary primitive theorem for piecewise-`C¹` paths.

This version keeps integrability of the complex curve integrand as an explicit hypothesis. For
open exact domains, prefer `complexCurveIntegral_eq_sub_of_isExactOn_piecewiseC1`, which derives
that integrability from continuity of the derivative on the path image.
-/
lemma complexCurveIntegral_eq_sub_of_hasPrimitiveOn_piecewiseC1
    {a b : ℂ} {U : Set ℂ} {f F : ℂ → ℂ} {γ : Path a b}
    (hγC1 : γ.IsPiecewiseC1)
    (hγU : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ U)
    (hF : ∀ z ∈ U,
      HasFDerivAt F ((fdzForm f z).restrictScalars ℝ) z)
    -- Keep this explicit at first; later prove it from continuity of `f` + piecewise C¹.
    (hint :
      IntervalIntegrable
        (complexCurveIntegrand f γ)
        volume
        0 1) :
    complexCurveIntegral f γ = F b - F a := by
  rw [complexCurveIntegral_eq_intervalIntegral_deriv]
  change
    (∫ t in (0 : ℝ)..1, complexCurveIntegrand f γ t) = F b - F a
  rcases hγC1.exists_subdivision with
    ⟨n, hn, ts, hts0, hts1, hts_mem, hstrict, hC1⟩
  let G : ℝ → ℂ := fun t => F (γ.extend t)
  let as : ℕ → ℝ := fun k =>
    if hk : k ≤ n then ts ⟨k, Nat.lt_succ_of_le hk⟩ else 0
  have has0 : as 0 = 0 := by
    simp [as, hts0]
  have hasn : as n = 1 := by
    simp [as, hts1]
  have hpiece_int :
      ∀ k < n, IntervalIntegrable (complexCurveIntegrand f γ) volume (as k) (as (k + 1)) := by
    intro k hk
    refine hint.mono_set ?_
    have hsub : [[as k, as (k + 1)]] ⊆ [[(0 : ℝ), 1]] := by
      apply uIcc_subset_uIcc
      · have hk_le : k ≤ n := Nat.le_of_lt hk
        have has_k : as k = ts ⟨k, Nat.lt_succ_of_le hk_le⟩ := by
          simp [as, hk_le]
        rw [has_k]
        simpa [uIcc_of_le zero_le_one] using
          (hts_mem ⟨k, Nat.lt_succ_of_le hk_le⟩)
      · have hks_le : k + 1 ≤ n := Nat.succ_le_iff.mpr hk
        have has_succ : as (k + 1) = ts ⟨k + 1, Nat.lt_succ_of_le hks_le⟩ := by
          simp [as, hks_le]
        rw [has_succ]
        simpa [uIcc_of_le zero_le_one] using
          (hts_mem ⟨k + 1, Nat.lt_succ_of_le hks_le⟩)
    simpa [uIcc_of_le zero_le_one] using hsub
  have hpiece_eq :
      ∀ k < n,
        (∫ t in (as k)..(as (k + 1)), complexCurveIntegrand f γ t)
          = G (as (k + 1)) - G (as k) := by
    intro k hk
    let i : Fin n := ⟨k, hk⟩
    have hk_le : k ≤ n := Nat.le_of_lt hk
    have hks_le : k + 1 ≤ n := Nat.succ_le_iff.mpr hk
    have has_k : as k = ts i.castSucc := by
      simp [as, hk_le, i]
    have has_succ : as (k + 1) = ts i.succ := by
      simp [as, hks_le, i]
    have hab : ts i.castSucc ≤ ts i.succ := (hstrict i).le
    have hcont : ContinuousOn G (Icc (ts i.castSucc) (ts i.succ)) := by
      intro t ht
      have htU : γ.extend t ∈ U := by
        apply hγU t
        have hleft0 : (0 : ℝ) ≤ ts i.castSucc := (hts_mem i.castSucc).1
        have hright1 : ts i.succ ≤ (1 : ℝ) := (hts_mem i.succ).2
        exact ⟨hleft0.trans ht.1, ht.2.trans hright1⟩
      exact (hF (γ.extend t) htU).continuousAt.comp_continuousWithinAt
        γ.continuous_extend.continuousWithinAt
    have hderiv : ∀ t ∈ Ioo (ts i.castSucc) (ts i.succ),
        HasDerivWithinAt G (complexCurveIntegrand f γ t) (Ioi t) t := by
      intro t ht
      have htU : γ.extend t ∈ U := by
        apply hγU t
        have hleft0 : (0 : ℝ) ≤ ts i.castSucc := (hts_mem i.castSucc).1
        have hright1 : ts i.succ ≤ (1 : ℝ) := (hts_mem i.succ).2
        exact ⟨hleft0.trans ht.1.le, ht.2.le.trans hright1⟩
      have hγdiffAt : DifferentiableAt ℝ γ.extend t := by
        exact ((hC1 i t ⟨ht.1.le, ht.2.le⟩).differentiableWithinAt one_ne_zero).differentiableAt
          (Icc_mem_nhds ht.1 ht.2)
      have hγderiv : HasDerivWithinAt γ.extend (deriv (⇑γ.extend) t) (Ioi t) t :=
        hγdiffAt.hasDerivAt.hasDerivWithinAt
      have hcomp :=
        (hF (γ.extend t) htU).comp_hasDerivWithinAt t hγderiv
      simpa [G, complexCurveIntegrand, fdzForm] using hcomp
    have hint_i : IntervalIntegrable (complexCurveIntegrand f γ) volume
        (ts i.castSucc) (ts i.succ) := by
      simpa [has_k, has_succ] using hpiece_int k hk
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
        hab hcont hderiv hint_i
    simpa [has_k, has_succ, G] using hFTC
  have hsum_integral :
      (∫ t in (as 0)..(as n), complexCurveIntegrand f γ t)
        = ∑ k ∈ Finset.range n,
            ∫ t in (as k)..(as (k + 1)), complexCurveIntegrand f γ t := by
    exact (intervalIntegral.sum_integral_adjacent_intervals hpiece_int).symm
  rw [← has0, ← hasn, hsum_integral]
  calc
    (∑ k ∈ Finset.range n,
        ∫ t in (as k)..(as (k + 1)), complexCurveIntegrand f γ t)
        = ∑ k ∈ Finset.range n, (G (as (k + 1)) - G (as k)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact hpiece_eq k (Finset.mem_range.mp hk)
    _ = G (as n) - G (as 0) := Finset.sum_range_sub (fun k => G (as k)) n
    _ = F b - F a := by
      simp [G, has0, hasn]

lemma Path.IsPiecewiseC1.intervalIntegrable_complexCurveIntegrand
    {a b : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ : Path a b}
    (hγC1 : γ.IsPiecewiseC1)
    (hγU : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ U)
    (hfU : ContinuousOn f U) :
    IntervalIntegrable
      (complexCurveIntegrand f γ)
      volume
      0 1 := by
  rcases hγC1.exists_subdivision with
    ⟨n, hn, ts, hts0, hts1, hts_mem, hstrict, hC1⟩
  let as : ℕ → ℝ := fun k =>
    if hk : k ≤ n then ts ⟨k, Nat.lt_succ_of_le hk⟩ else 0
  have has0 : as 0 = 0 := by
    simp [as, hts0]
  have hasn : as n = 1 := by
    simp [as, hts1]
  have hpiece :
      ∀ k < n, IntervalIntegrable (complexCurveIntegrand f γ) volume (as k) (as (k + 1)) := by
    intro k hk
    let i : Fin n := ⟨k, hk⟩
    have hk_le : k ≤ n := Nat.le_of_lt hk
    have hks_le : k + 1 ≤ n := Nat.succ_le_iff.mpr hk
    have has_k : as k = ts i.castSucc := by
      simp [as, hk_le, i]
    have has_succ : as (k + 1) = ts i.succ := by
      simp [as, hks_le, i]
    have hab : ts i.castSucc ≤ ts i.succ := (hstrict i).le
    let s : Set ℝ := Icc (ts i.castSucc) (ts i.succ)
    let g : ℝ → ℂ := fun t => f (γ.extend t) * derivWithin γ.extend s t
    have hmaps : Set.MapsTo γ.extend s U := by
      intro t ht
      apply hγU t
      have hleft0 : (0 : ℝ) ≤ ts i.castSucc := (hts_mem i.castSucc).1
      have hright1 : ts i.succ ≤ (1 : ℝ) := (hts_mem i.succ).2
      exact ⟨hleft0.trans ht.1, ht.2.trans hright1⟩
    have hfgamma : ContinuousOn (fun t => f (γ.extend t)) s := by
      exact hfU.comp' γ.continuous_extend.continuousOn hmaps
    have hderivWithin : ContinuousOn (derivWithin γ.extend s) s := by
      simpa [s] using
        (hC1 i).continuousOn_derivWithin (uniqueDiffOn_Icc (hstrict i)) (by norm_num)
    have hg : ContinuousOn g s := by
      exact hfgamma.mul hderivWithin
    have hgint : IntervalIntegrable g volume (ts i.castSucc) (ts i.succ) := by
      exact hg.intervalIntegrable_of_Icc hab
    have hcongr : g =ᵐ[volume.restrict (Ι (ts i.castSucc) (ts i.succ))]
        complexCurveIntegrand f γ := by
      rw [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
      have hderiv_eq :
          derivWithin γ.extend s t = deriv γ.extend t := by
        exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
      simp [g, complexCurveIntegrand, hderiv_eq]
    have hpiece_i : IntervalIntegrable (complexCurveIntegrand f γ) volume
        (ts i.castSucc) (ts i.succ) := hgint.congr_ae hcongr
    simpa [has_k, has_succ] using hpiece_i
  have htotal : IntervalIntegrable (complexCurveIntegrand f γ) volume (as 0) (as n) :=
    IntervalIntegrable.trans_iterate hpiece
  simpa [has0, hasn] using htotal

lemma Path.IsPiecewiseC1.curveIntegrable_fdzForm
    {a b : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ : Path a b}
    (hγC1 : γ.IsPiecewiseC1)
    (hγU : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ U)
    (hfU : ContinuousOn f U) :
    CurveIntegrable (fdzForm f) γ := by
  have hint := hγC1.intervalIntegrable_complexCurveIntegrand hγU hfU
  have hcongr :
      curveIntegralFun (fdzForm f) γ =ᵐ[volume.restrict (Ι (0 : ℝ) 1)]
        complexCurveIntegrand f γ := by
    rw [uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [curveIntegralFun_def]
    have hderiv_eq : derivWithin γ.extend I t = deriv γ.extend t := by
      exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    simp [complexCurveIntegrand, fdzForm, hderiv_eq]
  exact hint.congr_ae hcongr.symm

/--
If `f` is exact on an open set containing a piecewise-`C¹` path, then its complex curve integral
depends only on the endpoints.
-/
theorem complexCurveIntegral_eq_sub_of_isExactOn_piecewiseC1
    {a b : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ : Path a b}
    (hU : IsOpen U)
    (hγC1 : γ.IsPiecewiseC1)
    (hγU : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ U)
    (hF : Complex.IsExactOn f U) :
    ∃ F : ℂ → ℂ, complexCurveIntegral f γ = F b - F a := by
  have hfU : ContinuousOn f U := (Complex.IsExactOn.differentiableOn hU hF).continuousOn
  rcases hF with ⟨F, hF⟩
  refine ⟨F, ?_⟩
  refine complexCurveIntegral_eq_sub_of_hasPrimitiveOn_piecewiseC1
    hγC1 hγU ?_ ?_
  · -- Convert the complex derivative of the primitive into the real Fréchet derivative.
    intro z hz
    convert (hF z hz).hasFDerivAt.restrictScalars ℝ using 1
    · ext v
      simp [fdzForm, mul_comm]
    · exact IsScalarTower.complexToReal
    · exact IsScalarTower.complexToReal
  · -- Derive integrability from exactness and piecewise C¹-ness of `γ`.
    exact hγC1.intervalIntegrable_complexCurveIntegrand hγU hfU
