/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module

public import ComplexCurveIntegral.Primitive

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

/-- Complex curve integrals are additive under concatenation of piecewise-`C¹` paths. -/
lemma complexCurveIntegral_trans_piecewiseC1
    {a b c : ℂ} {f : ℂ → ℂ} {γab : Path a b} {γbc : Path b c}
    {U : Set ℂ}
    (hγabU : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γab.extend t ∈ U)
    (hγbcU : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γbc.extend t ∈ U)
    (hfU : ContinuousOn f U)
    (hγab : γab.IsPiecewiseC1) (hγbc : γbc.IsPiecewiseC1) :
    complexCurveIntegral f (γab.trans γbc) =
      complexCurveIntegral f γab + complexCurveIntegral f γbc := by
  rw [complexCurveIntegral_def, complexCurveIntegral_def, complexCurveIntegral_def]
  exact curveIntegral_trans
    (hγab.curveIntegrable_fdzForm hγabU hfU)
    (hγbc.curveIntegrable_fdzForm hγbcU hfU)

/-- Splitting a piecewise-`C¹` path at `1 / 2` splits its complex curve integral. -/
lemma complexCurveIntegral_subpath_split_two
    {a b : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ : Path a b}
    (hγU : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ U)
    (hfU : ContinuousOn f U)
    (hγC1 : γ.IsPiecewiseC1) :
    complexCurveIntegral f
        (γ.subpath 0 (⟨(1 / 2 : ℝ), by norm_num⟩ : I)) +
      complexCurveIntegral f
        (γ.subpath (⟨(1 / 2 : ℝ), by norm_num⟩ : I) 1) =
        complexCurveIntegral f γ := by
  let m : I := ⟨(1 / 2 : ℝ), by norm_num⟩
  let γ₀ : Path a (γ m) := (γ.subpath 0 m).cast (by simp) rfl
  let γ₁ : Path (γ m) b := (γ.subpath m 1).cast rfl (by simp)
  have hγ₀U : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ₀.extend t ∈ U := by
    intro t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ht
    rw [Path.extend_apply _ ht01]
    have hu :
        ((Set.Icc.convexCombo (0 : I) m ⟨t, ht01⟩ : I) : ℝ) ∈ Icc (0 : ℝ) 1 :=
      (Set.Icc.convexCombo (0 : I) m ⟨t, ht01⟩).2
    have hγu :
        γ.extend ((Set.Icc.convexCombo (0 : I) m ⟨t, ht01⟩ : I) : ℝ) ∈ U :=
      hγU _ hu
    rw [Path.extend_apply γ hu] at hγu
    change γ (Set.Icc.convexCombo (0 : I) m ⟨t, ht01⟩) ∈ U
    convert hγu using 2
  have hγ₁U : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ₁.extend t ∈ U := by
    intro t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ht
    rw [Path.extend_apply _ ht01]
    have hu :
        ((Set.Icc.convexCombo m (1 : I) ⟨t, ht01⟩ : I) : ℝ) ∈ Icc (0 : ℝ) 1 :=
      (Set.Icc.convexCombo m (1 : I) ⟨t, ht01⟩).2
    have hγu :
        γ.extend ((Set.Icc.convexCombo m (1 : I) ⟨t, ht01⟩ : I) : ℝ) ∈ U :=
      hγU _ hu
    rw [Path.extend_apply γ hu] at hγu
    change γ (Set.Icc.convexCombo m (1 : I) ⟨t, ht01⟩) ∈ U
    convert hγu using 2
  have htrans :
      complexCurveIntegral f (γ₀.trans γ₁) =
        complexCurveIntegral f γ₀ + complexCurveIntegral f γ₁ :=
    complexCurveIntegral_trans_piecewiseC1 hγ₀U hγ₁U hfU
      ((hγC1.subpath 0 m).cast (by simp) rfl)
      ((hγC1.subpath m 1).cast rfl (by simp))
  have hγ₀_eq :
      complexCurveIntegral f γ₀ =
        complexCurveIntegral f (γ.subpath 0 m) := by
    simp [γ₀, complexCurveIntegral]
  have hγ₁_eq :
      complexCurveIntegral f γ₁ =
        complexCurveIntegral f (γ.subpath m 1) := by
    simp [γ₁, complexCurveIntegral]
  have hpath : γ₀.trans γ₁ = γ := by
    ext t
    rw [Path.trans_apply]
    split_ifs with ht
    · simp [γ₀, m, Path.subpath, Set.Icc.convexCombo]
      congr 1
      apply Subtype.ext
      ring
    · simp [γ₁, m, Path.subpath, Set.Icc.convexCombo]
      congr 1
      apply Subtype.ext
      ring
  have h := htrans
  rw [hpath, hγ₀_eq, hγ₁_eq] at h
  exact h.symm

/-- Splitting a piecewise-`C¹` path at an arbitrary parameter splits its complex curve integral. -/
lemma complexCurveIntegral_subpath_zero_one_split
    {a b : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ : Path a b}
    (hγU : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ U)
    (hfU : ContinuousOn f U)
    (hγC1 : γ.IsPiecewiseC1)
    (t : I) :
    complexCurveIntegral f (γ.subpath 0 t) +
      complexCurveIntegral f (γ.subpath t 1) =
        complexCurveIntegral f γ := by
  let g : ℝ → ℂ := complexCurveIntegrand f γ
  have hint : IntervalIntegrable g volume (0 : ℝ) 1 := by
    simpa [g] using hγC1.intervalIntegrable_complexCurveIntegrand hγU hfU
  have hint_left : IntervalIntegrable g volume (0 : ℝ) (t : ℝ) :=
    hint.mono_set (Set.uIcc_subset_uIcc
      (by simp : (0 : ℝ) ∈ [[(0 : ℝ), (1 : ℝ)]])
      (by simp only [zero_le_one, uIcc_of_le, Subtype.coe_prop] : (t : ℝ) ∈ [[(0 : ℝ), (1 : ℝ)]]))
  have hint_right : IntervalIntegrable g volume (t : ℝ) 1 :=
    hint.mono_set (Set.uIcc_subset_uIcc
      (by simp only [zero_le_one, uIcc_of_le, Subtype.coe_prop] : (t : ℝ) ∈ [[(0 : ℝ), (1 : ℝ)]])
      (by simp : (1 : ℝ) ∈ [[(0 : ℝ), (1 : ℝ)]]))
  have hleft :
      complexCurveIntegral f (γ.subpath 0 t) =
        ∫ x in (0 : ℝ)..(t : ℝ), g x := by
    rw [complexCurveIntegral_eq_intervalIntegral_deriv]
    change (∫ r in (0 : ℝ)..1,
        f ((γ.subpath 0 t).extend r) * deriv (⇑(γ.subpath 0 t).extend) r) =
      ∫ x in (0 : ℝ)..(t : ℝ), g x
    have hsubst :
        (t : ℝ) • (∫ r in (0 : ℝ)..1, g ((t : ℝ) * r)) =
          ∫ x in (0 : ℝ)..(t : ℝ), g x := by
      simpa only [mul_zero, mul_one] using
        (intervalIntegral.smul_integral_comp_mul_left
          (f := g) (a := (0 : ℝ)) (b := (1 : ℝ)) (t : ℝ))
    rw [← hsubst]
    trans ∫ r in (0 : ℝ)..1, (t : ℝ) • g ((t : ℝ) * r)
    · apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
      have htr01 : (t : ℝ) * r ∈ Icc (0 : ℝ) 1 := by
        constructor <;> nlinarith [t.2.1, t.2.2, hr01.1, hr01.2]
      have Heq : (γ.subpath 0 t).extend =ᶠ[𝓝 r] fun x : ℝ => γ.extend ((t : ℝ) * x) := by
        filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
        have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
        have htx01 : (t : ℝ) * x ∈ Icc (0 : ℝ) 1 := by
          constructor <;> nlinarith [t.2.1, t.2.2, hx01.1, hx01.2]
        rw [Path.extend_apply _ hx01, Path.extend_apply γ htx01]
        simp [Path.subpath, Set.Icc.convexCombo]
        congr 1
        apply Subtype.ext
        ring
      have hval : (γ.subpath 0 t).extend r = γ.extend ((t : ℝ) * r) := Heq.self_of_nhds
      have hderiv :
          deriv (⇑(γ.subpath 0 t).extend) r =
            (t : ℝ) • deriv (⇑γ.extend) ((t : ℝ) * r) := by
        rw [Heq.deriv_eq]
        simpa using deriv_comp_mul_left (t : ℝ) (⇑γ.extend) r
      rw [hval, hderiv]
      rw [mul_smul_comm]
      change (t : ℝ) •
          (f (γ.extend ((t : ℝ) * r)) * deriv (⇑γ.extend) ((t : ℝ) * r)) =
        (t : ℝ) • complexCurveIntegrand f γ ((t : ℝ) * r)
      rw [complexCurveIntegrand_apply]
    · exact (intervalIntegral.integral_smul
        (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (r := (t : ℝ)) (f := fun r : ℝ => g ((t : ℝ) * r)))
  have hright :
      complexCurveIntegral f (γ.subpath t 1) =
        ∫ x in (t : ℝ)..1, g x := by
    rw [complexCurveIntegral_eq_intervalIntegral_deriv]
    change (∫ r in (0 : ℝ)..1,
        f ((γ.subpath t 1).extend r) * deriv (⇑(γ.subpath t 1).extend) r) =
      ∫ x in (t : ℝ)..1, g x
    have hsubst :
        ((1 : ℝ) - (t : ℝ)) •
            (∫ r in (0 : ℝ)..1, g ((t : ℝ) + (1 - (t : ℝ)) * r)) =
          ∫ x in (t : ℝ)..1, g x := by
      simpa only [mul_zero, add_zero, mul_one, add_sub_cancel] using
        (intervalIntegral.smul_integral_comp_add_mul
          (f := g) (a := (0 : ℝ)) (b := (1 : ℝ))
          ((1 : ℝ) - (t : ℝ)) (t : ℝ))
    rw [← hsubst]
    trans ∫ r in (0 : ℝ)..1,
        ((1 : ℝ) - (t : ℝ)) •
          g ((t : ℝ) + (1 - (t : ℝ)) * r)
    · apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
      have hρ01 : (t : ℝ) + (1 - (t : ℝ)) * r ∈ Icc (0 : ℝ) 1 := by
        constructor <;> nlinarith [t.2.1, t.2.2, hr01.1, hr01.2]
      have Heq : (γ.subpath t 1).extend =ᶠ[𝓝 r]
          fun x : ℝ => γ.extend ((t : ℝ) + (1 - (t : ℝ)) * x) := by
        filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
        have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
        have hρx01 : (t : ℝ) + (1 - (t : ℝ)) * x ∈ Icc (0 : ℝ) 1 := by
          constructor <;> nlinarith [t.2.1, t.2.2, hx01.1, hx01.2]
        rw [Path.extend_apply _ hx01, Path.extend_apply γ hρx01]
        simp [Path.subpath, Set.Icc.convexCombo]
        congr 1
        apply Subtype.ext
        ring
      have hval :
          (γ.subpath t 1).extend r =
            γ.extend ((t : ℝ) + (1 - (t : ℝ)) * r) := Heq.self_of_nhds
      have hderiv :
          deriv (⇑(γ.subpath t 1).extend) r =
            ((1 : ℝ) - (t : ℝ)) •
              deriv (⇑γ.extend) ((t : ℝ) + (1 - (t : ℝ)) * r) := by
        rw [Heq.deriv_eq]
        let c : ℝ := (1 : ℝ) - (t : ℝ)
        have hfun :
            (fun x : ℝ => γ.extend ((t : ℝ) + ((1 : ℝ) - (t : ℝ)) * x)) =
              fun x : ℝ => (fun y : ℝ => γ.extend (y + (t : ℝ))) (c * x) := by
          funext x
          congr 1
          simp [c]
          ring
        rw [hfun]
        have hmul :=
          deriv_comp_mul_left c (fun y : ℝ => γ.extend (y + (t : ℝ))) r
        change deriv (fun x : ℝ => (fun y : ℝ => γ.extend (y + (t : ℝ))) (c * x)) r =
          ((1 : ℝ) - (t : ℝ)) •
            deriv (⇑γ.extend) ((t : ℝ) + (1 - (t : ℝ)) * r)
        rw [hmul]
        rw [deriv_comp_add_const]
        subst c
        congr 1
        ring_nf
      rw [hval, hderiv]
      rw [mul_smul_comm]
      change ((1 : ℝ) - (t : ℝ)) •
          (f (γ.extend ((t : ℝ) + (1 - (t : ℝ)) * r)) *
            deriv (⇑γ.extend) ((t : ℝ) + (1 - (t : ℝ)) * r)) =
        ((1 : ℝ) - (t : ℝ)) •
          complexCurveIntegrand f γ ((t : ℝ) + (1 - (t : ℝ)) * r)
      rw [complexCurveIntegrand_apply]
    · exact (intervalIntegral.integral_smul
        (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (r := ((1 : ℝ) - (t : ℝ)))
        (f := fun r : ℝ => g ((t : ℝ) + (1 - (t : ℝ)) * r)))
  rw [hleft, hright, complexCurveIntegral_eq_intervalIntegral_deriv]
  change (∫ x in (0 : ℝ)..(t : ℝ), g x) + (∫ x in (t : ℝ)..1, g x) =
    ∫ x in (0 : ℝ)..1, g x
  exact intervalIntegral.integral_add_adjacent_intervals hint_left hint_right

/-- The integral over a subpath is the corresponding interval integral over the original path. -/
lemma complexCurveIntegral_subpath_eq_intervalIntegral
    {a b : ℂ} {f : ℂ → ℂ} {γ : Path a b} (p q : I) :
    complexCurveIntegral f (γ.subpath p q) =
      ∫ x in (p : ℝ)..(q : ℝ), complexCurveIntegrand f γ x := by
  let g : ℝ → ℂ := complexCurveIntegrand f γ
  rw [complexCurveIntegral_eq_intervalIntegral_deriv]
  change (∫ r in (0 : ℝ)..1,
      f ((γ.subpath p q).extend r) * deriv (⇑(γ.subpath p q).extend) r) =
    ∫ x in (p : ℝ)..(q : ℝ), g x
  have hsubst :
        ((q : ℝ) - (p : ℝ)) •
          (∫ r in (0 : ℝ)..1, g ((p : ℝ) + ((q : ℝ) - (p : ℝ)) * r)) =
        ∫ x in (p : ℝ)..(q : ℝ), g x := by
    convert
      (intervalIntegral.smul_integral_comp_add_mul
        (f := g) (a := (0 : ℝ)) (b := (1 : ℝ))
        ((q : ℝ) - (p : ℝ)) (p : ℝ)) using 1
    · ring_nf
  rw [← hsubst]
  trans ∫ r in (0 : ℝ)..1,
      ((q : ℝ) - (p : ℝ)) •
        g ((p : ℝ) + ((q : ℝ) - (p : ℝ)) * r)
  · apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
    have Heq : (γ.subpath p q).extend =ᶠ[𝓝 r]
        fun x : ℝ => γ.extend ((p : ℝ) + ((q : ℝ) - (p : ℝ)) * x) := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
      have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
      have hρx01 : (p : ℝ) + ((q : ℝ) - (p : ℝ)) * x ∈ Icc (0 : ℝ) 1 := by
        constructor <;> nlinarith [p.2.1, p.2.2, q.2.1, q.2.2, hx01.1, hx01.2]
      rw [Path.extend_apply _ hx01, Path.extend_apply γ hρx01]
      simp [Path.subpath, Set.Icc.convexCombo]
      congr 1
      apply Subtype.ext
      ring
    have hval :
        (γ.subpath p q).extend r =
          γ.extend ((p : ℝ) + ((q : ℝ) - (p : ℝ)) * r) := Heq.self_of_nhds
    have hderiv :
        deriv (⇑(γ.subpath p q).extend) r =
          ((q : ℝ) - (p : ℝ)) •
            deriv (⇑γ.extend) ((p : ℝ) + ((q : ℝ) - (p : ℝ)) * r) := by
      rw [Heq.deriv_eq]
      let c : ℝ := (q : ℝ) - (p : ℝ)
      have hfun :
          (fun x : ℝ => γ.extend ((p : ℝ) + ((q : ℝ) - (p : ℝ)) * x)) =
            fun x : ℝ => (fun y : ℝ => γ.extend (y + (p : ℝ))) (c * x) := by
        funext x
        congr 1
        simp [c]
        ring
      rw [hfun]
      have hmul :=
        deriv_comp_mul_left c (fun y : ℝ => γ.extend (y + (p : ℝ))) r
      change deriv (fun x : ℝ => (fun y : ℝ => γ.extend (y + (p : ℝ))) (c * x)) r =
        ((q : ℝ) - (p : ℝ)) •
          deriv (⇑γ.extend) ((p : ℝ) + ((q : ℝ) - (p : ℝ)) * r)
      rw [hmul]
      rw [deriv_comp_add_const]
      subst c
      congr 1
      ring_nf
    rw [hval, hderiv]
    rw [mul_smul_comm]
    change ((q : ℝ) - (p : ℝ)) •
        (f (γ.extend ((p : ℝ) + ((q : ℝ) - (p : ℝ)) * r)) *
          deriv (⇑γ.extend) ((p : ℝ) + ((q : ℝ) - (p : ℝ)) * r)) =
      ((q : ℝ) - (p : ℝ)) •
        complexCurveIntegrand f γ ((p : ℝ) + ((q : ℝ) - (p : ℝ)) * r)
    rw [complexCurveIntegrand_apply]
  · exact (intervalIntegral.integral_smul
      (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
      (r := ((q : ℝ) - (p : ℝ)))
      (f := fun r : ℝ => g ((p : ℝ) + ((q : ℝ) - (p : ℝ)) * r)))

/-- Additivity of complex curve integrals over consecutive subpaths. -/
theorem complexCurveIntegral_subpath_split
    {a b : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ : Path a b}
    (hγU : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ U)
    (hfU : ContinuousOn f U)
    (hγC1 : γ.IsPiecewiseC1)
    (s t u : I) :
    complexCurveIntegral f (γ.subpath s t) +
      complexCurveIntegral f (γ.subpath t u) =
        complexCurveIntegral f (γ.subpath s u) := by
  let g : ℝ → ℂ := complexCurveIntegrand f γ
  have hint : IntervalIntegrable g volume (0 : ℝ) 1 := by
    simpa [g] using hγC1.intervalIntegrable_complexCurveIntegrand hγU hfU
  have hint_st : IntervalIntegrable g volume (s : ℝ) (t : ℝ) :=
    hint.mono_set (Set.uIcc_subset_uIcc
      (by simp only [zero_le_one, uIcc_of_le, Subtype.coe_prop] : (s : ℝ) ∈ [[(0 : ℝ), (1 : ℝ)]])
      (by simp only [zero_le_one, uIcc_of_le, Subtype.coe_prop] : (t : ℝ) ∈ [[(0 : ℝ), (1 : ℝ)]]))
  have hint_tu : IntervalIntegrable g volume (t : ℝ) (u : ℝ) :=
    hint.mono_set (Set.uIcc_subset_uIcc
      (by simp only [zero_le_one, uIcc_of_le, Subtype.coe_prop] : (t : ℝ) ∈ [[(0 : ℝ), (1 : ℝ)]])
      (by simp only [zero_le_one, uIcc_of_le, Subtype.coe_prop] : (u : ℝ) ∈ [[(0 : ℝ), (1 : ℝ)]]))
  rw [complexCurveIntegral_subpath_eq_intervalIntegral (f := f) (γ := γ) s t,
    complexCurveIntegral_subpath_eq_intervalIntegral (f := f) (γ := γ) t u,
    complexCurveIntegral_subpath_eq_intervalIntegral (f := f) (γ := γ) s u]
  change (∫ x in (s : ℝ)..(t : ℝ), g x) + (∫ x in (t : ℝ)..(u : ℝ), g x) =
    ∫ x in (s : ℝ)..(u : ℝ), g x
  exact intervalIntegral.integral_add_adjacent_intervals hint_st hint_tu

/--
The complex curve integral over a path is the sum of the integrals over the equal-grid subpaths.
A later version should remove the equal-grid restriction and work for arbitrary ordered
subdivisions.
-/
theorem complexCurveIntegral_sum_equalGrid_subpath
    {a b : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ : Path a b} {N : ℕ}
    (hγU : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ U)
    (hfU : ContinuousOn f U)
    (hN : 0 < N)
    (hγC1 : γ.IsPiecewiseC1) :
    (∑ i : Fin N,
      complexCurveIntegral f (γ.subpath (Path.equalGrid N i.castSucc) (Path.equalGrid N i.succ))) =
        complexCurveIntegral f γ := by
  let g : ℝ → ℂ := complexCurveIntegrand f γ
  let as : ℕ → ℝ := fun k => (k : ℝ) / (N : ℝ)
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hint : IntervalIntegrable g volume (0 : ℝ) 1 := by
    simpa [g] using hγC1.intervalIntegrable_complexCurveIntegrand hγU hfU
  have has_mem : ∀ k, k ≤ N → as k ∈ Icc (0 : ℝ) 1 := by
    intro k hk
    have hN_nonneg : (0 : ℝ) ≤ N := by positivity
    constructor
    · exact div_nonneg (by positivity) hN_nonneg
    · exact div_le_one_of_le₀ (by exact_mod_cast hk) hN_nonneg
  have hpiece_int :
      ∀ k < N, IntervalIntegrable g volume (as k) (as (k + 1)) := by
    intro k hk
    exact hint.mono_set (Set.uIcc_subset_uIcc
      (Set.Icc_subset_uIcc (has_mem k (Nat.le_of_lt hk)))
      (Set.Icc_subset_uIcc (has_mem (k + 1) (Nat.succ_le_iff.mpr hk))))
  have hsum :
      (∑ k ∈ Finset.range N, ∫ x in as k..as (k + 1), g x) =
        ∫ x in as 0..as N, g x :=
    intervalIntegral.sum_integral_adjacent_intervals hpiece_int
  have hfin_to_range :
      (∑ i : Fin N,
        complexCurveIntegral f
          (γ.subpath (Path.equalGrid N i.castSucc) (Path.equalGrid N i.succ))) =
        ∑ k ∈ Finset.range N, ∫ x in as k..as (k + 1), g x := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < N := Finset.mem_range.mp hk
    let i : Fin N := ⟨k, hklt⟩
    have hleft : ((Path.equalGrid N i.castSucc : I) : ℝ) = as k := by
      simp [as, i]
    have hright : ((Path.equalGrid N i.succ : I) : ℝ) = as (k + 1) := by
      simp [as, i, Nat.cast_add, Nat.cast_one]
    simp [hklt]
    exact (complexCurveIntegral_subpath_eq_intervalIntegral
        (f := f) (γ := γ) (Path.equalGrid N i.castSucc) (Path.equalGrid N i.succ)).trans
      (by rw [hleft, hright])
  calc
    (∑ i : Fin N,
        complexCurveIntegral f
          (γ.subpath (Path.equalGrid N i.castSucc) (Path.equalGrid N i.succ)))
        =
      ∑ k ∈ Finset.range N, ∫ x in as k..as (k + 1), g x := hfin_to_range
    _ = ∫ x in as 0..as N, g x := hsum
    _ = complexCurveIntegral f γ := by
      rw [complexCurveIntegral_eq_intervalIntegral_deriv]
      change (∫ x in as 0..as N, g x) =
        ∫ x in (0 : ℝ)..1, g x
      have has0 : as 0 = 0 := by simp [as]
      have hasN : as N = 1 := by
        simp [as, hN_ne]
      rw [has0, hasN]
