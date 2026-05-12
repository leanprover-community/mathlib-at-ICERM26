/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module


public import CurveIntegral.Primitive

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

theorem exists_isPiecewiseLinear_mapsInto_of_isOpen_isConnected
    {U : Set ℂ} (hU_open : IsOpen U) (hU_connected : IsConnected U)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    ∃ γ : Path x y, γ.IsPiecewiseLinear ∧ γ.MapsInto U := by
  have hU_path : IsPathConnected U :=
    (hU_open.isConnected_iff_isPathConnected).mp hU_connected
  rcases hU_path.joinedIn x hx y hy with ⟨γ, hγU⟩
  let K : Set ℂ := Set.range γ
  have hK_compact : IsCompact K := isCompact_range γ.continuous
  have hK_subset : K ⊆ U := by
    rintro z ⟨t, rfl⟩
    exact hγU t
  rcases hK_compact.exists_thickening_subset_open hU_open hK_subset with
    ⟨ε, hεpos, hεU⟩
  rcases Path.exists_isPiecewiseLinear_forall_dist_lt γ ε hεpos with
    ⟨γ', hγ'PL, hγ'close⟩
  refine ⟨γ', hγ'PL, ?_⟩
  intro t
  apply hεU
  rw [Metric.mem_thickening_iff]
  exact ⟨γ t, ⟨t, rfl⟩, by simpa [dist_comm] using hγ'close t⟩

theorem eq_complexCurveIntegral_of_mapsInto_ball_piecewiseC1
    {a b c : ℂ} {r : ℝ} {f : ℂ → ℂ} {γ γ' : Path a b}
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (hγU : γ.MapsInto (Metric.ball c r))
    (hγ'U : γ'.MapsInto (Metric.ball c r))
    (hγC1 : γ.IsPiecewiseC1)
    (hγ'C1 : γ'.IsPiecewiseC1) :
    complexCurveIntegral f γ' = complexCurveIntegral f γ := by
  have hγU_extend : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ Metric.ball c r := by
    intro t ht
    simpa [Path.extend_apply γ ht] using hγU ⟨t, ht⟩
  have hγ'U_extend : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ'.extend t ∈ Metric.ball c r := by
    intro t ht
    simpa [Path.extend_apply γ' ht] using hγ'U ⟨t, ht⟩

  rcases hf.isExactOn_ball with ⟨F, hF⟩
  have hfU : ContinuousOn f (Metric.ball c r) := hf.continuousOn
  have hF_real : ∀ z ∈ Metric.ball c r,
      HasFDerivAt F ((fdzForm f z).restrictScalars ℝ) z := by
    intro z hz
    convert (hF z hz).hasFDerivAt.restrictScalars ℝ using 1
    · ext v
      simp [fdzForm, mul_comm]
    · exact IsScalarTower.complexToReal
    · exact IsScalarTower.complexToReal
  have hγ_int :
      IntervalIntegrable (complexCurveIntegrand f γ) volume 0 1 :=
    hγC1.intervalIntegrable_complexCurveIntegrand hγU_extend hfU
  have hγ'_int :
      IntervalIntegrable (complexCurveIntegrand f γ') volume 0 1 :=
    hγ'C1.intervalIntegrable_complexCurveIntegrand hγ'U_extend hfU
  have hγ_eq :
      complexCurveIntegral f γ = F b - F a :=
    complexCurveIntegral_eq_sub_of_hasPrimitiveOn_piecewiseC1
      hγC1 hγU_extend hF_real hγ_int
  have hγ'_eq :
      complexCurveIntegral f γ' = F b - F a :=
    complexCurveIntegral_eq_sub_of_hasPrimitiveOn_piecewiseC1
      hγ'C1 hγ'U_extend hF_real hγ'_int
  exact hγ'_eq.trans hγ_eq.symm

theorem complexCurveIntegral_trans_piecewiseC1
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

theorem complexCurveIntegral_subpath_split_two
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

theorem complexCurveIntegral_subpath_zero_one_split
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
        ring
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

theorem complexCurveIntegral_subpath_eq_intervalIntegral
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
      ring
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

@[simp]
theorem complexCurveIntegral_segment_same {a : ℂ} (f : ℂ → ℂ) :
    complexCurveIntegral f (Path.segment a a) = 0 := by
  simp [complexCurveIntegral, Path.segment_same, curveIntegral_refl]

/-- Local ladder lemma for a path and a uniformly close perturbation.

This is the finite-subdivision argument described below:
choose a partition fine enough that adjacent points of `γ` are close compared with the
thickening radius, form the small quadrilaterals with vertical sides between `γ` and `γ'`,
apply `eq_complexCurveIntegral_of_mapsInto_ball_piecewiseC1` inside the ball centered at the
left endpoint of each cell, and telescope the segment contributions. -/
theorem complexCurveIntegral_eq_of_uniformClose_piecewiseC1_of_thickening
    {a b : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ γ' : Path a b}
    (hf : DifferentiableOn ℂ f U)
    (hγC1 : γ.IsPiecewiseC1)
    (hγ'C1 : γ'.IsPiecewiseC1)
    {ε : ℝ} (hεpos : 0 < ε)
    (hεU : Metric.thickening ε (Set.range γ) ⊆ U)
    (hclose : γ.UniformClose γ' (ε / 4)) :
    complexCurveIntegral f γ' = complexCurveIntegral f γ := by
  have hγ_uc : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  rcases Metric.uniformContinuous_iff.mp hγ_uc (ε / 4) (by positivity) with ⟨δ, hδ, huc⟩
  rcases exists_nat_one_div_lt hδ with ⟨n, hn⟩
  let N : ℕ := n + 1
  have hN : 0 < N := Nat.succ_pos n
  let grid : Fin (N + 1) → I := Path.equalGrid N
  have hmesh : (1 : ℝ) / N < δ := by
    simpa [N, Nat.cast_add, Nat.cast_one] using hn

  have hcell_close : ∀ i : Fin N,
      dist (γ (grid i.castSucc)) (γ (grid i.succ)) < ε / 4 := by
    intro i
    apply huc
    have hdist_eq :
        dist (grid i.castSucc) (grid i.succ) = (1 : ℝ) / N := by
      rw [dist_comm, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
      · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        simp [grid, Nat.cast_add, Nat.cast_one, sub_eq_add_neg, div_eq_mul_inv]
        field_simp [ne_of_gt hNpos]
        ring
      · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        rw [sub_nonneg]
        dsimp [grid, Path.equalGrid]
        change ((i.val : ℝ) / (N : ℝ)) ≤ ((i.val + 1 : ℕ) : ℝ) / (N : ℝ)
        gcongr
        exact Nat.le_succ _
    simpa [hdist_eq] using hmesh

  have hgrid_le : ∀ i : Fin N, grid i.castSucc ≤ grid i.succ := by
    intro i
    change (grid i.castSucc : ℝ) ≤ (grid i.succ : ℝ)
    dsimp [grid, Path.equalGrid]
    gcongr
    exact Nat.le_succ _

  have hgrid_dist_lt : ∀ i : Fin N, ∀ u : I,
      u ∈ Set.Icc (grid i.castSucc) (grid i.succ) →
        dist (grid i.castSucc) u < δ := by
    intro i u hu
    have hdist_le : dist (grid i.castSucc) u ≤ (1 : ℝ) / N := by
      rw [dist_comm, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
      · have hstep :
            (grid i.succ : ℝ) - (grid i.castSucc : ℝ) = (1 : ℝ) / N := by
          dsimp [grid, Path.equalGrid]
          change ((i.val + 1 : ℕ) : ℝ) / (N : ℝ) - (i.val : ℝ) / (N : ℝ) =
            (1 : ℝ) / N
          have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
          field_simp [ne_of_gt hNpos]
          norm_num [Nat.cast_add, Nat.cast_one]
        calc
          (u : ℝ) - (grid i.castSucc : ℝ)
              ≤ (grid i.succ : ℝ) - (grid i.castSucc : ℝ) := by
                have hu2 : (u : ℝ) ≤ (grid i.succ : ℝ) := hu.2
                exact sub_le_sub_right hu2 _
          _ = (1 : ℝ) / N := hstep
      · exact sub_nonneg.mpr hu.1
    exact lt_of_le_of_lt hdist_le hmesh

  have hγ_mem_ball : ∀ i : Fin N, ∀ u : I,
      u ∈ Set.Icc (grid i.castSucc) (grid i.succ) →
        γ u ∈ Metric.ball (γ (grid i.castSucc)) ε := by
    intro i u hu
    rw [Metric.mem_ball]
    exact lt_trans (huc (by simpa [dist_comm] using hgrid_dist_lt i u hu)) (by linarith)

  have hγ'_mem_ball : ∀ i : Fin N, ∀ u : I,
      u ∈ Set.Icc (grid i.castSucc) (grid i.succ) →
        γ' u ∈ Metric.ball (γ (grid i.castSucc)) ε := by
    intro i u hu
    rw [Metric.mem_ball]
    calc
      dist (γ' u) (γ (grid i.castSucc))
          ≤ dist (γ' u) (γ u) + dist (γ u) (γ (grid i.castSucc)) := dist_triangle _ _ _
      _ < ε / 4 + ε / 4 := by
        exact add_lt_add (by simpa [dist_comm] using hclose u)
          (by simpa [dist_comm] using huc (hgrid_dist_lt i u hu))
      _ < ε := by linarith

  have hsegment_mem_ball : ∀ i : Fin N, ∀ u : I, ∀ p q : ℂ,
      p ∈ Metric.ball (γ (grid i.castSucc)) ε →
      q ∈ Metric.ball (γ (grid i.castSucc)) ε →
        Path.segment p q u ∈ Metric.ball (γ (grid i.castSucc)) ε := by
    intro i u p q hp hq
    exact (convex_ball (γ (grid i.castSucc)) ε).segment_subset hp hq
      (by
        rw [← Path.range_segment]
        exact ⟨u, rfl⟩)

  -- The local quadrilateral identity in the ball centered at the left endpoint of the cell.
  have hcell :
      ∀ i : Fin N,
        let c := γ (grid i.castSucc)
        let top : Path c (γ' (grid i.succ)) :=
          (γ.subpath (grid i.castSucc) (grid i.succ)).trans
            (Path.segment (γ (grid i.succ)) (γ' (grid i.succ)))
        let bottom : Path c (γ' (grid i.succ)) :=
          (Path.segment (γ (grid i.castSucc)) (γ' (grid i.castSucc))).trans
            (γ'.subpath (grid i.castSucc) (grid i.succ))
        complexCurveIntegral f bottom = complexCurveIntegral f top := by
    intro i
    dsimp
    refine eq_complexCurveIntegral_of_mapsInto_ball_piecewiseC1
      (c := γ (grid i.castSucc)) (r := ε) ?_ ?_ ?_ ?_ ?_
    · exact hf.mono (by
        intro z hz
        apply hεU
        rw [Metric.mem_thickening_iff]
        exact ⟨γ (grid i.castSucc), ⟨grid i.castSucc, rfl⟩, hz⟩)
    · -- the top side followed by the right vertical side lies in this ball
      intro t
      rw [Path.trans_apply]
      split_ifs with ht
      · apply hγ_mem_ball
        constructor
        · exact Icc.le_convexCombo (hgrid_le i) _
        · exact Icc.convexCombo_le (hgrid_le i) _
      · apply hsegment_mem_ball
        · exact hγ_mem_ball i (grid i.succ) ⟨hgrid_le i, le_rfl⟩
        · exact hγ'_mem_ball i (grid i.succ) ⟨hgrid_le i, le_rfl⟩
    · -- the left vertical side followed by the bottom side lies in this ball
      intro t
      rw [Path.trans_apply]
      split_ifs with ht
      · apply hsegment_mem_ball
        · exact Metric.mem_ball_self hεpos
        · exact hγ'_mem_ball i (grid i.castSucc) ⟨le_rfl, hgrid_le i⟩
      · apply hγ'_mem_ball
        constructor
        · exact Icc.le_convexCombo (hgrid_le i) _
        · exact Icc.convexCombo_le (hgrid_le i) _
    · -- concatenation of the `γ`-subpath with a segment is piecewise-`C¹`
      exact (hγC1.subpath (grid i.castSucc) (grid i.succ)).trans
        (Path.segment_isPiecewiseC1 (γ (grid i.succ)) (γ' (grid i.succ)))
    · -- concatenation of a segment with the `γ'`-subpath is piecewise-`C¹`
      exact (Path.segment_isPiecewiseC1 (γ (grid i.castSucc)) (γ' (grid i.castSucc))).trans
        (hγ'C1.subpath (grid i.castSucc) (grid i.succ))

  -- Summing `hcell i` over all cells and using additivity of curve integrals over subpaths
  -- gives cancellation of the vertical sides. The endpoint verticals are constant because
  -- `γ` and `γ'` have the same endpoints.
  let A : Fin N → ℂ := fun i =>
    complexCurveIntegral f (γ.subpath (grid i.castSucc) (grid i.succ))
  let B : Fin N → ℂ := fun i =>
    complexCurveIntegral f (γ'.subpath (grid i.castSucc) (grid i.succ))
  let V : Fin (N + 1) → ℂ := fun j =>
    complexCurveIntegral f (Path.segment (γ (grid j)) (γ' (grid j)))

  have hcell_add : ∀ i : Fin N, V i.castSucc + B i = A i + V i.succ := by
    intro i
    have hc := hcell i
    dsimp [A, B, V] at hc ⊢
    let Ucell : Set ℂ := Metric.ball (γ (grid i.castSucc)) ε
    have hfUcell : ContinuousOn f Ucell := hf.continuousOn.mono (by
      intro z hz
      apply hεU
      rw [Metric.mem_thickening_iff]
      exact ⟨γ (grid i.castSucc), ⟨grid i.castSucc, rfl⟩, hz⟩)
    have hsegL_U : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
        (Path.segment (γ (grid i.castSucc)) (γ' (grid i.castSucc))).extend r ∈ Ucell := by
      intro r hr
      rw [Path.extend_apply _ hr]
      exact hsegment_mem_ball i ⟨r, hr⟩ (γ (grid i.castSucc)) (γ' (grid i.castSucc))
        (Metric.mem_ball_self hεpos)
        (hγ'_mem_ball i (grid i.castSucc) ⟨le_rfl, hgrid_le i⟩)
    have hsegR_U : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
        (Path.segment (γ (grid i.succ)) (γ' (grid i.succ))).extend r ∈ Ucell := by
      intro r hr
      rw [Path.extend_apply _ hr]
      exact hsegment_mem_ball i ⟨r, hr⟩ (γ (grid i.succ)) (γ' (grid i.succ))
        (hγ_mem_ball i (grid i.succ) ⟨hgrid_le i, le_rfl⟩)
        (hγ'_mem_ball i (grid i.succ) ⟨hgrid_le i, le_rfl⟩)
    have hγsub_U : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
        (γ.subpath (grid i.castSucc) (grid i.succ)).extend r ∈ Ucell := by
      intro r hr
      rw [Path.extend_apply _ hr]
      apply hγ_mem_ball
      constructor
      · exact Icc.le_convexCombo (hgrid_le i) _
      · exact Icc.convexCombo_le (hgrid_le i) _
    have hγ'sub_U : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
        (γ'.subpath (grid i.castSucc) (grid i.succ)).extend r ∈ Ucell := by
      intro r hr
      rw [Path.extend_apply _ hr]
      apply hγ'_mem_ball
      constructor
      · exact Icc.le_convexCombo (hgrid_le i) _
      · exact Icc.convexCombo_le (hgrid_le i) _
    rw [complexCurveIntegral_trans_piecewiseC1
          hsegL_U hγ'sub_U hfUcell
          (Path.segment_isPiecewiseC1 (γ (grid i.castSucc)) (γ' (grid i.castSucc)))
          (hγ'C1.subpath (grid i.castSucc) (grid i.succ)),
        complexCurveIntegral_trans_piecewiseC1
          hγsub_U hsegR_U hfUcell
          (hγC1.subpath (grid i.castSucc) (grid i.succ))
          (Path.segment_isPiecewiseC1 (γ (grid i.succ)) (γ' (grid i.succ)))] at hc
    exact hc

  have hsum_cell :
      (∑ i : Fin N, V i.castSucc) + ∑ i : Fin N, B i =
        (∑ i : Fin N, A i) + ∑ i : Fin N, V i.succ := by
    calc
      (∑ i : Fin N, V i.castSucc) + ∑ i : Fin N, B i
          = ∑ i : Fin N, (V i.castSucc + B i) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ i : Fin N, (A i + V i.succ) := by
              exact Finset.sum_congr rfl (fun i _ => hcell_add i)
      _ = (∑ i : Fin N, A i) + ∑ i : Fin N, V i.succ := by
              rw [Finset.sum_add_distrib]

  have hgrid0 : grid 0 = 0 := by
    ext
    simp [grid]
  have hgridN : grid (Fin.last N) = 1 := by
    ext
    change (N : ℝ) / (N : ℝ) = 1
    exact div_self (by exact_mod_cast hN.ne')
  have hV0 : V 0 = 0 := by
    have hγ0 : γ (grid 0) = a := by simp [hgrid0]
    have hγ'0 : γ' (grid 0) = a := by simp [hgrid0]
    dsimp [V]
    rw [hγ0, hγ'0, Path.segment_same]
    simp [complexCurveIntegral, curveIntegral_refl]
  have hVlast : V (Fin.last N) = 0 := by
    have hγ1 : γ (grid (Fin.last N)) = b := by simp [hgridN]
    have hγ'1 : γ' (grid (Fin.last N)) = b := by simp [hgridN]
    dsimp [V]
    rw [hγ1, hγ'1, Path.segment_same]
    simp [complexCurveIntegral, curveIntegral_refl]

  have hVsum : (∑ i : Fin N, V i.castSucc) = ∑ i : Fin N, V i.succ := by
    have hcast : (∑ i : Fin N, V i.castSucc) = ∑ j : Fin (N + 1), V j := by
      have h := Fin.sum_univ_castSucc V
      rw [hVlast, add_zero] at h
      exact h.symm
    have hsucc : (∑ i : Fin N, V i.succ) = ∑ j : Fin (N + 1), V j := by
      have h := Fin.sum_univ_succ V
      rw [hV0, zero_add] at h
      exact h.symm
    exact hcast.trans hsucc.symm

  have hsum_BA : (∑ i : Fin N, B i) = ∑ i : Fin N, A i := by
    have h := hsum_cell
    rw [hVsum] at h
    have h' :
        (∑ i : Fin N, V i.succ) + (∑ i : Fin N, B i) =
          (∑ i : Fin N, V i.succ) + (∑ i : Fin N, A i) := by
      simpa [add_comm, add_left_comm, add_assoc] using h
    exact add_left_cancel h'

  have hγU_extend : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → γ.extend r ∈ U := by
    intro r hr
    apply hεU
    rw [Metric.mem_thickening_iff]
    exact ⟨γ ⟨r, hr⟩, ⟨⟨r, hr⟩, rfl⟩, by
      rw [Path.extend_apply γ hr]
      simpa using (Metric.mem_ball_self hεpos : γ ⟨r, hr⟩ ∈ Metric.ball (γ ⟨r, hr⟩) ε)⟩
  have hγ'U_extend : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → γ'.extend r ∈ U := by
    intro r hr
    apply hεU
    rw [Metric.mem_thickening_iff]
    refine ⟨γ ⟨r, hr⟩, ⟨⟨r, hr⟩, rfl⟩, ?_⟩
    rw [Path.extend_apply γ' hr]
    exact lt_trans (by simpa [dist_comm] using hclose ⟨r, hr⟩) (by linarith)

  have hA_sum : (∑ i : Fin N, A i) = complexCurveIntegral f γ := by
    simpa [A, grid] using
      complexCurveIntegral_sum_equalGrid_subpath
        (U := U) (f := f) (γ := γ) hγU_extend hf.continuousOn hN hγC1
  have hB_sum : (∑ i : Fin N, B i) = complexCurveIntegral f γ' := by
    simpa [B, grid] using
      complexCurveIntegral_sum_equalGrid_subpath
        (U := U) (f := f) (γ := γ') hγ'U_extend hf.continuousOn hN hγ'C1

  calc
    complexCurveIntegral f γ' = ∑ i : Fin N, B i := hB_sum.symm
    _ = ∑ i : Fin N, A i := hsum_BA
    _ = complexCurveIntegral f γ := hA_sum

theorem exists_eps_eq_complexCurveIntegral_of_uniformClose_piecewiseC1'
    {a b : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ : Path a b}
    (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (hγU : γ.MapsInto U)
    (hγC1 : γ.IsPiecewiseC1) :
    ∃ ε > 0, ∀ {γ' : Path a b},
      γ'.IsPiecewiseC1 →
      γ.UniformClose γ' ε →
        γ'.MapsInto U ∧
        complexCurveIntegral f γ' = complexCurveIntegral f γ := by
  let K : Set ℂ := Set.range γ
  have hK_compact : IsCompact K := isCompact_range γ.continuous
  have hK_subset : K ⊆ U := by
    rintro z ⟨t, rfl⟩
    exact hγU t
  rcases hK_compact.exists_thickening_subset_open hU_open hK_subset with
    ⟨δ, hδpos, hδU⟩
  let ε : ℝ := δ / 4
  have hεpos : 0 < ε := by positivity
  refine ⟨ε, hεpos, ?_⟩
  intro γ' hγ'C1 hclose
  have hγ'U : γ'.MapsInto U := by
    intro t
    apply hδU
    rw [Metric.mem_thickening_iff]
    refine ⟨γ t, ⟨t, rfl⟩, ?_⟩
    exact lt_of_lt_of_le (by simpa [ε, dist_comm] using hclose t) (by linarith)
  refine ⟨hγ'U, ?_⟩
  exact complexCurveIntegral_eq_of_uniformClose_piecewiseC1_of_thickening
    hf hγC1 hγ'C1 hδpos hδU (by
      intro t
      simpa [ε] using hclose t)
