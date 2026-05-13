/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module

public import Complex.CauchyIntegralTheorem
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Meromorphic.NormalForm

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

/-- The function obtained from `f` by subtracting the finite sum of prescribed principal parts. -/
noncomputable def meromorphicRemainder
    (f : ℂ → ℂ) (poles : Finset ℂ) (principalPart : ℂ → ℂ → ℂ) : ℂ → ℂ :=
  fun z => f z - poles.sum (fun p => principalPart p z)

/-- The finite sum of the prescribed principal parts. -/
noncomputable def principalPartSum
    (poles : Finset ℂ) (principalPart : ℂ → ℂ → ℂ) : ℂ → ℂ :=
  fun z => poles.sum (fun p => principalPart p z)

lemma fdzForm_meromorphicRemainder
    (f : ℂ → ℂ) (poles : Finset ℂ) (principalPart : ℂ → ℂ → ℂ) :
    fdzForm (meromorphicRemainder f poles principalPart) =
      fdzForm f - fdzForm (principalPartSum poles principalPart) := by
  funext z
  ext
  simp [fdzForm, meromorphicRemainder, principalPartSum]

/--
If the integral of `f` minus its prescribed principal parts is zero, then the integral of `f`
is the integral of the principal-part sum.

This is just mathlib's linearity of `curveIntegral`, specialized through `complexCurveIntegral`.
-/
lemma complexCurveIntegral_eq_principalPartSum_of_remainder_integral_eq_zero
    {a b : ℂ} {f : ℂ → ℂ} {γ : Path a b}
    (poles : Finset ℂ) (principalPart : ℂ → ℂ → ℂ)
    (hf_int : CurveIntegrable (fdzForm f) γ)
    (hpp_int : CurveIntegrable (fdzForm (principalPartSum poles principalPart)) γ)
    (hrem_zero :
      complexCurveIntegral (meromorphicRemainder f poles principalPart) γ = 0) :
    complexCurveIntegral f γ =
      complexCurveIntegral (principalPartSum poles principalPart) γ := by
  have hsub :
      complexCurveIntegral (meromorphicRemainder f poles principalPart) γ =
        complexCurveIntegral f γ -
          complexCurveIntegral (principalPartSum poles principalPart) γ := by
    rw [complexCurveIntegral_def, fdzForm_meromorphicRemainder]
    exact curveIntegral_fun_sub hf_int hpp_int
  rw [hsub] at hrem_zero
  exact sub_eq_zero.mp hrem_zero

/--
Holomorphicity of the remainder, plus null-homotopy of the loop, gives the first reduction in the
residue theorem: only the principal parts contribute to the curve integral.
-/
lemma complexCurveIntegral_eq_principalPartSum_of_holomorphic_remainder
    {a : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ : Path a a}
    (poles : Finset ℂ) (principalPart : ℂ → ℂ → ℂ)
    (hU_open : IsOpen U)
    (hγC1 : γ.IsPiecewiseC1)
    (H : Path.Homotopy γ (Path.refl a))
    (hHU : ∀ s t : I, H (s, t) ∈ U)
    (hrem_diff : DifferentiableOn ℂ (meromorphicRemainder f poles principalPart) U)
    (hf_int : CurveIntegrable (fdzForm f) γ)
    (hpp_int : CurveIntegrable (fdzForm (principalPartSum poles principalPart)) γ) :
    complexCurveIntegral f γ =
      complexCurveIntegral (principalPartSum poles principalPart) γ := by
  refine complexCurveIntegral_eq_principalPartSum_of_remainder_integral_eq_zero
    poles principalPart hf_int hpp_int ?_
  exact complexCurveIntegral_eq_zero_of_nullhomotopic_piecewiseC1
    hU_open hrem_diff hγC1 H hHU

/--
The higher-order residue kernels have primitives off their pole, hence integrate to zero around
piecewise `C¹` loops avoiding the pole.
-/
lemma complexCurveIntegral_sub_zpow_neg_eq_zero_of_two_le
    {a : ℂ} {γ : Path a a} (z₀ : ℂ) (n : ℕ)
    (hn : 2 ≤ n)
    (hγC1 : γ.IsPiecewiseC1)
    (hγ_avoids : ∀ t : I, γ t ≠ z₀) :
    complexCurveIntegral (fun z => (z - z₀) ^ (-(n : ℤ))) γ = 0 := by
  let U : Set ℂ := {z | z ≠ z₀}
  let F : ℂ → ℂ := fun z => (z - z₀) ^ (1 - (n : ℤ)) / (1 - (n : ℂ))
  have hn_ne_one_nat : n ≠ 1 := by omega
  have hn_den : (1 - (n : ℂ)) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (Ne.symm hn_ne_one_nat)
  have hγU : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ U := by
    intro t ht
    simpa [U, Path.extend_apply γ ht] using hγ_avoids ⟨t, ht⟩
  have hf_cont : ContinuousOn (fun z : ℂ => (z - z₀) ^ (-(n : ℤ))) U := by
    exact ((continuousOn_id.sub continuousOn_const).zpow₀ _ fun z hz =>
      Or.inl (sub_ne_zero.mpr hz))
  have hF : ∀ z ∈ U,
      HasFDerivAt F
        ((fdzForm (fun z => (z - z₀) ^ (-(n : ℤ))) z).restrictScalars ℝ)
        z := by
    intro z hz
    have hz_sub : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have hderiv_zpow :
        HasDerivAt F ((z - z₀) ^ (-(n : ℤ))) z := by
      have hpow :
          HasDerivAt
            (fun z : ℂ => (z - z₀) ^ (1 - (n : ℤ)))
            (((1 - (n : ℤ) : ℤ) : ℂ) * (z - z₀) ^ ((1 - (n : ℤ)) - 1))
            z := by
        simpa using
          (hasDerivAt_zpow (1 - (n : ℤ)) (z - z₀) (Or.inl hz_sub)).comp z
            ((hasDerivAt_id z).sub_const z₀)
      have hdiv := hpow.div_const (1 - (n : ℂ))
      convert hdiv using 1
      have h_exp : (1 - (n : ℤ)) - 1 = -(n : ℤ) := by ring
      have h_cast : (((1 - (n : ℤ) : ℤ) : ℂ)) = 1 - (n : ℂ) := by
        norm_num
      rw [h_exp, h_cast]
      field_simp [hn_den]
    convert hderiv_zpow.hasFDerivAt.restrictScalars ℝ using 1
    · ext v
      simp [fdzForm, mul_comm]
    · exact IsScalarTower.complexToReal
    · exact IsScalarTower.complexToReal
  have hint :
      IntervalIntegrable
        (complexCurveIntegrand (fun z => (z - z₀) ^ (-(n : ℤ))) γ)
        volume
        0 1 :=
    hγC1.intervalIntegrable_complexCurveIntegrand hγU hf_cont
  have h_eval :=
    complexCurveIntegral_eq_sub_of_hasPrimitiveOn_piecewiseC1
      hγC1 hγU hF hint
  simpa using h_eval

/--
Mathlib's meromorphic normal-form API packages the removable-singularity step as:
`MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd`.

So, for a meromorphic function in normal form, proving that its divisor is nonnegative is enough to
show that it is holomorphic.
-/
lemma analyticOnNhd_of_meromorphicNFOn_nonneg_divisor
    {U : Set ℂ} {g : ℂ → ℂ}
    (hgNF : MeromorphicNFOn g U)
    (hg_divisor_nonneg : 0 ≤ MeromorphicOn.divisor g U) :
    AnalyticOnNhd ℂ g U :=
  (hgNF.divisor_nonneg_iff_analyticOnNhd).mp hg_divisor_nonneg

/--
After subtracting principal parts at every pole, the resulting remainder is holomorphic.

This is the first substantial proof step for the residue theorem.  The principal parts should be
chosen so that the remainder is meromorphic in normal form and has nonnegative divisor; mathlib then
turns that directly into analyticity.
-/
lemma analyticOnNhd_meromorphicRemainder_of_nonneg_divisor
    {U : Set ℂ} {f : ℂ → ℂ}
    (poles : Finset ℂ) (principalPart : ℂ → ℂ → ℂ)
    (hgNF : MeromorphicNFOn (meromorphicRemainder f poles principalPart) U)
    (hg_divisor_nonneg :
      0 ≤ MeromorphicOn.divisor (meromorphicRemainder f poles principalPart) U) :
    AnalyticOnNhd ℂ (meromorphicRemainder f poles principalPart) U :=
  analyticOnNhd_of_meromorphicNFOn_nonneg_divisor hgNF hg_divisor_nonneg

/-- Differentiability consequence of `analyticOnNhd_meromorphicRemainder_of_nonneg_divisor`. -/
lemma differentiableOn_meromorphicRemainder_of_nonneg_divisor
    {U : Set ℂ} {f : ℂ → ℂ}
    (poles : Finset ℂ) (principalPart : ℂ → ℂ → ℂ)
    (hgNF : MeromorphicNFOn (meromorphicRemainder f poles principalPart) U)
    (hg_divisor_nonneg :
      0 ≤ MeromorphicOn.divisor (meromorphicRemainder f poles principalPart) U) :
    DifferentiableOn ℂ (meromorphicRemainder f poles principalPart) U :=
  (analyticOnNhd_meromorphicRemainder_of_nonneg_divisor
    poles principalPart hgNF hg_divisor_nonneg).differentiableOn

/--
A meromorphic finite-pole version of the residue theorem statement for a null-homotopic loop.

Mathlib already provides `MeromorphicOn` and `meromorphicOrderAt`, which are the right way to say
that `f` is holomorphic away from isolated poles.  The hypothesis `hpoles_exhaust` says that the
finite set `poles` contains every negative-order point of `f` in `U`.

The hypotheses `H` and `hHU` say that `γ` is null-homotopic in `U`.  This is the topological
condition needed by the Cauchy theorem: a simpler sufficient assumption would be that `U` is simply
connected, but the local API currently consumes the actual homotopy.

The residue coefficient is left as the explicit parameter `residue` for now.  This avoids
restricting to simple poles: `meromorphicTrailingCoeffAt` gives the residue coefficient only when
the pole has order `-1`, while the residue theorem should also cover higher-order poles.  A later
step should introduce or connect to a Laurent `(-1)`-coefficient API for this parameter.
-/
theorem complexCurveIntegral_eq_sum_meromorphic_residue_kernel_integrals
    {a : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ : Path a a}
    (poles : Finset ℂ) (residue : ℂ → ℂ)
    (hU_open : IsOpen U)
    (hf_meromorphic : MeromorphicOn f U)
    (hγC1 : γ.IsPiecewiseC1)
    (hγU : γ.MapsInto U)
    (hγ_avoids_poles :
      ∀ t : I, γ t ∉ (poles : Set ℂ))
    (H : Path.Homotopy γ (Path.refl a))
    (hHU : ∀ s t : I, H (s, t) ∈ U)
    (hpoles_mem : ∀ p ∈ poles, p ∈ U)
    (hpoles_exhaust :
      ∀ z ∈ U, meromorphicOrderAt f z < ((0 : ℤ) : WithTop ℤ) → z ∈ (poles : Set ℂ)) :
    complexCurveIntegral f γ =
      poles.sum (fun p =>
        residue p * complexCurveIntegral (fun z => (z - p)⁻¹) γ) := by
  sorry

/-
plans: (1) existence of primitive on simply connected;
(2) maybe: existence of primitive if unique (i.e., independent of paths).


-/
