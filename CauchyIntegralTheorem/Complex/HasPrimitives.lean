module

public import ComplexCurveIntegral.Primitive
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

namespace Complex

/--
On a simply connected open set, every holomorphic function has a primitive.

Mathlib's primitive predicate is `Complex.IsExactOn f U`, i.e.
`∃ F, ∀ z ∈ U, HasDerivAt F (f z) z`.
-/
theorem AnalyticOnNhd.isExactOn_of_isSimplyConnected
    {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hU_open : IsOpen U)
    (hU_sc : IsSimplyConnected U) :
    IsExactOn f U := by
  sorry

/--
Unfolded primitive form of `AnalyticOnNhd.isExactOn_of_isSimplyConnected`.
-/
lemma exists_primitive_of_analyticOnNhd_isSimplyConnected
    {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hU_open : IsOpen U)
    (hU_sc : IsSimplyConnected U) :
    ∃ F : ℂ → ℂ, ∀ z ∈ U, HasDerivAt F (f z) z :=
  AnalyticOnNhd.isExactOn_of_isSimplyConnected hf hU_open hU_sc

/--
Same statement with the open-set differentiability formulation of holomorphicity.
-/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected
    {U : Set ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U)
    (hU_open : IsOpen U)
    (hU_sc : IsSimplyConnected U) :
    IsExactOn f U :=
  AnalyticOnNhd.isExactOn_of_isSimplyConnected
    ((analyticOnNhd_iff_differentiableOn hU_open).mpr hf) hU_open hU_sc

end Complex

/--
On a ball, a holomorphic function has a path-integral primitive.

The primitive is normalized to vanish at `z₀`, and its value at `z` is the integral of `f dz`
along any piecewise `C¹` path from `z₀` to `z` staying in the ball.  In particular, the integral is
independent of the chosen path.
-/
lemma exists_analyticOnNhd_pathIntegralPrimitiveOn_ball
    {c z₀ : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (_hz₀ : z₀ ∈ Metric.ball c r) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (Metric.ball c r) ∧
      (∀ z ∈ Metric.ball c r, HasDerivAt F (f z) z) ∧
      F z₀ = 0 ∧
      ∀ {z : ℂ} (_hz : z ∈ Metric.ball c r) (γ : Path z₀ z),
        γ.IsPiecewiseC1 →
        γ.MapsInto (Metric.ball c r) →
          F z = complexCurveIntegral f γ := by
  rcases hf.isExactOn_ball.with_val_at z₀ (0 : ℂ) with ⟨F, hFz₀, hF⟩
  have hF_diff : DifferentiableOn ℂ F (Metric.ball c r) := by
    intro z hz
    exact (hF z hz).differentiableAt.differentiableWithinAt
  have hF_analytic : AnalyticOnNhd ℂ F (Metric.ball c r) :=
    (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).mpr hF_diff
  refine ⟨F, hF_analytic, hF, hFz₀, ?_⟩
  intro z hz γ hγC1 hγU
  have hγU_extend : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ.extend t ∈ Metric.ball c r := by
    intro t ht
    simpa [Path.extend_apply γ ht] using hγU ⟨t, ht⟩
  have hF_real : ∀ z ∈ Metric.ball c r,
      HasFDerivAt F ((fdzForm f z).restrictScalars ℝ) z := by
    intro z hz
    convert (hF z hz).hasFDerivAt.restrictScalars ℝ using 1
    · ext v
      simp [fdzForm, mul_comm]
    · exact IsScalarTower.complexToReal
    · exact IsScalarTower.complexToReal
  have hint : IntervalIntegrable (complexCurveIntegrand f γ) volume 0 1 :=
    hγC1.intervalIntegrable_complexCurveIntegrand hγU_extend hf.continuousOn
  have hγ_eq : complexCurveIntegral f γ = F z - F z₀ :=
    complexCurveIntegral_eq_sub_of_hasPrimitiveOn_piecewiseC1
      hγC1 hγU_extend hF_real hint
  rw [hγ_eq, hFz₀, sub_zero]

/--
The function obtained by choosing a path from `z₀` to each point of a ball and integrating `f dz`
along that path.  It is only meaningful on the ball; outside the ball it is set to `0`.
-/
noncomputable def pathIntegralFromFamilyOnBall
    (c z₀ : ℂ) (r : ℝ) (f : ℂ → ℂ)
    (γ : (z : Metric.ball c r) → Path z₀ z) : ℂ → ℂ := by
  classical
  exact fun z : ℂ =>
    if hz : z ∈ Metric.ball c r then
      complexCurveIntegral f (γ ⟨z, hz⟩)
    else
      0

/--
If one chooses, for each point `z` in a ball, a piecewise `C¹` path from `z₀` to `z` staying in
the ball, then the function given by integrating `f dz` along the chosen path is holomorphic.
-/
lemma analyticOnNhd_pathIntegral_of_pathFamilyOn_ball
    {c z₀ : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (hz₀ : z₀ ∈ Metric.ball c r)
    (γ : (z : Metric.ball c r) → Path z₀ z)
    (hγC1 : ∀ z : Metric.ball c r, (γ z).IsPiecewiseC1)
    (hγU : ∀ z : Metric.ball c r, (γ z).MapsInto (Metric.ball c r)) :
    AnalyticOnNhd ℂ (pathIntegralFromFamilyOnBall c z₀ r f γ) (Metric.ball c r) := by
  classical
  rcases exists_analyticOnNhd_pathIntegralPrimitiveOn_ball hf hz₀ with
    ⟨F, hF_analytic, _hF_deriv, _hFz₀, hF_integral⟩
  refine hF_analytic.congr Metric.isOpen_ball ?_
  intro z hz
  rw [pathIntegralFromFamilyOnBall, dif_pos hz]
  exact hF_integral hz (γ ⟨z, hz⟩) (hγC1 ⟨z, hz⟩) (hγU ⟨z, hz⟩)
