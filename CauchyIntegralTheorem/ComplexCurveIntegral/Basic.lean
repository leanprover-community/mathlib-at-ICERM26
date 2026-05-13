/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module

public import Topology.Path.UniformClose
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.LinearAlgebra.Complex.Module

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section
public noncomputable abbrev fdzForm (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.mul ℂ ℂ (f z)

@[simp]
lemma fdzForm_apply (f : ℂ → ℂ) (z v : ℂ) :
    fdzForm f z v = f z * v := by
  simp [fdzForm]

/-- Complex curve integral `∫_γ f dz`, defined via mathlib's `curveIntegral`. -/
public noncomputable abbrev complexCurveIntegral {a b : ℂ} (f : ℂ → ℂ) (γ : Path a b) : ℂ :=
  ∫ᶜ z in γ, fdzForm f z

lemma complexCurveIntegral_def {a b : ℂ} (f : ℂ → ℂ) (γ : Path a b) :
    complexCurveIntegral f γ = ∫ᶜ z in γ, fdzForm f z := rfl

@[expose] noncomputable def complexCurveIntegrand {a b : ℂ} (f : ℂ → ℂ) (γ : Path a b) :
    ℝ → ℂ :=
  fun t => f (γ.extend t) * deriv (⇑γ.extend) t

lemma complexCurveIntegrand_apply {a b : ℂ} (f : ℂ → ℂ) (γ : Path a b) (t : ℝ) :
    complexCurveIntegrand f γ t = f (γ.extend t) * deriv (⇑γ.extend) t := rfl

/-- Unfolding gives the usual `∫₀¹ f(γ t) γ'(t) dt`. -/
lemma complexCurveIntegral_eq_intervalIntegral_deriv
    {a b : ℂ} (f : ℂ → ℂ) (γ : Path a b) :
    complexCurveIntegral f γ =
      ∫ t in (0 : ℝ)..1, complexCurveIntegrand f γ t := by
  rw [complexCurveIntegral, curveIntegral_eq_intervalIntegral_deriv]
  simp [complexCurveIntegrand, fdzForm]

@[simp]
theorem complexCurveIntegral_segment_same {a : ℂ} (f : ℂ → ℂ) :
    complexCurveIntegral f (Path.segment a a) = 0 := by
  simp [complexCurveIntegral, Path.segment_same, curveIntegral_refl]


