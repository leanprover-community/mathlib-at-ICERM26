/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module


public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Topology.Connected.LocPathConnected
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Subpath

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

namespace Path

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma intervalIntegral_reparam_C1
    {φ φ' : ℝ → ℝ} {g : ℝ → E}
    (hφ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (φ' x) x)
    (hφ' : ContinuousOn φ' (Set.uIcc (0 : ℝ) 1))
    (hg : ContinuousOn g (φ '' Set.uIcc (0 : ℝ) 1))
    (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    (∫ x in (0 : ℝ)..1, φ' x • g (φ x))
      = ∫ x in (0 : ℝ)..1, g x := by
  simpa [Function.comp_def, h0, h1] using
    (integral_deriv_smul_comp'
      (a := (0 : ℝ)) (b := 1)
      (f := φ) (f' := φ') (g := g)
      hφ hφ' hg)

/-- Piecewise-`C¹` substitution, in summed form.

Here `ts 0, ts 1, ..., ts n` is the subdivision. On each interval
`ts k..ts (k+1)`, the reparametrization has derivative `φ'`.

This version rewrites the source integral as a sum of target integrals. It does
not require the target-side integrals to telescope. -/
lemma intervalIntegral_reparam_piecewise_C1_sum
    {n : ℕ} {ts : ℕ → ℝ} {φ φ' : ℝ → ℝ} {g : ℝ → E}
    (hφ :
      ∀ k < n, ∀ x ∈ Set.uIcc (ts k) (ts (k + 1)),
        HasDerivAt φ (φ' x) x)
    (hφ' :
      ∀ k < n, ContinuousOn φ' (Set.uIcc (ts k) (ts (k + 1))))
    (hg :
      ∀ k < n, ContinuousOn g (φ '' Set.uIcc (ts k) (ts (k + 1))))
    (hFint :
      ∀ k < n,
        IntervalIntegrable
          (fun x => φ' x • g (φ x))
          volume
          (ts k) (ts (k + 1))) :
    (∫ x in ts 0..ts n, φ' x • g (φ x))
      =
    ∑ k ∈ Finset.range n,
      ∫ y in φ (ts k)..φ (ts (k + 1)), g y := by
  let F : ℝ → E := fun x => φ' x • g (φ x)

  have hpiece :
      ∀ k < n,
        (∫ x in ts k..ts (k + 1), F x)
          =
        ∫ y in φ (ts k)..φ (ts (k + 1)), g y := by
    intro k hk
    simpa [F, Function.comp_def] using
      (intervalIntegral.integral_deriv_smul_comp'
        (a := ts k) (b := ts (k + 1))
        (f := φ) (f' := φ') (g := g)
        (hφ k hk) (hφ' k hk) (hg k hk))

  have hsum_source :
      ∑ k ∈ Finset.range n,
          ∫ x in ts k..ts (k + 1), F x
        =
      ∫ x in ts 0..ts n, F x := by
    exact
      intervalIntegral.sum_integral_adjacent_intervals
        (f := F) (a := ts) (n := n)
        (by
          intro k hk
          simpa [F] using hFint k hk)

  calc
    (∫ x in ts 0..ts n, φ' x • g (φ x))
        = ∫ x in ts 0..ts n, F x := by
            rfl
    _ = ∑ k ∈ Finset.range n,
          ∫ x in ts k..ts (k + 1), F x := by
            exact hsum_source.symm
    _ = ∑ k ∈ Finset.range n,
          ∫ y in φ (ts k)..φ (ts (k + 1)), g y := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact hpiece k (Finset.mem_range.mp hk)

/-- Piecewise-`C¹` substitution, telescoped form.

This is the clean total-integral version:

`∫ φ' • g ∘ φ = ∫ g`

from `ts 0` to `ts n`, with no monotonicity assumption on `φ`. The target
intervals telescope because interval integrals are oriented. -/
lemma intervalIntegral_reparam_piecewise_C1
    {n : ℕ} {ts : ℕ → ℝ} {φ φ' : ℝ → ℝ} {g : ℝ → E}
    (hφ :
      ∀ k < n, ∀ x ∈ Set.uIcc (ts k) (ts (k + 1)),
        HasDerivAt φ (φ' x) x)
    (hφ' :
      ∀ k < n, ContinuousOn φ' (Set.uIcc (ts k) (ts (k + 1))))
    (hg :
      ∀ k < n, ContinuousOn g (φ '' Set.uIcc (ts k) (ts (k + 1))))
    (hFint :
      ∀ k < n,
        IntervalIntegrable
          (fun x => φ' x • g (φ x))
          volume
          (ts k) (ts (k + 1)))
    (hgint :
      ∀ k < n,
        IntervalIntegrable
          g volume
          (φ (ts k)) (φ (ts (k + 1)))) :
    (∫ x in ts 0..ts n, φ' x • g (φ x))
      =
    ∫ y in φ (ts 0)..φ (ts n), g y := by
  have hsum_target :
      ∑ k ∈ Finset.range n,
          ∫ y in φ (ts k)..φ (ts (k + 1)), g y
        =
      ∫ y in φ (ts 0)..φ (ts n), g y := by
    exact
      intervalIntegral.sum_integral_adjacent_intervals
        (f := g) (a := fun k => φ (ts k)) (n := n)
        (by
          intro k hk
          simpa using hgint k hk)

  calc
    (∫ x in ts 0..ts n, φ' x • g (φ x))
        =
      ∑ k ∈ Finset.range n,
        ∫ y in φ (ts k)..φ (ts (k + 1)), g y := by
          exact
            intervalIntegral_reparam_piecewise_C1_sum
              (n := n) (ts := ts) (φ := φ) (φ' := φ') (g := g)
              hφ hφ' hg hFint
    _ = ∫ y in φ (ts 0)..φ (ts n), g y := hsum_target

/-- Piecewise-`C¹` substitution on `[0,1]`.
This is probably the form you want for reparametrizations of paths. -/

lemma intervalIntegral_reparam_piecewise_C1_zero_one
    {n : ℕ} {ts : ℕ → ℝ} {φ φ' : ℝ → ℝ} {g : ℝ → E}
    (hφ : ∀ k < n, ∀ x ∈ Set.uIcc (ts k) (ts (k + 1)), HasDerivAt φ (φ' x) x)
    (hφ' : ∀ k < n, ContinuousOn φ' (Set.uIcc (ts k) (ts (k + 1))))
    (hg : ∀ k < n, ContinuousOn g (φ '' Set.uIcc (ts k) (ts (k + 1))))
    (hFint : ∀ k < n, IntervalIntegrable (fun x => φ' x • g (φ x)) volume (ts k) (ts (k + 1)))
    (hgint : ∀ k < n, IntervalIntegrable g volume (φ (ts k)) (φ (ts (k + 1))))
    (hts0 : ts 0 = 0)
    (htsn : ts n = 1)
    (hφ0 : φ 0 = 0)
    (hφ1 : φ 1 = 1) :
    (∫ x in (0 : ℝ)..1, φ' x • g (φ x))
      =
    ∫ y in (0 : ℝ)..1, g y := by
  simpa [hts0, htsn, hφ0, hφ1] using
    (intervalIntegral_reparam_piecewise_C1
      (n := n) (ts := ts) (φ := φ) (φ' := φ') (g := g)
      hφ hφ' hg hFint hgint)

noncomputable abbrev equalGrid (N : ℕ) : Fin (N + 1) → I := fun i => ⟨i / N, by
  simp
  constructor
  · positivity
  · exact div_le_one_of_le₀ (by exact_mod_cast Nat.lt_succ_iff.mp i.isLt) (by positivity)⟩

end Path

