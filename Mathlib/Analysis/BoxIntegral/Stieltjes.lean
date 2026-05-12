/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! # Riemann–Stieltjes integral

In this file we define the (one-dimensional) Riemann–Stieltjes integral of a function
`f : ℝ → E` against an integrator `g : ℝ → F`, paired by a continuous bilinear map
`B : E →L[ℝ] F →L[ℝ] G`. The integral is realized as a `BoxIntegral.HasIntegral` over the
half-open interval `(a, b]`, viewed as a `Box (Fin 1)`, with respect to the box-additive
"differential" associated to `g`.

The development follows the treatment of Riemann–Stieltjes integration in
Montgomery–Vaughan, *Multiplicative Number Theory I: Classical Theory*, Appendix A.

## Main definitions

* `BoxIntegral.BoxAdditiveMap.ofDiff g`: the box-additive map associated to `g : ℝ → M`,
  sending a box `J` to `g (J.upper 0) - g (J.lower 0)`.
* `Stieltjes.interval a b`: the half-open interval `(a, b]` as a `Box (Fin 1)` (returning a
  dummy box when `a ≥ b`).
* `HasStieltjesIntegral a b B f g L`: the predicate asserting that `L : G` is the
  Riemann–Stieltjes integral of `f` against `g`, paired by the bilinear map `B`, over `(a, b]`.
* `Stieltjes.RiemannIntegrable a b f`: a placeholder predicate for Riemann integrability of
  `f` on `(a, b]`.

## Main theorems

* `Stieltjes.exists_of_continuousOn_of_boundedVariationOn` (Theorem A.1): if `f` is continuous
  and `g` has bounded variation on `[a, b]`, then the Riemann–Stieltjes integral exists.
* `Stieltjes.integration_by_parts` (Theorem A.2): integration by parts.
* `Stieltjes.variation_of_derivative` (Theorem A.3(a)) and
  `Stieltjes.integral_of_derivative` (Theorem A.3(b)): when `g` is `C¹`, the total variation
  and the Riemann–Stieltjes integral are computed from `g′`.
* `Stieltjes.integral_le_integral_of_variation` (Theorem A.4): a norm bound on the integral
  in terms of the variation of `g`.
* `Stieltjes.sum_eq_integral_nat_floor` and `Stieltjes.sum_eq_integral_int_floor`: relate
  sums `∑ f n` to Riemann–Stieltjes integrals against the floor function.
* `Stieltjes.sum_eq_integral_natSummatory_le` / `_lt` : relate sums `∑ B (f n) (g n)` to
  Riemann–Stieltjes integrals against the right- or left-continuous summatory function
  `x ↦ ∑ n ≤ x, g n` (resp. `x ↦ ∑ n < x, g n`).

## Endpoint convention

The underlying box `Stieltjes.interval a b` is the half-open interval `(a, b]`, but the
hypotheses below typically use `Set.Icc a b` — this is needed both for compactness
(for `ContinuousOn` / `ContDiffOn` arguments) and to include the value `g a` in
bounded-variation hypotheses, since the leftmost sub-box can have lower endpoint `a`.
See the comment near `HasStieltjesIntegral` for details.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*,
  Cambridge Studies in Advanced Mathematics 97, Cambridge University Press, 2007 (Appendix A).

## Tags

Stieltjes integral, Riemann–Stieltjes, bounded variation
-/


namespace BoxIntegral.BoxAdditiveMap

/-- If `g : ℝ → M` is a map, `ofDiff g : BoxAdditiveMap (Fin 1) M ⊤` is the box additive map that
sends a box `J` to `g (J.upper 0) - g (J.lower 0)`. -/
def ofDiff {M : Type*} [AddCommGroup M] (g : ℝ → M) :
    BoxAdditiveMap (Fin 1) M ⊤ :=
  ofMapSplitAdd
    (fun J : Box (Fin 1) => g (J.upper 0) - g (J.lower 0)) ⊤
    (by
      intro I _ i x hx
      fin_cases i
      rw [Box.splitLower_def hx, Box.splitUpper_def hx]
      simp [Option.elim'])

end BoxIntegral.BoxAdditiveMap

open BoxIntegral ContinuousLinearMap

namespace Stieltjes

/-- The interval (a, b]. Returns the dummy interval (0, 1] if a ≥ b. -/
noncomputable def interval (a b : ℝ) : Box (Fin 1) :=
  if h : a < b then
    { lower := fun _ ↦ a
      upper := fun _ ↦ b
      lower_lt_upper := fun _ ↦ h }
  else
    { lower := fun _ ↦ 0
      upper := fun _ ↦ 1
      lower_lt_upper := fun _ ↦ zero_lt_one }

/- Our notion of Stieltjes transformation requires a choice of continuous bilinear mapping from the
ranges of `f`, `g` to the desired output range.
Standard choices already available in Mathlib
include:
* `ContinuousLinearMap.mul ℝ A : A →L[ℝ] A →L[ℝ] A` for `A` a normed `ℝ`-algebra
  (e.g. when `f`, `g` are both real- or both complex-valued).
* `ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E` for scalar multiplication when `f` is real,
  and `(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip : E →L[ℝ] ℝ →L[ℝ] E` when `g`
  is real.
Use `ContinuousLinearMap.flip` to swap the argument order of any of these. -/

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable (a b : ℝ) (B : E →L[ℝ] F →L[ℝ] G)

/- Endpoint convention. The underlying box `interval a b` is the half-open interval `(a, b]`,
but most hypotheses and outputs below use `Set.Icc a b` rather than `Set.Ioc a b`. This is the
conservative choice and is needed in several places:
* `ContinuousOn` / `ContDiffOn` hypotheses rely on compactness of the domain (e.g. for uniform
  continuity), which fails on `Ioc`.
* For a prepartition of `(a, b]` the leftmost sub-box has lower endpoint `a`, so `g a` appears
  in `BoxAdditiveMap.ofDiff g`. Bounded-variation hypotheses on `g` must therefore include `a`.
Some occurrences below may admit a half-open weakening; for now we keep `Set.Icc` everywhere
and flag this as a possible future refinement. -/

/-- The Stieltjes integral of a function `f : ℝ → E` and `g : ℝ → F` given a bilinear
map `B : E → F → G` and endpoints `a`, `b` takes values in `G`. -/
def HasStieltjesIntegral (f : ℝ → E) (g : ℝ → F) (L : G) : Prop :=
  HasIntegral (Stieltjes.interval a b) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) (BoxAdditiveMap.ofDiff (fun x ↦ B.flip (g x))) L

/-- For any valid box partition of (a, b], the sum of the norm of the
differential `ofDiff g` is bounded by the total variation of g on the interval. -/
lemma sum_norm_ofDiff_le_norm_mul_eVariationOn (g : ℝ → F)
    (hg : BoundedVariationOn g (Set.Icc a b))
    (π : Prepartition (interval a b)) :
    ∑ J ∈ π.boxes, ‖(BoxAdditiveMap.ofDiff (fun x ↦ B.flip (g x))) J‖ ≤
      ‖B‖ * (eVariationOn g (Set.Icc a b)).toReal := by
  sorry

/-- Prove that the Riemann-Stieltjes integrand is Box-Integrable.
Use the Cauchy criterion and the uniform continuity of f on [a, b].
We separate integrability for more modular API. -/
lemma integrable_of_continuousOn_of_boundedVariationOn
    (f : ℝ → E) (g : ℝ → F)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : BoundedVariationOn g (Set.Icc a b)) :
    Integrable (interval a b) IntegrationParams.Riemann
      (fun x ↦ f (x 0)) (BoxAdditiveMap.ofDiff (fun x ↦ B.flip (g x))) := by sorry

/-! ## Main theorems -/

/-- Theorem A.1 of Montgomery Vaughan: if `f` is continuous and `g` is bounded variation
then the Stieltjes integral exists. -/
theorem exists_of_continuousOn_of_boundedVariationOn
    (f : ℝ → E) (g : ℝ → F)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : BoundedVariationOn g (Set.Icc a b)) :
    ∃ L, HasStieltjesIntegral a b B f g L := by
  have hint := integrable_of_continuousOn_of_boundedVariationOn a b B f g hf hg
  exact ⟨_, Integrable.hasIntegral hint⟩

/-- Theorem A.2 of Montgomery Vaughan: if ∫ₐᵇ f dg exists, then ∫ₐᵇ g df exists and
∫ₐᵇ g df = g(b) * f(b) - g(a) * f(a) - ∫ₐᵇ f dg. -/
theorem integration_by_parts {f : ℝ → E} {g : ℝ → F} {L : G}
    (hL : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral a b B.flip g f (B (f b) (g b) - B (f a) (g a) - L) := by sorry

/-- Theorem A.3 (a).  If g′ is continuous on [a, b], then
Varₐᵇ g = ∫ₐᵇ ‖g′(x)‖ dx.
-/
theorem variation_of_derivative {g : ℝ → F} (hgdiff : ContDiffOn ℝ 1 g (Set.Icc a b)) :
    (eVariationOn g (Set.Icc a b)).toReal = ∫ x in a..b, ‖deriv g x‖ := by sorry

/-- Placeholder abbreviation; there may be a better spelling for this. -/
abbrev RiemannIntegrable (f : ℝ → E) : Prop :=
  Integrable (interval a b) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) BoxAdditiveMap.volume

/-- Theorem A.3 (b).  If g′ is continuous on [a, b] and if in addition f is
Riemann integrable, then ∫ₐᵇ f(x) dg(x) = ∫ₐᵇ f(x) g′(x) dx. -/
theorem integral_of_derivative {f : ℝ → E} {g : ℝ → F}
    (hgdiff : ContDiffOn ℝ 1 g (Set.Icc a b))
    (hfint : RiemannIntegrable a b f) :
    HasStieltjesIntegral a b B f g (∫ x in a..b, B (f x) (deriv g x)) := by sorry

/-- Theorem A.4. Suppose that g has bounded variation, and put g∗(x) = Varₐˣ g. Then
‖∫ₐᵇ f(x) dg(x)‖ ≤ ∫ₐᵇ ‖f(x)‖ dg∗(x),
provided that both integrals exist. -/
theorem integral_le_integral_of_variation {f : ℝ → E} {g : ℝ → F} {L : G} {L' : ℝ}
    (hgvar : BoundedVariationOn g (Set.Icc a b))
    (hfgint : HasStieltjesIntegral a b B f g L)
    (hfabs_gstar : HasStieltjesIntegral a b (mul ℝ ℝ) (fun x ↦ ‖f x‖)
      (fun x ↦ (eVariationOn g (Set.Icc a x)).toReal) L') :
    ‖L‖ ≤ ‖B‖ * L' := by sorry

/-- Relate sums ∑ f(n) with Stieltjes integrals ∫ f d ⌊x⌋ -/
theorem sum_eq_integral_nat_floor (f : ℝ → E) :
    HasStieltjesIntegral a b (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip f
      (fun x ↦ Nat.floor x)
      (∑ n ∈ Finset.Ico (Nat.ceil a) (Nat.ceil b), f n) := by sorry

theorem sum_eq_integral_int_floor (f : ℝ → E) :
    HasStieltjesIntegral a b (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip f
      (fun x ↦ Int.floor x)
      (∑ n ∈ Finset.Ico (Int.ceil a) (Int.ceil b), f n) := by sorry

/-- Sum of pairings `B (f n) (g n)` over natural `n ∈ (⌊a⌋, ⌊b⌋]`, expressed as a Stieltjes
integral of `f` against the right-continuous summatory `x ↦ ∑ n ≤ x, g n`. -/
theorem sum_eq_integral_natSummatory_le (f : ℝ → E) (g : ℕ → F) :
    HasStieltjesIntegral a b B f
      (fun x ↦ ∑ n ∈ Finset.Iic (Nat.floor x), g n)
      (∑ n ∈ Finset.Ioc (Nat.floor a) (Nat.floor b), B (f n) (g n)) := by sorry

/-- Sum of pairings `B (f n) (g n)` over natural `n ∈ [⌈a⌉, ⌈b⌉)`, expressed as a Stieltjes
integral of `f` against the left-continuous summatory `x ↦ ∑ n < x, g n`. -/
theorem sum_eq_integral_natSummatory_lt (f : ℝ → E) (g : ℕ → F) :
    HasStieltjesIntegral a b B f
      (fun x ↦ ∑ n ∈ Finset.Iio (Nat.ceil x), g n)
      (∑ n ∈ Finset.Ico (Nat.ceil a) (Nat.ceil b), B (f n) (g n)) := by sorry

end Stieltjes
