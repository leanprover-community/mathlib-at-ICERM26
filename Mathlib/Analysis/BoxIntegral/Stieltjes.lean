/-
Copyright (c) ???. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ???
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation

namespace Stieltjes

open BoxIntegral

/-- If  `g : ℝ → M` is a map, `dg : BoxAdditiveMap Unit M ⊤` is the box additive map that sends a box `J` to `g(J.upper()) - g(J.lower())`.
-/
def deriv {M : Type*} [AddCommGroup M] (g : ℝ → M) :
    BoxAdditiveMap Unit M ⊤ :=
  BoxAdditiveMap.ofMapSplitAdd
    (fun J : Box Unit => g (J.upper ()) - g (J.lower ())) ⊤
    (by
      intro I _ i x hx
      cases i
      rw [Box.splitLower_def hx, Box.splitUpper_def hx]
      simp [Option.elim'])

/-- The interval [a,b).
-/
def interval (a b : ℝ) : Box Unit := sorry

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable (a b : ℝ) (B : E →L[ℝ] F →L[ℝ] G)

def flip (B : E →L[ℝ] F →L[ℝ] G) : F →L[ℝ] E →L[ℝ] G := sorry

/-- The Stieltjes integral of a function `f : ℝ → E` and `g : ℝ → F` given a bilinear
 map `B : E → F → G` and an interval `I` takes values in `G`.
-/
def HasIntegral (f : ℝ → E) (g : ℝ → F) (L : G) : Prop :=
  BoxIntegral.HasIntegral (interval a b) IntegrationParams.Riemann (fun x ↦ f (x ()))
  (deriv (fun x ↦ (flip B) (g x))) L

/-- Theorem A.1 of Montgomery Vaughan: if `f` is continuous and `g` is bounded variation
then the Stieltjes integral exists.
-/
theorem exists_of_continuous_of_bounded_variation
  (f : ℝ → E) (g : ℝ → F)
  (hf : ContinuousOn f (Set.Icc a b)) (hg : BoundedVariationOn g (Set.Icc a b)) :
  ∃ L, HasIntegral a b B f g L := by sorry

/-- Theorem A.2 of Montgomery Vaughan: if ∫_a^b f d g exists, then ∫_a^b g d f exists and
∫_a^b g d f = g(b) * f(b) - g(a) * f(a) - ∫_a^b f d g.
-/
theorem integration_by_parts {f : ℝ → E} {g : ℝ → F} {L : G}
  (hL : HasIntegral a b B f g L) :
  HasIntegral a b (flip B) g f (B (g b) (f b) - B (g a) (f a) - L) := by sorry

/-- Theorem A.3 (a).  If g′ is continuous on [a, b], then
Var[a,b]g = ∫_a^b |g'(x)|\ dx
-/
theorem variation_of_derivative {g : ℝ → F} (hgdiff : ContDiffOn ℝ g (Set.Icc a b)) :
  eVariationOn g (Set.Icc a b) = ∫ x in a..b, ‖deriv g x‖ := by sorry

/- Task 6: Theorem A.3 (b).  If g′ is continuous on [a, b] and if in addition f is Riemann integrable, then
∫_a^b f (x) dg(x) = ∫_a^b f (x)g′(x) dx. -/
theorem integral_of_derivative {f : ℝ → E} {g : ℝ → F}
  (hgdiff : ContDiffOn ℝ g (Set.Icc a b)) (hfint : BoxIntegral.Integrable (interval a b) IntegrationParams.Riemann f) :
  HasIntegral a b B f g (∫ x in a..b, B (f x) (deriv g x)) := by sorry


/-- Task 7: Theorem A.4 Suppose that g has bounded variation, and put g^∗(x) = Var[a,x]g. Then

∫_a^b f(x) dg(x) ≤ ∫_a^b | f (x)| dg∗(x).
provided that both integrals exist.
-/


/-- Task 8: Relate sums ∑ f(n) with Stieltjes integrals ∫ f d ⌊x⌋ -/



end Stieltjes
