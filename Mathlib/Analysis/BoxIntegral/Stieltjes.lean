/-
Copyright (c) ???. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: ???
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

namespace Stieltjes

open BoxIntegral LinearMap

/-- If  `g : ℝ → M` is a map, `dg : BoxAdditiveMap Unit M ⊤` is the box additive map that sends a box `J` to `g(J.upper()) - g(J.lower())`. -/
def deriv {M : Type*} [AddCommGroup M] (g : ℝ → M) :
    BoxAdditiveMap Unit M ⊤ :=
  BoxAdditiveMap.ofMapSplitAdd
    (fun J : Box Unit => g (J.upper ()) - g (J.lower ())) ⊤
    (by
      intro I _ i x hx
      cases i
      rw [Box.splitLower_def hx, Box.splitUpper_def hx]
      simp [Option.elim'])

/-- The interval [a,b).  -/
def interval (a b : ℝ) : Box Unit := sorry

/- Task 2: Define a Stieltjes integral of a function `f : ℝ → E` and `g : ℝ → F` given a bilinear map `B : E → F → G` and an interval `I` to give an output in `G`. -/

def HasIntegral {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  (B : E →ₗ[ℝ] F →ₗ[ℝ] G) (f : ℝ → E) (g : ℝ → F) (a b : ℝ) (L : G) : Prop :=
  BoxIntegral.HasIntegral (interval a b) IntegrationParams.Riemann (fun x ↦ f (x ()))
  (deriv (fun x ↦ (flip B) (g (x ())))) L

/- Task 3: Theorem A.1 of Montgomery Vaughan: if `f` is continuous and `g` is bounded variation
then the Stieltjes integral exists. -/

theorem exists_of_continuous_of_bounded_variation {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  (B : E →ₗ[ℝ] F →ₗ[ℝ] G) (f : ℝ → E) (g : ℝ → F) (a b : ℝ)
  (hf : ContinuousOn f (Set.Icc a b)) (hg : BoundedVariationOn g (Set.Icc a b)) :
  ∃ L, HasIntegral B f g a b L := by sorry

/- Task 4: Theorem A.2 of Montgomery Vaughan: if ∫_a^b f d g exists, then ∫_a^b g d f exists and
∫_a^b g d f = g(b) * f(b) - g(a) * f(a) - ∫_a^b f d g. -/

theorem integration_by_parts {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  (B : E →ₗ[ℝ] F →ₗ[ℝ] G) (f : ℝ → E) (g : ℝ → F) (a b : ℝ) {L : G}
  (hL : HasIntegral B f g a b L) :
  HasIntegral (flip B) g f a b (B (g b) (f b) - B (g a) (f a) - L) := by sorry

/- Task 5: Theorem A.3 (a).  If g′ is continuous on [a, b], then
Var[a,b]g = ∫_a^b |g'(x)|\ dx
-/

/- Task 6: Theorem A.3 (b).  If g′ is continuous on [a, b] and if in addition f is Riemann integrable, then
∫_a^b f (x) dg(x) = ∫_a^b f (x)g′(x) dx. -/


/-- Task 7: Theorem A.4 Suppose that g has bounded variation, and put g^∗(x) = Var[a,x]g. Then

∫_a^b f(x) dg(x) ≤ ∫_a^b | f (x)| dg∗(x).
provided that both integrals exist.
-/


/-- Task 8: Relate sums ∑ f(n) with Stieltjes integrals ∫ f d ⌊x⌋ -/



end Stieltjes
