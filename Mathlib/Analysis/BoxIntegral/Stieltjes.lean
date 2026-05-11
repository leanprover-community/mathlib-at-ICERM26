/-
Copyright (c) ???. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ???
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

namespace Stieltjes

/-- Task 1: Turn a map `g : ℝ → M` to a BoxAdditiveMap `dg : BoxAdditiveMap Unit M ⊤` -/
def StieltjesDerivative {M : Type*} [AddCommGroup M] (g : ℝ → M): BoxAdditiveMap Unit M ⊤ := by sorry

/-- Task 2: Define a Stieltjes integral of a function `f : ℝ → E` and a function `g : R → F` and given a bilinear map `B : E → F → G` to give an output in `G` on an interval `I` by using `BoxIntegral`, and the above additive map-/

def hasIntegral {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  (B : E → F → G) (f : ℝ → E) (g : ℝ → F) (I : Interval ℝ) (L : G) : Prop := by sorry

/-- Task 3: Theorem A.1 of Montgomery Vaughan: if `f` is continuous and `g` is bounded variation then the Stieltjes integral exists.  -/

theorem exists_of_continuous_of_bounded_variation {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  (B : E → F → G) (f : ℝ → E) (g : ℝ → F) (I : Interval ℝ)
  (hf : ContinuousOn f I) (hg : BoundedVariationOn g I) :
  ∃ L, hasIntegral B f g I L := by sorry

/-- Task 4: Theorem A.2 of Montgomery Vaughan: if ∫_a^b f d g exists, then ∫_a^b g d f exists and
∫_a^b g d f = g(b) * f(b) - g(a) * f(a) - ∫_a^b f d g. -/

def symm {E : Type*} {F : Type*} {G : Type*} (B : E → F → G) : F → E → G := by sorry

theorem integration_by_parts {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  (B : E → F → G) (f : ℝ → E) (g : ℝ → F) (I : Interval ℝ) {L : G}
  (hL : hasIntegral B f g I L) :
  hasIntegral (symm B) g f I (B (g I.2) (f I.2) - B (g I.1) (f I.1) - L) := by sorry

/-- Task 5: Theorem A.3 (a).  If g′ is continuous on [a, b], then
Var[a,b]g = ∫_a^b |g'(x)|\ dx
-/

/-- Task 6: Theorem A.3 (b).  If g′ is continuous on [a, b] and if in addition f is Riemann integrable, then
∫_a^b f (x) dg(x) = ∫_a^b f (x)g′(x) dx. -/


/-- Task 7: Theorem A.4 Suppose that g has bounded variation, and put g^∗(x) = Var[a,x]g. Then

∫_a^b f(x) dg(x) ≤ ∫_a^b | f (x)| dg∗(x).
provided that both integrals exist.
-/


/-- Task 8: Relate sums ∑ f(n) with Stieltjes integrals ∫ f d ⌊x⌋ -/



end Stieltjes
