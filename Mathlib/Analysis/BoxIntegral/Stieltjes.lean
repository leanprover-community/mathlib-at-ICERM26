/-
Copyright (c) ???. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ???
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

namespace StieltjesIntegral

/-- Task 1: Turn a map `g : ℝ → M` to a BoxAdditiveMap `dg : BoxAdditiveMap Unit M ⊤` -/
def StieltjesDerivative {M : Type*} [AddCommGroup M] (g : ℝ → M) :
    BoxIntegral.BoxAdditiveMap Unit M ⊤ :=
  BoxIntegral.BoxAdditiveMap.ofMapSplitAdd
    (fun J : BoxIntegral.Box Unit => g (J.upper ()) - g (J.lower ())) ⊤
    (by
      intro I _ i x hx
      cases i
      rw [BoxIntegral.Box.splitLower_def hx, BoxIntegral.Box.splitUpper_def hx]
      simp [Option.elim'])

/- Task 2: Define a Stieltjes integral of a function `f : ℝ → E` and a function
`g : R → (E →[L] F)` on an interval `I` by using `BoxIntegral`, the above additive map. -/

/- Task 2': Also define a Stieltjes integral of a function `f : ℝ → E` and a function
`g : ℝ → F` given a bilinear map `B : E → F → G` to give an output in `G`. -/


/- Task 3: Theorem A.1 of Montgomery Vaughan: if `f` is continuous and `g` is bounded variation
then the Stieltjes integral exists. -/


/- Task 4: Theorem A.2 of Montgomery Vaughan: if ∫_a^b f d g exists, then ∫_a^b g d f exists and
∫_a^b g d f = g(b) * f(b) - g(a) * f(a) - ∫_a^b f d g. -/


/- Task 5: Theorem A.3 (a).  If g′ is continuous on [a, b], then
Var[a,b]g = ∫_a^b |g'(x)|\ dx
-/

/- Task 6: Theorem A.3 (b).  If g′ is continuous on [a, b] and if in addition f is Riemann integrable, then
∫_a^b f (x) dg(x) = ∫_a^b f (x)g′(x) dx. -/


/-- Task 7: Theorem A.4 Suppose that g has bounded variation, and put g^∗(x) = Var[a,x]g. Then

∫_a^b f(x) dg(x) ≤ ∫_a^b | f (x)| dg∗(x).
provided that both integrals exist.
-/



end StieltjesIntegral
