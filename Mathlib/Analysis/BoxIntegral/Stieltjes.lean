/-
Copyright (c) ???. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ???
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

namespace StieltjesIntegral

/-- Task 1: Turn a map `g : ℝ → M` to a BoxAdditiveMap `dg : BoxAdditiveMap Unit M I` -/
def StieltjesDerivative {M : Type*} [AddCommMonoid M] (I: WithTop (Box Unit)) (g : ℝ → M): BoxAdditiveMap Unit M I := by sorry

/-- Task 2: Define a Stieltjes integral of a function `f : ℝ → E` and a function `g : R → (E →[L] F)` on an interval `I` by using `BoxIntegral`, the above additive map-/


/-- Task 3: Theorem A.1 of Montgomery Vaughan: if `f` is continuous and `g` is bounded variation then the Stieltjes integral exists.  -/

end StieltjesIntegral
