/-
Copyright (c) ???. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ???
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

namespace StieltjesIntegral

/-- Turn a map `g : ℝ → M` to a BoxAdditiveMap `dg : BoxAdditiveMap Unit M I` -/
def StieltjesDerivative {M : Type*} [AddCommMonoid M] (I: WithTop (Box Unit)) (g : ℝ → M): BoxAdditiveMap Unit M I := by sorry


end StieltjesIntegral
