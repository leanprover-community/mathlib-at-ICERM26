/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Stieltjes


/-! # Riemann–Stieltjes integral and Stieltjes measure

In this file we show that the Riemann–Stieltjes integral
`∫⟨B⟩ x in a..b, f x ∂g` defined in `Analysis.BoxIntegral.Stieltjes.Defs` is compatible
with the Stieltjes measure defined in `MeasureTheory.Measure.Stieltjes` when g is monotone.

-/

@[expose] public section

namespace BoxIntegral

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {a b : ℝ}

theorem HasStieltjesIntegral.of_continuous_of_Stieltjes
    {f : ℝ → E} {g : ℝ → ℝ} (hab : a < b)
    (hf : ContinuousOn f (.Icc a b)) (g : StieltjesFunction ℝ) :
    HasStieltjesIntegral a b ((lsmul ℝ ℝ).flip) f (g : ℝ → ℝ) (∫ x in a..b, f x ∂g.measure) := by
  sorry


end BoxIntegral
