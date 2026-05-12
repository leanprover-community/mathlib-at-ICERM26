/-
Copyright (c) ???. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: ???
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace BoxIntegral.BoxAdditiveMap

/-- If `g : ℝ → M` is a map, `ofDiff g : BoxAdditiveMap Unit M ⊤` is the box additive map that
sends a box `J` to `g (J.upper ()) - g (J.lower ())`. -/
def ofDiff {M : Type*} [AddCommGroup M] (g : ℝ → M) :
    BoxAdditiveMap Unit M ⊤ :=
  ofMapSplitAdd
    (fun J : Box Unit => g (J.upper ()) - g (J.lower ())) ⊤
    (by
      intro I _ i x hx
      cases i
      rw [Box.splitLower_def hx, Box.splitUpper_def hx]
      simp [Option.elim'])

end BoxIntegral.BoxAdditiveMap

open BoxIntegral

namespace Stieltjes

/-- The interval (a,b]. Returns the dummy interval (0, 1] if a ≥ b. -/
noncomputable def interval (a b : ℝ) : Box Unit :=
  if h : a < b then
    { lower := fun _ ↦ a
      upper := fun _ ↦ b
      lower_lt_upper := fun _ ↦ h }
  else
    { lower := fun _ ↦ 0
      upper := fun _ ↦ 1
      lower_lt_upper := fun _ ↦ zero_lt_one }

end Stieltjes

/- Our notion of Stieltjes transformation requires a choice of continuous bilinear mapping from the
ranges of `f`, `g` to the desired output range. Standard choices already available in Mathlib
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

/-- The Stieltjes integral of a function `f : ℝ → E` and `g : ℝ → F` given a bilinear
map `B : E → F → G` and endpoints `a`, `b` takes values in `G`. -/
def HasStieltjesIntegral (f : ℝ → E) (g : ℝ → F) (L : G) : Prop :=
  BoxIntegral.HasIntegral (Stieltjes.interval a b) IntegrationParams.Riemann
    (fun x ↦ f (x ())) (BoxAdditiveMap.ofDiff (fun x ↦ B.flip (g x))) L

namespace Stieltjes

/-- Theorem A.1 of Montgomery Vaughan: if `f` is continuous and `g` is bounded variation
then the Stieltjes integral exists. -/
theorem exists_of_continuous_of_bounded_variation
  (f : ℝ → E) (g : ℝ → F)
  (hf : ContinuousOn f (Set.Icc a b)) (hg : BoundedVariationOn g (Set.Icc a b)) :
  ∃ L, HasStieltjesIntegral a b B f g L := by sorry

/-- Theorem A.2 of Montgomery Vaughan: if ∫_a^b f d g exists, then ∫_a^b g d f exists and
∫_a^b g d f = g(b) * f(b) - g(a) * f(a) - ∫_a^b f d g. -/
theorem integration_by_parts {f : ℝ → E} {g : ℝ → F} {L : G}
  (hL : HasStieltjesIntegral a b B f g L) :
  HasStieltjesIntegral a b B.flip g f (B (f b) (g b) - B (f a) (g a) - L) := by sorry

/-- Theorem A.3 (a).  If g′ is continuous on [a, b], then
Var[a,b]g = ∫_a^b |g'(x)|\ dx
-/
theorem variation_of_derivative {g : ℝ → F} (hgdiff : ContDiffOn ℝ 1 g (Set.Icc a b)) :
  (eVariationOn g (Set.Icc a b)).toReal = ∫ x in a..b, ‖deriv g x‖ := by sorry

/-- Is there a better spelling for this? -/
def RiemannIntegrable (f : ℝ → E) : Prop := BoxIntegral.Integrable (interval a b)
  IntegrationParams.Riemann (fun x ↦ f (x ())) BoxAdditiveMap.volume

/-- Theorem A.3 (b).  If g′ is continuous on [a, b] and if in addition f is
Riemann integrable, then ∫_a^b f (x) dg(x) = ∫_a^b f (x)g′(x) dx. -/
theorem integral_of_derivative {f : ℝ → E} {g : ℝ → F}
  (hgdiff : ContDiffOn ℝ 1 g (Set.Icc a b))
  (hfint : RiemannIntegrable a b f) :
  HasStieltjesIntegral a b B f g (∫ x in a..b, B (f x) (deriv g x)) := by sorry


/-- Theorem A.4. Suppose that g has bounded variation, and put g^∗(x) = Var[a,x]g. Then
∫_a^b f(x) dg(x) ≤ ∫_a^b | f (x)| dg∗(x).
provided that both integrals exist. -/
theorem integral_le_integral_of_variation {f : ℝ → E} {g : ℝ → F}
  (hgvar : BoundedVariationOn g (Set.Icc a b)) (L : G) (L' M : ℝ)
  (hfgint : HasStieltjesIntegral a b B f g L)
  (hbound : ∀ e f, ‖B e f‖ ≤ M * ‖e‖ * ‖f‖)
  (hfabs_gstar : HasStieltjesIntegral a b (ContinuousLinearMap.mul ℝ ℝ) (fun x ↦ ‖f x‖)
    (fun x ↦ (eVariationOn g (Set.Icc a x)).toReal) L') :
  ‖L‖ ≤ M * L' := by sorry

/-- Relate sums ∑ f(n) with Stieltjes integrals ∫ f d ⌊x⌋ -/
theorem sum_le_integral_nat_floor (f : ℝ → E) :
  HasStieltjesIntegral a b (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip f
    (fun x ↦ Nat.floor x)
    (∑ n ∈ Finset.Ico (Nat.ceil a) (Nat.ceil b), f n) := by sorry

theorem sum_le_integral_floor (f : ℝ → E) :
  HasStieltjesIntegral a b (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip f
    (fun x ↦ Int.floor x)
    (∑ n ∈ Finset.Ico (Int.ceil a) (Int.ceil b), f n) := by sorry


end Stieltjes