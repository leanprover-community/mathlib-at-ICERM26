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

namespace Stieltjes

open BoxIntegral

/-- If  `g : ℝ → M` is a map, `dg : BoxAdditiveMap Unit M ⊤` is the box additive map that sends
a box `J` to `g(J.upper()) - g(J.lower())`.
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


/-- The interval [a,b). Returns the dummy interval [0, 1) if a ≥ b. -/
noncomputable def interval (a b : ℝ) : Box Unit :=
  if h : a < b then
    { lower := fun _ ↦ a
      upper := fun _ ↦ b
      lower_lt_upper := fun _ ↦ h }
  else
    { lower := fun _ ↦ 0
      upper := fun _ ↦ 1
      lower_lt_upper := fun _ ↦ zero_lt_one }

/- Our notion of Stieltjes transformation requires a choice of continuous bilinear mapping from the
ranges of `f`, `g` to the desired output range. Below we set out some standard choices. -/

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable (a b : ℝ) (B : E →L[ℝ] F →L[ℝ] G)

/-- A version of `LinearMap.flip` for continuous linear maps. -/
noncomputable def flip (B : E →L[ℝ] F →L[ℝ] G) : F →L[ℝ] E →L[ℝ] G :=
  B.flip

/-- Right scalar multiplication on the reals as a bilinear map.
A suitable choice for Stieltjes integrals when `g` is real. -/
noncomputable def smul_right : E →L[ℝ] ℝ →L[ℝ] E :=
  ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)

/-- Left scalar multiplication on the reals as a bilinear map.
A suitable choice for Stieltjes integrals when `f` is real. -/
noncomputable def smul_left : ℝ →L[ℝ] F →L[ℝ] F := flip smul_right

/-- Normed algebra multiplication (e.g., on ℝ or ℂ) as a bilinear map.
A suitable choice for Stieltjes integrals when `f`, `g` are both real or both complex. -/
noncomputable def mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] :
  A →L[ℝ] A →L[ℝ] A :=
  ContinuousLinearMap.mul ℝ A

/-- The Stieltjes integral of a function `f : ℝ → E` and `g : ℝ → F` given a bilinear
 map `B : E → F → G` and endpoints `a`, `b` takes values in `G`. -/
def HasIntegral (f : ℝ → E) (g : ℝ → F) (L : G) : Prop :=
  BoxIntegral.HasIntegral (interval a b) IntegrationParams.Riemann (fun x ↦ f (x ()))
  (deriv (fun x ↦ (flip B) (g x))) L

/-- Theorem A.1 of Montgomery Vaughan: if `f` is continuous and `g` is bounded variation
then the Stieltjes integral exists. -/
theorem exists_of_continuous_of_bounded_variation
  (f : ℝ → E) (g : ℝ → F)
  (hf : ContinuousOn f (Set.Icc a b)) (hg : BoundedVariationOn g (Set.Icc a b)) :
  ∃ L, Stieltjes.HasIntegral a b B f g L := by sorry

/-- Theorem A.2 of Montgomery Vaughan: if ∫_a^b f d g exists, then ∫_a^b g d f exists and
∫_a^b g d f = g(b) * f(b) - g(a) * f(a) - ∫_a^b f d g. -/
theorem integration_by_parts {f : ℝ → E} {g : ℝ → F} {L : G}
  (hL : Stieltjes.HasIntegral a b B f g L) :
  Stieltjes.HasIntegral a b (flip B) g f (B (f b) (g b) - B (f a) (g a) - L) := by sorry

/-- Theorem A.3 (a).  If g′ is continuous on [a, b], then
Var[a,b]g = ∫_a^b |g'(x)|\ dx
-/
theorem variation_of_derivative {g : ℝ → F} (hgdiff : ContDiffOn ℝ 1 g (Set.Icc a b)) :
  (eVariationOn g (Set.Icc a b)).toReal = ∫ x in a..b, ‖_root_.deriv g x‖  := by sorry

/-- Is there a better spelling for this? -/
def RiemannIntegrable (f : ℝ → E) : Prop := BoxIntegral.Integrable (interval a b)
  IntegrationParams.Riemann (fun x ↦ f (x ())) BoxAdditiveMap.volume

/-- Theorem A.3 (b).  If g′ is continuous on [a, b] and if in addition f is
Riemann integrable, then ∫_a^b f (x) dg(x) = ∫_a^b f (x)g′(x) dx. -/
theorem integral_of_derivative {f : ℝ → E} {g : ℝ → F}
  (hgdiff : ContDiffOn ℝ 1 g (Set.Icc a b))
  (hfint : RiemannIntegrable a b f) :
  HasIntegral a b B f g (∫ x in a..b, B (f x) (_root_.deriv g x)) := by sorry


/-- Theorem A.4. Suppose that g has bounded variation, and put g^∗(x) = Var[a,x]g. Then
∫_a^b f(x) dg(x) ≤ ∫_a^b | f (x)| dg∗(x).
provided that both integrals exist. -/
theorem integral_le_integral_of_variation {f : ℝ → E} {g : ℝ → F}
  (hgvar : BoundedVariationOn g (Set.Icc a b)) (L : G) (L' M : ℝ)
  (hfgint : HasIntegral a b B f g L)
  (hbound : ∀ e f, ‖B e f‖ ≤ M * ‖e‖ * ‖f‖)
  (hfabs_gstar : HasIntegral a b mul (fun x ↦ ‖f x‖)
    (fun x ↦ (eVariationOn g (Set.Icc a x)).toReal) L') :
  ‖L‖ ≤ M * L' := by sorry

/-- Relate sums ∑ f(n) with Stieltjes integrals ∫ f d ⌊x⌋ -/
theorem sum_le_integral_nat_floor (f : ℝ → E) :
  HasIntegral a b smul_right f (fun x ↦ Nat.floor x)
  (∑ n ∈ Finset.Ico (Nat.ceil a) (Nat.ceil b), f n) := by sorry

theorem sum_le_integral_floor (f : ℝ → E) :
  HasIntegral a b smul_right f (fun x ↦ Int.floor x)
  (∑ n ∈ Finset.Ico (Int.ceil a) (Int.ceil b), f n) := by sorry


end Stieltjes
