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
* `Stieltjes.Ioc a b`: the half-open interval `(a, b]` as a `Box (Fin 1)` (returning a
  dummy box when `a ≥ b`).
* `HasStieltjesIntegral a b B f g L`: the predicate asserting that `L : G` is the
  Riemann–Stieltjes integral of `f` against `g`, paired by the bilinear map `B`, over `(a, b]`.
* `StieltjesIntegrable a b B f g`: existence of the integral, i.e. some `L` with
  `HasStieltjesIntegral a b B f g L`.
* `stieltjesIntegral a b B f g`: the integral as a function, returning `0` on non-integrable
  inputs (analogous to `BoxIntegral.integral`, `MeasureTheory.integral`, etc.).
* `Stieltjes.RiemannIntegrable a b f`: a placeholder predicate for Riemann integrability of
  `f` on `(a, b]`.

## Notation

`∫⟨B⟩ x in a..b, f x d g` is notation for `stieltjesIntegral a b B (fun x ↦ f x) g`,
scoped to the `Stieltjes` namespace (`open scoped Stieltjes` to make it available). It
parallels Mathlib's `∫ x in a..b, f x ∂μ` notation for `intervalIntegral`, with the
bilinear pairing `B` carried explicitly in angle brackets since it has no canonical default.

## Main theorems

* `HasStieltjesIntegral.unique`: the value `L` of the Riemann–Stieltjes integral, when it
  exists, is unique.
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

## TODO

* Develop a higher-dimensional Stieltjes integral
* Develop a Stieltjes integral based around `Ico` intervals rather than `Ioc` intervals
* Change of variables formula wrt monotone substitutions
* Interpretation of `ofDiff` as a measure (assuming monotonicity)
* Interpretation of `ofDiff` as a signed measure (assuming bounded variation)
* `map` lemmas for `BoxIntegral` and `stieltjesIntegral` applying homomorphisms to the various
normed vector spaces etc.

## Tags

Stieltjes integral, Riemann–Stieltjes, bounded variation
-/

@[expose] public section

namespace BoxIntegral.BoxAdditiveMap

/-! ## `BoxIntegral.BoxAdditiveMap` extensions (to upstream)

The declarations in this section are *not* Stieltjes-specific. They fill in gaps in the
`BoxAdditiveMap` API in `Mathlib.Analysis.BoxIntegral.Partition.Additive`:

* the `@[ext]` lemma `ext_funLike`;
* the `_apply` simp lemmas `add_apply`, `smul_apply`, `neg_apply`, `sub_apply` (companions to
  the existing `@[simps -fullyApplied]` `Zero` instance);
* the `Neg` and `Sub` instances when `M : AddCommGroup`, alongside the existing
  `Zero` / `Add` / `SMul` / `AddCommMonoid` instances;
* the packaged `AddCommGroup (ι →ᵇᵃ[I₀] M)` instance (via `Function.Injective.addCommGroup`
  on `DFunLike.coe`).

Once these land upstream the local declarations here should be removed.
-/

@[ext]
theorem ext_funLike {ι M : Type*} [AddCommMonoid M] {I₀ : WithTop (Box ι)}
    {f g : ι →ᵇᵃ[I₀] M} (h : ∀ J, f J = g J) : f = g :=
  DFunLike.ext _ _ h

@[simp]
lemma add_apply {ι M : Type*} [AddCommMonoid M] {I₀ : WithTop (Box ι)}
    (f g : ι →ᵇᵃ[I₀] M) (J : Box ι) : (f + g) J = f J + g J := rfl

@[simp]
lemma smul_apply {ι M : Type*} [AddCommMonoid M] {I₀ : WithTop (Box ι)}
    {R : Type*} [Monoid R] [DistribMulAction R M]
    (c : R) (f : ι →ᵇᵃ[I₀] M) (J : Box ι) : (c • f) J = c • (f J) := rfl

variable {M : Type*} [AddCommGroup M]

instance {ι : Type*} {I₀ : WithTop (Box ι)} : Neg (ι →ᵇᵃ[I₀] M) :=
  ⟨fun f ↦
    ⟨-(f : Box ι → M), fun I hI π hπ ↦ by
      simp only [Pi.neg_apply, Finset.sum_neg_distrib, sum_partition_boxes _ hI hπ]⟩⟩

instance {ι : Type*} {I₀ : WithTop (Box ι)} : Sub (ι →ᵇᵃ[I₀] M) :=
  ⟨fun f g ↦
    ⟨(f : Box ι → M) - g, fun I hI π hπ ↦ by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_partition_boxes _ hI hπ]⟩⟩

instance {ι : Type*} {I₀ : WithTop (Box ι)} : AddCommGroup (ι →ᵇᵃ[I₀] M) :=
  Function.Injective.addCommGroup _ DFunLike.coe_injective
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp]
lemma neg_apply {ι : Type*} {I₀ : WithTop (Box ι)} (f : ι →ᵇᵃ[I₀] M) (J : Box ι) :
    (-f) J = -(f J) := rfl

@[simp]
lemma sub_apply {ι : Type*} {I₀ : WithTop (Box ι)} (f g : ι →ᵇᵃ[I₀] M) (J : Box ι) :
    (f - g) J = f J - g J := rfl

/-! ## The differential `ofDiff` of a function on `ℝ` -/

/-- The box-additive "differential" sending a function `g : ℝ → M` to the box-additive map on
`Box (Fin 1)` defined by `J ↦ g (J.upper 0) - g (J.lower 0)`, bundled as an
`AddMonoidHom`. -/
def ofDiff : (ℝ → M) →+ ((Fin 1) →ᵇᵃ M) where
  toFun g := ofMapSplitAdd
    (fun J : Box (Fin 1) ↦ g (J.upper 0) - g (J.lower 0)) ⊤
    (by
      intro I _ i x hx
      fin_cases i
      rw [Box.splitLower_def hx, Box.splitUpper_def hx]
      simp [Option.elim'])
  map_zero' := by
    ext J
    change (0 : ℝ → M) (J.upper 0) - (0 : ℝ → M) (J.lower 0) = (0 : (Fin 1) →ᵇᵃ M) J
    simp
  map_add' g h := by
    ext J
    change (g + h) (J.upper 0) - (g + h) (J.lower 0) =
      (g (J.upper 0) - g (J.lower 0)) + (h (J.upper 0) - h (J.lower 0))
    simp [Pi.add_apply]
    abel

@[simp]
lemma ofDiff_apply (g : ℝ → M) (J : Box (Fin 1)) :
    ofDiff g J = g (J.upper 0) - g (J.lower 0) := rfl

@[simp]
lemma ofDiff_smul {R : Type*} [Monoid R] [DistribMulAction R M]
    (c : R) (g : ℝ → M) : ofDiff (c • g) = c • ofDiff g := by
  ext J
  simp [smul_sub]

/-- `ofDiff` commutes with `BoxAdditiveMap.map` along an `AddMonoidHom`: postcomposing the
differential `ofDiff g` by `φ : M →+ N` is the same as taking the differential of `φ ∘ g`. -/
@[simp]
lemma map_ofDiff {N : Type*} [AddCommGroup N] (g : ℝ → M) (φ : M →+ N) :
    (ofDiff g).map φ = ofDiff (φ ∘ g) := by
  ext J
  simp [map_sub]

/-- The Riemann–Stieltjes differential of `ContinuousLinearMap.lsmul ℝ ℝ : ℝ → (E →L[ℝ] E)`
equals the Lebesgue volume box-additive map on `Box (Fin 1)`. Mathematically, this says that
the Stieltjes integral against the identity integrator (paired with scalar multiplication)
agrees with the ordinary Riemann integral on the real line. -/
lemma ofDiff_lsmul_eq_volume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ofDiff (fun x : ℝ ↦ (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) x) =
      (BoxAdditiveMap.volume : (Fin 1) →ᵇᵃ E →L[ℝ] E) := by
  sorry

end BoxIntegral.BoxAdditiveMap

namespace BoxIntegral

/-! ## Linearity of `BoxIntegral.HasIntegral` in the volume (to upstream)

The lemmas in this section extend `BoxIntegral.HasIntegral`'s integrand-side linearity
(`HasIntegral.add`, `.neg`, `.sub`, `.smul`, `hasIntegral_zero` in `BoxIntegral/Basic.lean`)
to the volume side. They belong upstream next to their integrand-side counterparts.
-/

variable {ι : Type*} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {I : Box ι} {l : IntegrationParams}

@[simp]
theorem integralSum_zero_vol (f : (ι → ℝ) → E) (π : TaggedPrepartition I) :
    integralSum f (0 : ι →ᵇᵃ E →L[ℝ] F) π = 0 := by
  simp [integralSum]

@[simp]
theorem integralSum_add_vol (f : (ι → ℝ) → E) (vol₁ vol₂ : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) :
    integralSum f (vol₁ + vol₂) π = integralSum f vol₁ π + integralSum f vol₂ π := by
  simp [integralSum, BoxAdditiveMap.add_apply, ContinuousLinearMap.add_apply,
    Finset.sum_add_distrib]

@[simp]
theorem integralSum_neg_vol (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) :
    integralSum f (-vol) π = -integralSum f vol π := by
  simp [integralSum, BoxAdditiveMap.neg_apply, ContinuousLinearMap.neg_apply,
    Finset.sum_neg_distrib]

@[simp]
theorem integralSum_sub_vol (f : (ι → ℝ) → E) (vol₁ vol₂ : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) :
    integralSum f (vol₁ - vol₂) π = integralSum f vol₁ π - integralSum f vol₂ π := by
  simp [integralSum, BoxAdditiveMap.sub_apply, ContinuousLinearMap.sub_apply,
    Finset.sum_sub_distrib]

@[simp]
theorem integralSum_smul_vol (c : ℝ) (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) :
    integralSum f (c • vol) π = c • integralSum f vol π := by
  simp [integralSum, BoxAdditiveMap.smul_apply, ContinuousLinearMap.smul_apply,
    Finset.smul_sum]

variable [Fintype ι] {f : (ι → ℝ) → E}

theorem hasIntegral_zero_vol : HasIntegral I l f (0 : ι →ᵇᵃ E →L[ℝ] F) 0 := by
  unfold HasIntegral
  rw [funext (integralSum_zero_vol f) (g := (0 : TaggedPrepartition I → F))]
  exact tendsto_const_nhds

theorem HasIntegral.add_vol {vol₁ vol₂ : ι →ᵇᵃ E →L[ℝ] F} {y₁ y₂ : F}
    (h₁ : HasIntegral I l f vol₁ y₁) (h₂ : HasIntegral I l f vol₂ y₂) :
    HasIntegral I l f (vol₁ + vol₂) (y₁ + y₂) := by
  unfold HasIntegral at h₁ h₂ ⊢
  rw [funext (integralSum_add_vol f vol₁ vol₂)]
  exact h₁.add h₂

theorem HasIntegral.neg_vol {vol : ι →ᵇᵃ E →L[ℝ] F} {y : F}
    (h : HasIntegral I l f vol y) : HasIntegral I l f (-vol) (-y) := by
  unfold HasIntegral at h ⊢
  rw [funext (integralSum_neg_vol f vol)]
  exact h.neg

theorem HasIntegral.sub_vol {vol₁ vol₂ : ι →ᵇᵃ E →L[ℝ] F} {y₁ y₂ : F}
    (h₁ : HasIntegral I l f vol₁ y₁) (h₂ : HasIntegral I l f vol₂ y₂) :
    HasIntegral I l f (vol₁ - vol₂) (y₁ - y₂) := by
  simpa only [sub_eq_add_neg] using h₁.add_vol h₂.neg_vol

theorem HasIntegral.smul_vol {vol : ι →ᵇᵃ E →L[ℝ] F} {y : F}
    (h : HasIntegral I l f vol y) (c : ℝ) :
    HasIntegral I l f (c • vol) (c • y) := by
  unfold HasIntegral at h ⊢
  rw [funext (integralSum_smul_vol c f vol)]
  exact (tendsto_const_nhds : Filter.Tendsto _ _ (nhds c)).smul h

end BoxIntegral

open BoxIntegral ContinuousLinearMap

namespace Stieltjes

/-! ## Definition of the Riemann–Stieltjes integral -/

/-- The interval `(a, b]` as a `Box (Fin 1)`. Returns the junk interval `(0, 1]` if `a ≥ b`. -/
noncomputable def Ioc (a b : ℝ) : Box (Fin 1) :=
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

/- Endpoint convention. The underlying box `Ioc a b` is the half-open interval `(a, b]`,
but most hypotheses and outputs below use `Set.Icc a b` rather than `Set.Ioc a b`. This is the
conservative choice and is needed in several places:
* `ContinuousOn` / `ContDiffOn` hypotheses rely on compactness of the domain (e.g. for uniform
  continuity), which fails on `Set.Ioc`.
* For a prepartition of `(a, b]` the leftmost sub-box has lower endpoint `a`, so `g a` appears
  in `BoxAdditiveMap.ofDiff g`. Bounded-variation hypotheses on `g` must therefore include `a`.
Some occurrences below may admit a half-open weakening; for now we keep `Set.Icc` everywhere
and flag this as a possible future refinement. -/

/-- The Stieltjes integral of a function `f : ℝ → E` and `g : ℝ → F` given a bilinear
map `B : E → F → G` and endpoints `a`, `b` takes values in `G`. -/
def HasStieltjesIntegral (f : ℝ → E) (g : ℝ → F) (L : G) : Prop :=
  HasIntegral (Ioc a b) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) (BoxAdditiveMap.ofDiff (fun x ↦ B.flip (g x))) L

/-- `StieltjesIntegrable a b B f g` asserts that the Riemann–Stieltjes integral of `f` against
`g` paired by `B` over `(a, b]` exists, i.e. some `L` satisfies `HasStieltjesIntegral a b B f g L`.
-/
def StieltjesIntegrable (f : ℝ → E) (g : ℝ → F) : Prop :=
  ∃ L, HasStieltjesIntegral a b B f g L

open Classical in
/-- The Riemann–Stieltjes integral of `f` against `g` paired by `B` over `(a, b]`. Returns the
junk value `0` if no such integral exists. -/
noncomputable def stieltjesIntegral (f : ℝ → E) (g : ℝ → F) : G :=
  if h : StieltjesIntegrable a b B f g then h.choose else 0

/-- Notation for the Riemann–Stieltjes integral. `∫⟨B⟩ x in a..b, f x d g` is
`stieltjesIntegral a b B (fun x ↦ f x) g`. The bilinear pairing `B` is written explicitly inside
angle brackets because there is no canonical choice (e.g. `ContinuousLinearMap.mul ℝ ℝ` for
scalar-valued `f` and `g`, `(ContinuousLinearMap.lsmul ℝ ℝ).flip` when `g` is real-valued, etc.).
The notation parallels Mathlib's `∫ x in a..b, f x ∂μ` for `intervalIntegral`. -/
@[inherit_doc stieltjesIntegral]
scoped notation3 "∫⟨"B"⟩ "(...)" in "a".."b", "r:60:(scoped f => f)" d "g:70 =>
  stieltjesIntegral a b B r g

/-! ## Basic API -/

/-- Uniqueness: the Riemann–Stieltjes integral, when it exists, is unique. -/
theorem HasStieltjesIntegral.unique {f : ℝ → E} {g : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral a b B f g L₁) (h₂ : HasStieltjesIntegral a b B f g L₂) :
    L₁ = L₂ :=
  HasIntegral.unique h₁ h₂

/-- The existence of a Riemann–Stieltjes integral implies `StieltjesIntegrable`. -/
theorem HasStieltjesIntegral.stieltjesIntegrable {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) : StieltjesIntegrable a b B f g :=
  ⟨L, h⟩

/-- A chosen witness extracted from `StieltjesIntegrable`. -/
protected theorem StieltjesIntegrable.hasStieltjesIntegral {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) :
    HasStieltjesIntegral a b B f g h.choose :=
  h.choose_spec

/-- If `HasStieltjesIntegral a b B f g L`, then `stieltjesIntegral a b B f g = L`. -/
theorem HasStieltjesIntegral.stieltjesIntegral_eq {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) : stieltjesIntegral a b B f g = L := by
  classical
  have hI : StieltjesIntegrable a b B f g := h.stieltjesIntegrable
  simp only [stieltjesIntegral, dif_pos hI]
  exact hI.choose_spec.unique a b B h

/-! ## Linearity -/

/-! ### In the integrand -/

theorem HasStieltjesIntegral.zero_left {g : ℝ → F} : HasStieltjesIntegral a b B 0 g 0 :=
  hasIntegral_zero

theorem HasStieltjesIntegral.add_left {f₁ f₂ : ℝ → E} {g : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral a b B f₁ g L₁) (h₂ : HasStieltjesIntegral a b B f₂ g L₂) :
    HasStieltjesIntegral a b B (f₁ + f₂) g (L₁ + L₂) :=
  HasIntegral.add h₁ h₂

theorem HasStieltjesIntegral.neg_left {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral a b B (-f) g (-L) :=
  HasIntegral.neg h

theorem HasStieltjesIntegral.sub_left {f₁ f₂ : ℝ → E} {g : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral a b B f₁ g L₁) (h₂ : HasStieltjesIntegral a b B f₂ g L₂) :
    HasStieltjesIntegral a b B (f₁ - f₂) g (L₁ - L₂) :=
  HasIntegral.sub h₁ h₂

theorem HasStieltjesIntegral.smul_left {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) (c : ℝ) :
    HasStieltjesIntegral a b B (c • f) g (c • L) :=
  HasIntegral.smul h c

/-! ### In the integrator -/

theorem HasStieltjesIntegral.zero_right {f : ℝ → E} : HasStieltjesIntegral a b B f 0 0 := by
  unfold HasStieltjesIntegral
  have h : (fun x : ℝ ↦ B.flip ((0 : ℝ → F) x)) = 0 := by ext; simp
  rw [h, map_zero]
  exact hasIntegral_zero_vol

theorem HasStieltjesIntegral.add_right {f : ℝ → E} {g₁ g₂ : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral a b B f g₁ L₁) (h₂ : HasStieltjesIntegral a b B f g₂ L₂) :
    HasStieltjesIntegral a b B f (g₁ + g₂) (L₁ + L₂) := by
  unfold HasStieltjesIntegral at h₁ h₂ ⊢
  have h : (fun x : ℝ ↦ B.flip ((g₁ + g₂) x)) =
      (fun x ↦ B.flip (g₁ x)) + (fun x ↦ B.flip (g₂ x)) := by ext; simp
  rw [h, map_add]
  exact h₁.add_vol h₂

theorem HasStieltjesIntegral.neg_right {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral a b B f (-g) (-L) := by
  unfold HasStieltjesIntegral at h ⊢
  have heq : (fun x : ℝ ↦ B.flip ((-g) x)) = -(fun x ↦ B.flip (g x)) := by ext; simp
  rw [heq, map_neg]
  exact h.neg_vol

theorem HasStieltjesIntegral.sub_right {f : ℝ → E} {g₁ g₂ : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral a b B f g₁ L₁) (h₂ : HasStieltjesIntegral a b B f g₂ L₂) :
    HasStieltjesIntegral a b B f (g₁ - g₂) (L₁ - L₂) := by
  unfold HasStieltjesIntegral at h₁ h₂ ⊢
  have h : (fun x : ℝ ↦ B.flip ((g₁ - g₂) x)) =
      (fun x ↦ B.flip (g₁ x)) - (fun x ↦ B.flip (g₂ x)) := by ext; simp
  rw [h, map_sub]
  exact h₁.sub_vol h₂

theorem HasStieltjesIntegral.smul_right {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) (c : ℝ) :
    HasStieltjesIntegral a b B f (c • g) (c • L) := by
  unfold HasStieltjesIntegral at h ⊢
  have heq : (fun x : ℝ ↦ B.flip ((c • g) x)) = c • (fun x ↦ B.flip (g x)) := by ext; simp
  rw [heq, BoxIntegral.BoxAdditiveMap.ofDiff_smul]
  exact h.smul_vol c

/-! ### Integrability in the integrand -/

theorem StieltjesIntegrable.zero_left {g : ℝ → F} : StieltjesIntegrable a b B 0 g :=
  (HasStieltjesIntegral.zero_left a b B).stieltjesIntegrable

theorem StieltjesIntegrable.add_left {f₁ f₂ : ℝ → E} {g : ℝ → F}
    (h₁ : StieltjesIntegrable a b B f₁ g) (h₂ : StieltjesIntegrable a b B f₂ g) :
    StieltjesIntegrable a b B (f₁ + f₂) g :=
  (h₁.hasStieltjesIntegral.add_left a b B h₂.hasStieltjesIntegral).stieltjesIntegrable

theorem StieltjesIntegrable.neg_left {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) : StieltjesIntegrable a b B (-f) g :=
  (h.hasStieltjesIntegral.neg_left a b B).stieltjesIntegrable

theorem StieltjesIntegrable.sub_left {f₁ f₂ : ℝ → E} {g : ℝ → F}
    (h₁ : StieltjesIntegrable a b B f₁ g) (h₂ : StieltjesIntegrable a b B f₂ g) :
    StieltjesIntegrable a b B (f₁ - f₂) g :=
  (h₁.hasStieltjesIntegral.sub_left a b B h₂.hasStieltjesIntegral).stieltjesIntegrable

theorem StieltjesIntegrable.smul_left {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) (c : ℝ) : StieltjesIntegrable a b B (c • f) g :=
  (h.hasStieltjesIntegral.smul_left a b B c).stieltjesIntegrable

/-! ### Integrability in the integrator -/

theorem StieltjesIntegrable.zero_right {f : ℝ → E} : StieltjesIntegrable a b B f 0 :=
  (HasStieltjesIntegral.zero_right a b B).stieltjesIntegrable

theorem StieltjesIntegrable.add_right {f : ℝ → E} {g₁ g₂ : ℝ → F}
    (h₁ : StieltjesIntegrable a b B f g₁) (h₂ : StieltjesIntegrable a b B f g₂) :
    StieltjesIntegrable a b B f (g₁ + g₂) :=
  (h₁.hasStieltjesIntegral.add_right a b B h₂.hasStieltjesIntegral).stieltjesIntegrable

theorem StieltjesIntegrable.neg_right {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) : StieltjesIntegrable a b B f (-g) :=
  (h.hasStieltjesIntegral.neg_right a b B).stieltjesIntegrable

theorem StieltjesIntegrable.sub_right {f : ℝ → E} {g₁ g₂ : ℝ → F}
    (h₁ : StieltjesIntegrable a b B f g₁) (h₂ : StieltjesIntegrable a b B f g₂) :
    StieltjesIntegrable a b B f (g₁ - g₂) :=
  (h₁.hasStieltjesIntegral.sub_right a b B h₂.hasStieltjesIntegral).stieltjesIntegrable

theorem StieltjesIntegrable.smul_right {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) (c : ℝ) : StieltjesIntegrable a b B f (c • g) :=
  (h.hasStieltjesIntegral.smul_right a b B c).stieltjesIntegrable

/-! ### Integral linearity in the integrand -/

theorem stieltjesIntegral_zero_left {g : ℝ → F} : stieltjesIntegral a b B 0 g = 0 :=
  (HasStieltjesIntegral.zero_left a b B).stieltjesIntegral_eq

theorem stieltjesIntegral_add_left {f₁ f₂ : ℝ → E} {g : ℝ → F}
    (h₁ : StieltjesIntegrable a b B f₁ g) (h₂ : StieltjesIntegrable a b B f₂ g) :
    stieltjesIntegral a b B (f₁ + f₂) g
      = stieltjesIntegral a b B f₁ g + stieltjesIntegral a b B f₂ g := by
  rw [(h₁.hasStieltjesIntegral.add_left a b B h₂.hasStieltjesIntegral).stieltjesIntegral_eq,
    h₁.hasStieltjesIntegral.stieltjesIntegral_eq,
    h₂.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem stieltjesIntegral_neg_left {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) :
    stieltjesIntegral a b B (-f) g = -stieltjesIntegral a b B f g := by
  rw [(h.hasStieltjesIntegral.neg_left a b B).stieltjesIntegral_eq,
    h.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem stieltjesIntegral_sub_left {f₁ f₂ : ℝ → E} {g : ℝ → F}
    (h₁ : StieltjesIntegrable a b B f₁ g) (h₂ : StieltjesIntegrable a b B f₂ g) :
    stieltjesIntegral a b B (f₁ - f₂) g
      = stieltjesIntegral a b B f₁ g - stieltjesIntegral a b B f₂ g := by
  rw [(h₁.hasStieltjesIntegral.sub_left a b B h₂.hasStieltjesIntegral).stieltjesIntegral_eq,
    h₁.hasStieltjesIntegral.stieltjesIntegral_eq,
    h₂.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem stieltjesIntegral_smul_left {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) (c : ℝ) :
    stieltjesIntegral a b B (c • f) g = c • stieltjesIntegral a b B f g := by
  rw [(h.hasStieltjesIntegral.smul_left a b B c).stieltjesIntegral_eq,
    h.hasStieltjesIntegral.stieltjesIntegral_eq]

/-! ### Integral linearity in the integrator -/

theorem stieltjesIntegral_zero_right {f : ℝ → E} : stieltjesIntegral a b B f 0 = 0 :=
  (HasStieltjesIntegral.zero_right a b B).stieltjesIntegral_eq

theorem stieltjesIntegral_add_right {f : ℝ → E} {g₁ g₂ : ℝ → F}
    (h₁ : StieltjesIntegrable a b B f g₁) (h₂ : StieltjesIntegrable a b B f g₂) :
    stieltjesIntegral a b B f (g₁ + g₂)
      = stieltjesIntegral a b B f g₁ + stieltjesIntegral a b B f g₂ := by
  rw [(h₁.hasStieltjesIntegral.add_right a b B h₂.hasStieltjesIntegral).stieltjesIntegral_eq,
    h₁.hasStieltjesIntegral.stieltjesIntegral_eq,
    h₂.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem stieltjesIntegral_neg_right {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) :
    stieltjesIntegral a b B f (-g) = -stieltjesIntegral a b B f g := by
  rw [(h.hasStieltjesIntegral.neg_right a b B).stieltjesIntegral_eq,
    h.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem stieltjesIntegral_sub_right {f : ℝ → E} {g₁ g₂ : ℝ → F}
    (h₁ : StieltjesIntegrable a b B f g₁) (h₂ : StieltjesIntegrable a b B f g₂) :
    stieltjesIntegral a b B f (g₁ - g₂)
      = stieltjesIntegral a b B f g₁ - stieltjesIntegral a b B f g₂ := by
  rw [(h₁.hasStieltjesIntegral.sub_right a b B h₂.hasStieltjesIntegral).stieltjesIntegral_eq,
    h₁.hasStieltjesIntegral.stieltjesIntegral_eq,
    h₂.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem stieltjesIntegral_smul_right {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) (c : ℝ) :
    stieltjesIntegral a b B f (c • g) = c • stieltjesIntegral a b B f g := by
  rw [(h.hasStieltjesIntegral.smul_right a b B c).stieltjesIntegral_eq,
    h.hasStieltjesIntegral.stieltjesIntegral_eq]

/-! ## Auxiliary lemmas -/

/-- For any valid box partition of (a, b], the sum of the norm of the
differential `ofDiff g` is bounded by the total variation of g on the interval. -/
lemma sum_norm_ofDiff_le_norm_mul_eVariationOn (g : ℝ → F)
    (hg : BoundedVariationOn g (Set.Icc a b))
    (π : Prepartition (Ioc a b)) :
    ∑ J ∈ π.boxes, ‖(BoxAdditiveMap.ofDiff (fun x ↦ B.flip (g x))) J‖ ≤
      ‖B‖ * (eVariationOn g (Set.Icc a b)).toReal := by
  sorry

/-- Prove that the Riemann-Stieltjes integrand is Box-Integrable.
Use the Cauchy criterion and the uniform continuity of f on [a, b].
We separate integrability for more modular API. -/
lemma integrable_of_continuousOn_of_boundedVariationOn
    (f : ℝ → E) (g : ℝ → F)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : BoundedVariationOn g (Set.Icc a b)) :
    Integrable (Ioc a b) IntegrationParams.Riemann
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
theorem variation_of_derivative {g : ℝ → F} (hg : ContDiffOn ℝ 1 g (Set.Icc a b)) :
    (eVariationOn g (Set.Icc a b)).toReal = ∫ x in a..b, ‖deriv g x‖ := by sorry

/-- Placeholder abbreviation; there may be a better spelling for this. -/
abbrev RiemannIntegrable (f : ℝ → E) : Prop :=
  Integrable (Ioc a b) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) BoxAdditiveMap.volume

/-- Theorem A.3 (b).  If g′ is continuous on [a, b] and if in addition f is
Riemann integrable, then ∫ₐᵇ f(x) dg(x) = ∫ₐᵇ f(x) g′(x) dx. -/
theorem integral_of_derivative {f : ℝ → E} {g : ℝ → F}
    (hg : ContDiffOn ℝ 1 g (Set.Icc a b))
    (hf : RiemannIntegrable a b f) :
    HasStieltjesIntegral a b B f g (∫ x in a..b, B (f x) (deriv g x)) := by sorry

/-- Theorem A.4. Suppose that g has bounded variation, and put g∗(x) = Varₐˣ g. Then
‖∫ₐᵇ f(x) dg(x)‖ ≤ ∫ₐᵇ ‖f(x)‖ dg∗(x),
provided that both integrals exist. -/
theorem integral_le_integral_of_variation {f : ℝ → E} {g : ℝ → F} {L : G} {L' : ℝ}
    (hg : BoundedVariationOn g (Set.Icc a b))
    (hfg : HasStieltjesIntegral a b B f g L)
    (hfabs_gstar : HasStieltjesIntegral a b (mul ℝ ℝ) (fun x ↦ ‖f x‖)
      (fun x ↦ (eVariationOn g (Set.Icc a x)).toReal) L') :
    ‖L‖ ≤ ‖B‖ * L' := by sorry

/-! ### Connection to standard integrals -/

/-- When the integrator is the identity, the Stieltjes integral with the scalar-multiplication
pairing `(lsmul ℝ ℝ).flip` reduces to the ordinary `BoxIntegral.HasIntegral` against the
Lebesgue volume on `(a, b]`. -/
theorem hasStieltjesIntegral_id_iff_hasIntegral_volume (f : ℝ → E) (L : E) :
    HasStieltjesIntegral a b (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip f id L ↔
      HasIntegral (Ioc a b) IntegrationParams.Riemann (fun x ↦ f (x 0))
        BoxAdditiveMap.volume L := by sorry

/-- Function-level form of Theorem A.3(b) (`integral_of_derivative`): when `g` is `C¹` on
`[a, b]` and `f` is Riemann integrable, the Stieltjes integral of `f` against `g` equals the
Riemann integral of `B (f x) (g' x)`. -/
theorem stieltjesIntegral_eq_intervalIntegral_of_contDiffOn {f : ℝ → E} {g : ℝ → F}
    (hg : ContDiffOn ℝ 1 g (Set.Icc a b)) (hf : RiemannIntegrable a b f) :
    stieltjesIntegral a b B f g = ∫ x in a..b, B (f x) (deriv g x) :=
  (integral_of_derivative a b B hg hf).stieltjesIntegral_eq

/-! ### Sums as Stieltjes integrals -/

/-- Relate sums ∑ f(n) with Stieltjes integrals ∫ f d ⌊x⌋ -/
theorem sum_eq_integral_nat_floor (f : ℝ → E) :
    HasStieltjesIntegral a b (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip f
      (fun x ↦ ⌊x⌋₊)
      (∑ n ∈ Finset.Ico ⌈a⌉₊ ⌈b⌉₊, f n) := by sorry

theorem sum_eq_integral_int_floor (f : ℝ → E) :
    HasStieltjesIntegral a b (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip f
      (fun x ↦ ⌊x⌋)
      (∑ n ∈ Finset.Ico ⌈a⌉ ⌈b⌉, f n) := by sorry

/-- Sum of pairings `B (f n) (g n)` over natural `n ∈ (⌊a⌋, ⌊b⌋]`, expressed as a Stieltjes
integral of `f` against the right-continuous summatory `x ↦ ∑ n ≤ x, g n`. -/
theorem sum_eq_integral_natSummatory_le (f : ℝ → E) (g : ℕ → F) :
    HasStieltjesIntegral a b B f
      (fun x ↦ ∑ n ∈ Finset.Iic ⌊x⌋₊, g n)
      (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, B (f n) (g n)) := by sorry

/-- Sum of pairings `B (f n) (g n)` over natural `n ∈ [⌈a⌉, ⌈b⌉)`, expressed as a Stieltjes
integral of `f` against the left-continuous summatory `x ↦ ∑ n < x, g n`. -/
theorem sum_eq_integral_natSummatory_lt (f : ℝ → E) (g : ℕ → F) :
    HasStieltjesIntegral a b B f
      (fun x ↦ ∑ n ∈ Finset.Iio ⌈x⌉₊, g n)
      (∑ n ∈ Finset.Ico ⌈a⌉₊ ⌈b⌉₊, B (f n) (g n)) := by sorry

end Stieltjes
