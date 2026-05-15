/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic
public import Mathlib.Analysis.BoxIntegral.Partition.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Riemann–Stieltjes integral

In this file we define the (one-dimensional) Riemann–Stieltjes integral of a function
`f : ℝ → E` against an integrator `g : ℝ → F`, paired by a continuous bilinear map
`B : E →L[ℝ] F →L[ℝ] G`. The integral is realized as a `BoxIntegral.HasIntegral` over the
half-open interval `(a, b]`, viewed as a `Box (Fin 1)`, with respect to the box-additive
"differential" associated to `g`.

The development follows the treatment of Riemann–Stieltjes integration in
Montgomery–Vaughan, *Multiplicative Number Theory I: Classical Theory*, Appendix A.

Currently we are using `Stieltjes` to refer to the one-dimensional Riemann–Stieltjes integral; the
name may be subject to change if further variants of Stieltjes integration are introduced.

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
* Stieltjes integral for negative or trivial intervals
* Example: decay of Fourier transforms of total variation functions

## Tags

Stieltjes integral, Riemann–Stieltjes, bounded variation
-/

@[expose] public section

/-! ## Intervals -/

namespace Stieltjes

open BoxIntegral

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

@[simp]
lemma Ioc.upper {a b : ℝ} (h : a < b) (i : Fin 1) : (Ioc a b).upper i = b := by
  simp [Ioc, h]

@[simp]
lemma Ioc.lower {a b : ℝ} (h : a < b) (i : Fin 1) : (Ioc a b).lower i = a := by
  simp [Ioc, h]

lemma Box.eq_Ioc (J : Box (Fin 1)) : J = Ioc (J.lower 0) (J.upper 0) := by
  ext
  simp [Ioc, Box.mem_def]

@[simp]
lemma mem_Ioc {a b : ℝ} (hab : a < b) (x : Fin 1 → ℝ) : x ∈ Ioc a b ↔ a < x 0 ∧ x 0 ≤ b := by
  simp [Box.mem_def, Ioc.upper hab, Ioc.lower hab]

end Stieltjes



namespace BoxIntegral.BoundaryPoints

open BoxIntegral Stieltjes

noncomputable def toPartition {N : ℕ} {a b : ℝ}
    (x : Fin (N + 1) → ℝ) (hx : StrictMono x)
    (ha : (x 0) = a) (hb : x (Fin.last N) = b) :
    Prepartition (Ioc a b) where
  boxes := by
    classical
    exact (Finset.univ : Finset (Fin N)).image fun i ↦ Ioc (x i.castSucc) (x i.succ)
  le_of_mem' := by sorry
  pairwiseDisjoint := by sorry

theorem toPartition.IsPartition {N : ℕ} {a b : ℝ} (hab : a < b)
    (x : Fin (N + 1) → ℝ) (hx : StrictMono x)
    (ha : (x 0) = a) (hb : x (Fin.last N) = b):
    (toPartition x hx ha hb).IsPartition := by
  sorry

theorem fromPartition
    {a b : ℝ} (hab : a < b)
    (π : Prepartition (Ioc a b))
    (hπ : π.IsPartition):
    letI N := Finset.card π.boxes
    ∃ (x : Fin (N + 1) → ℝ) (hx : StrictMono x) (ha : (x 0) = a) (hb : x (Fin.last N) = b),
     π = toPartition x hx ha hb := by
  sorry

end BoxIntegral.BoundaryPoints

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

open Stieltjes

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

/-- The Riemann–Stieltjes differential of a constant function vanishes. -/
@[simp]
lemma ofDiff_const (c : M) : ofDiff (fun _ : ℝ ↦ c) = 0 := by
  ext J
  simp

@[simp]
lemma ofDiff_Ioc (g : ℝ → M) {a b : ℝ} (h : a < b) :
    ofDiff g (Ioc a b) = g b - g a := by
  simp [h]

/-- `ofDiff g` vanishes iff `g` is constant. -/
lemma ofDiff_eq_zero_iff {g : ℝ → M} : ofDiff g = 0 ↔ ∀ x y, g x = g y := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ ?_⟩
  · have key {a b : ℝ} (hab : a < b) : g a = g b := by
      replace h := DFunLike.congr_fun h (Ioc a b)
      simp [hab] at h
      grind
    rcases lt_trichotomy x y with hlt | rfl | hgt
    · exact key hlt
    · rfl
    · exact (key hgt).symm
  · ext J
    simp [ofDiff_apply, h (J.upper 0) (J.lower 0), sub_self]

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

/-! ### Intertwining `HasIntegral` by continuous linear maps -/

/-- If `φ : E →L[ℝ] E'` acts on integrands and `ψ : F →L[ℝ] F'` acts on integrated values, and
`(vol, vol')` are intertwined in the sense that the diagram
```
        vol J
   E ─────────→ F
   │            │
   φ            ψ
   ↓            ↓
   E' ────────→ F'
        vol' J
```
commutes for every box `J` — i.e. `ψ (vol J e) = vol' J (φ e)` for all `J, e` — then `HasIntegral`
transports along `(φ, ψ)`: if `f` has integral `y` under `vol`, then `φ ∘ f` has integral `ψ y`
under `vol'`. -/
theorem HasIntegral.map {E' F' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {vol : ι →ᵇᵃ E →L[ℝ] F} {vol' : ι →ᵇᵃ E' →L[ℝ] F'} {y : F}
    (φ : E →L[ℝ] E') (ψ : F →L[ℝ] F')
    (hvol : ∀ (J : Box ι) (e : E), ψ (vol J e) = vol' J (φ e))
    (h : HasIntegral I l f vol y) :
    HasIntegral I l (fun x ↦ φ (f x)) vol' (ψ y) := by
  have hSum : ∀ π : TaggedPrepartition I,
      integralSum (fun x ↦ φ (f x)) vol' π = ψ (integralSum f vol π) := fun π ↦ by
    simp only [integralSum, map_sum]
    exact Finset.sum_congr rfl fun J _ ↦ (hvol J (f (π.tag J))).symm
  unfold HasIntegral at h ⊢
  exact ((ψ.continuous.tendsto y).comp h).congr fun π ↦ (hSum π).symm

/-- Existence version of `HasIntegral.map`: integrability is preserved when transporting
along an intertwined pair of continuous linear maps. -/
theorem Integrable.map {E' F' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {vol : ι →ᵇᵃ E →L[ℝ] F} {vol' : ι →ᵇᵃ E' →L[ℝ] F'}
    (φ : E →L[ℝ] E') (ψ : F →L[ℝ] F')
    (hvol : ∀ (J : Box ι) (e : E), ψ (vol J e) = vol' J (φ e))
    (h : Integrable I l f vol) : Integrable I l (fun x ↦ φ (f x)) vol' :=
  (h.hasIntegral.map φ ψ hvol).integrable

/-- Function-level version of `HasIntegral.map`: applying `ψ` to the integral of `f` against
`vol` equals the integral of `φ ∘ f` against `vol'`, when `f` is integrable and the volumes
are intertwined. -/
theorem integral_map {E' F' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {vol : ι →ᵇᵃ E →L[ℝ] F} {vol' : ι →ᵇᵃ E' →L[ℝ] F'}
    (φ : E →L[ℝ] E') (ψ : F →L[ℝ] F')
    (hvol : ∀ (J : Box ι) (e : E), ψ (vol J e) = vol' J (φ e))
    (h : Integrable I l f vol) :
    integral I l (fun x ↦ φ (f x)) vol' = ψ (integral I l f vol) := by
  rw [(h.hasIntegral.map φ ψ hvol).integral_eq, h.hasIntegral.integral_eq]

/-! ### Additivity along a partition -/

/-- Box-integral additivity along a partition: if `π : Prepartition I` is a partition of `I`,
`f` is integrable on `I`, and `f` has integral `y J` over each sub-box `J ∈ π.boxes` (with the
same volume `vol` and integration parameters `l`), then `f` has integral `∑ J ∈ π.boxes, y J`
over `I`.

This is the dual of `HasIntegral.sum`: that lemma sums *different integrands* on the same box;
this one sums the *same integrand* on the pieces of a partition. The two-box specialization
(via `Prepartition.split I i x`) underwrites adjacent-interval splitting for Stieltjes and
interval integrals.

The integrability assumption on `I` is the price we pay for not gluing per-box gauges; in
practice it is supplied by separate continuity / bounded-variation hypotheses on the caller's
side. A future strengthening would derive `Integrable I` from `∀ J ∈ π.boxes, Integrable J` via
gauge gluing. -/
theorem HasIntegral.sum_of_isPartition [CompleteSpace F] {π : Prepartition I} (hπ : π.IsPartition)
    {vol : ι →ᵇᵃ E →L[ℝ] F} (hI : Integrable I l f vol) {y : Box ι → F}
    (h : ∀ J ∈ π.boxes, HasIntegral J l f vol (y J)) :
    HasIntegral I l f vol (∑ J ∈ π.boxes, y J) := by
  have hsum : (∑ J ∈ π.boxes, y J) = integral I l f vol := by
    have hba := hI.toBoxAdditive.sum_partition_boxes le_rfl hπ
    simp only [Integrable.toBoxAdditive_apply] at hba
    rw [← hba]
    exact Finset.sum_congr rfl fun J hJ ↦ ((h J hJ).integral_eq).symm
  rw [hsum]
  exact hI.hasIntegral

/-- Two-box specialization of `HasIntegral.sum_of_isPartition`. If a box `I` splits at
coordinate `i` and value `x` into sub-boxes `J_lo` (lower) and `J_hi` (upper), both non-bot,
`f` is integrable on `I`, and `f` has integral `y_lo` on `J_lo` and `y_hi` on `J_hi`, then `f`
has integral `y_lo + y_hi` on `I`. -/
theorem HasIntegral.split [CompleteSpace F] (i : ι) (x : ℝ) {J_lo J_hi : Box ι}
    (h_lower : I.splitLower i x = ↑J_lo) (h_upper : I.splitUpper i x = ↑J_hi)
    {vol : ι →ᵇᵃ E →L[ℝ] F} (hI : Integrable I l f vol) {y_lo y_hi : F}
    (h₁ : HasIntegral J_lo l f vol y_lo) (h₂ : HasIntegral J_hi l f vol y_hi) :
    HasIntegral I l f vol (y_lo + y_hi) := by
  classical
  have : (I.splitLower i x  : Set (ι → ℝ)) ∩ (I.splitUpper i x  : Set (ι → ℝ)) = ∅ := by
    ext p; simp; grind
  have hne : J_hi ≠ J_lo := by
    intro heq
    simp [h_lower, h_upper, heq] at this
  let y : Box ι → F := fun J ↦ if J = J_lo then y_lo else y_hi
  have hy_lo : y J_lo = y_lo := if_pos rfl
  have hy_hi : y J_hi = y_hi := if_neg hne
  rw [← hy_lo, ← hy_hi]
  have h_sum_eq : (∑ J ∈ (Prepartition.split I i x).boxes, y J) = y J_lo + y J_hi := by
    rw [Prepartition.sum_split_boxes, h_lower, h_upper]
    rfl
  rw [← h_sum_eq]
  apply HasIntegral.sum_of_isPartition (Prepartition.isPartitionSplit I i x) hI
  intro J hJ
  rcases Prepartition.mem_split_iff.mp hJ with hJ | hJ
  · rw [WithBot.coe_injective (hJ.trans h_lower), hy_lo]; exact h₁
  · rw [WithBot.coe_injective (hJ.trans h_upper), hy_hi]; exact h₂

end BoxIntegral

open BoxIntegral ContinuousLinearMap

namespace Stieltjes

/-! ## Definition of the Riemann–Stieltjes integral -/

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
map `B : E → F → G` and endpoints `a`, `b` takes values in `G`.  Initially defined under the
implicit assumption that `a < b`, then
extended by antisymmetry to general `a`, `b`. -/
def HasStieltjesIntegral' (f : ℝ → E) (g : ℝ → F) (L : G) : Prop :=
  HasIntegral (Ioc a b) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) (BoxAdditiveMap.ofDiff (fun x ↦ B.flip (g x))) L

def HasStieltjesIntegral (f : ℝ → E) (g : ℝ → F) (L : G) : Prop :=
  if a = b then L = 0 else
    if a < b then HasStieltjesIntegral' a b B f g L else
      HasStieltjesIntegral' b a B f g (-L)

@[simp]
lemma HasStieltjesIntegral.of_eq_iff_zero (f : ℝ → E) (g : ℝ → F) (L : G) :
    HasStieltjesIntegral a a B f g L ↔ L = 0 := by
  simp [HasStieltjesIntegral]

@[simp]
lemma HasStieltjesIntegral.of_lt (f : ℝ → E) (g : ℝ → F) (L : G) (hab : a < b) :
    HasStieltjesIntegral a b B f g L ↔ HasStieltjesIntegral' a b B f g L := by
  simp [HasStieltjesIntegral, hab, hab.ne]

@[simp]
lemma HasStieltjesIntegral.of_gt (f : ℝ → E) (g : ℝ → F) (L : G) (hba : b < a) :
    HasStieltjesIntegral a b B f g L ↔ HasStieltjesIntegral' b a B f g (-L) := by
  simp [HasStieltjesIntegral, Std.not_gt_of_lt hba, hba.ne.symm]

lemma HasStieltjesIntegral.symm_iff (f : ℝ → E) (g : ℝ → F) (L : G) :
    HasStieltjesIntegral a b B f g L ↔ HasStieltjesIntegral b a B f g (-L) := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [HasStieltjesIntegral, h, Std.not_gt_of_lt h, h.ne, h.ne.symm]
  · simp [HasStieltjesIntegral]
  simp [HasStieltjesIntegral, h, Std.not_gt_of_lt h, h.ne, h.ne.symm]

@[symm]
lemma HasStieltjesIntegral.symm {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral b a B f g (-L) := by
  rwa [← symm_iff]

/-- `StieltjesIntegrable a b B f g` asserts that the Riemann–Stieltjes integral of `f` against
`g` paired by `B` over `(a, b]` exists, i.e. some `L` satisfies `HasStieltjesIntegral a b B f g L`.
-/
private def StieltjesIntegrable' (f : ℝ → E) (g : ℝ → F) : Prop :=
  ∃ L, HasStieltjesIntegral' a b B f g L

def StieltjesIntegrable (f : ℝ → E) (g : ℝ → F) : Prop :=
  ∃ L, HasStieltjesIntegral a b B f g L

@[simp]
lemma StieltjesIntegrable.of_eq (f : ℝ → E) (g : ℝ → F) :
  StieltjesIntegrable a a B f g := by
  simp [StieltjesIntegrable, HasStieltjesIntegral]

private lemma StieltjesIntegrable.of_lt (f : ℝ → E) (g : ℝ → F) (hab : a < b) :
    StieltjesIntegrable a b B f g ↔ StieltjesIntegrable' a b B f g := by
  simp [StieltjesIntegrable, StieltjesIntegrable', hab]

lemma StieltjesIntegrable.symm_iff (f : ℝ → E) (g : ℝ → F) :
    StieltjesIntegrable a b B f g ↔ StieltjesIntegrable b a B f g := by
  unfold StieltjesIntegrable
  constructor <;> rintro ⟨ L, h ⟩ <;> use -L <;> apply h.symm

@[symm]
lemma StieltjesIntegrable.symm {f : ℝ → E} {g : ℝ → F} (h : StieltjesIntegrable a b B f g) :
    StieltjesIntegrable b a B f g := by
  rwa [← symm_iff]

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
scoped notation3 "∫⟨"B"⟩ "(...)" in "a".."b", "r:60:(scoped f => f)" d "g:70 =>
  stieltjesIntegral a b B r g

/-! ## Basic API -/

/-- Uniqueness: the Riemann–Stieltjes integral, when it exists, is unique. -/
theorem HasStieltjesIntegral.unique {f : ℝ → E} {g : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral a b B f g L₁) (h₂ : HasStieltjesIntegral a b B f g L₂) :
    L₁ = L₂ := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [h, of_lt] at h₁ h₂
    exact HasIntegral.unique h₁ h₂
  · simp_all
  symm at h₁ h₂
  simp only [h, of_lt] at h₁ h₂
  have := HasIntegral.unique h₁ h₂
  grind

/-- The existence of a Riemann–Stieltjes integral implies `StieltjesIntegrable`. -/
theorem HasStieltjesIntegral.stieltjesIntegrable {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) : StieltjesIntegrable a b B f g :=
  ⟨L, h⟩

/-- A chosen witness extracted from `StieltjesIntegrable`. -/
theorem StieltjesIntegrable.hasStieltjesIntegral {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) :
    HasStieltjesIntegral a b B f g (∫⟨B⟩ x in a..b, f x d g) := by
  simp [stieltjesIntegral, h, h.choose_spec]

/-- If `HasStieltjesIntegral a b B f g L`, then `stieltjesIntegral a b B f g = L`. -/
theorem HasStieltjesIntegral.stieltjesIntegral_eq {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) : ∫⟨B⟩ x in a..b, f x d g = L := by
  classical
  have hI : StieltjesIntegrable a b B f g := h.stieltjesIntegrable
  simp only [stieltjesIntegral, dif_pos hI]
  exact hI.choose_spec.unique a b B h

theorem StieltjesIntegrable.hasStieltjesIntegral_iff {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) (L : G) :
   HasStieltjesIntegral a b B f g L ↔ ∫⟨B⟩ x in a..b, f x d g = L
     := by
  grind [hasStieltjesIntegral, HasStieltjesIntegral.unique]

@[simp]
theorem stieltjesIntegral.of_eq (f : ℝ → E) (g : ℝ → F) :
    ∫⟨B⟩ x in a..a, f x d g = 0 := by
  simp only [stieltjesIntegral, StieltjesIntegrable.of_eq, ↓reduceDIte]
  rw [← HasStieltjesIntegral.of_eq_iff_zero a B f g]
  apply Exists.choose_spec

theorem stieltjesIntegral.of_symm (f : ℝ → E) (g : ℝ → F) :
    ∫⟨B⟩ x in b..a, f x d g = -∫⟨B⟩ x in a..b, f x d g := by
  by_cases h_integ : StieltjesIntegrable a b B f g
  · have h_integ_symm : StieltjesIntegrable b a B f g := h_integ.symm
    exact (h_integ.hasStieltjesIntegral.symm.unique _ _ _ h_integ_symm.hasStieltjesIntegral).symm
  have h_integ_symm : ¬ StieltjesIntegrable b a B f g := by contrapose! h_integ; exact h_integ.symm
  simp [stieltjesIntegral, h_integ, h_integ_symm]

/-! ## Linearity -/

/-! ### In the integrand -/

private theorem HasStieltjesIntegral'.zero_left {g : ℝ → F} : HasStieltjesIntegral' a b B 0 g 0 :=
  hasIntegral_zero

theorem HasStieltjesIntegral.zero_left {g : ℝ → F} : HasStieltjesIntegral a b B 0 g 0 := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [of_lt, h, HasStieltjesIntegral'.zero_left]
  · simp
  rw [symm_iff]
  simp only [neg_zero, h, of_lt, HasStieltjesIntegral'.zero_left]

private theorem HasStieltjesIntegral'.add_left {f₁ f₂ : ℝ → E} {g : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral' a b B f₁ g L₁) (h₂ : HasStieltjesIntegral' a b B f₂ g L₂) :
    HasStieltjesIntegral' a b B (f₁ + f₂) g (L₁ + L₂) :=
  HasIntegral.add h₁ h₂

theorem HasStieltjesIntegral.add_left {f₁ f₂ : ℝ → E} {g : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral a b B f₁ g L₁) (h₂ : HasStieltjesIntegral a b B f₂ g L₂) :
    HasStieltjesIntegral a b B (f₁ + f₂) g (L₁ + L₂) := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [of_lt, h] at h₁ h₂ ⊢
    exact h₁.add_left _ _ _ h₂
  · simp_all
  rw [symm_iff] at h₁ h₂ ⊢
  simp only [h, of_lt, neg_add] at h₁ h₂ ⊢
  exact h₁.add_left _ _ _ h₂

private theorem HasStieltjesIntegral'.neg_left {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral' a b B f g L) :
    HasStieltjesIntegral' a b B (-f) g (-L) :=
  HasIntegral.neg h

theorem HasStieltjesIntegral.neg_left {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral a b B (-f) g (-L) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · simp only [of_lt, hab] at h ⊢
    apply h.neg_left
  · simp_all
  rw [symm_iff] at h ⊢
  simp only [hab, of_lt] at h ⊢
  apply h.neg_left

private theorem HasStieltjesIntegral'.sub_left {f₁ f₂ : ℝ → E} {g : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral' a b B f₁ g L₁) (h₂ : HasStieltjesIntegral' a b B f₂ g L₂) :
    HasStieltjesIntegral' a b B (f₁ - f₂) g (L₁ - L₂) :=
  HasIntegral.sub h₁ h₂

theorem HasStieltjesIntegral.sub_left {f₁ f₂ : ℝ → E} {g : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral a b B f₁ g L₁) (h₂ : HasStieltjesIntegral a b B f₂ g L₂) :
    HasStieltjesIntegral a b B (f₁ - f₂) g (L₁ - L₂) := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [of_lt, h] at h₁ h₂ ⊢
    exact h₁.sub_left _ _ _ h₂
  · simp_all
  rw [symm_iff] at h₁ h₂ ⊢
  simp only [h, of_lt] at h₁ h₂ ⊢
  convert h₁.sub_left _ _ _ h₂ using 1
  abel

private theorem HasStieltjesIntegral'.smul_left {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral' a b B f g L) (c : ℝ) :
    HasStieltjesIntegral' a b B (c • f) g (c • L) :=
  HasIntegral.smul h c

theorem HasStieltjesIntegral.smul_left {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) (c : ℝ) :
    HasStieltjesIntegral a b B (c • f) g (c • L) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · simp only [of_lt, hab] at h ⊢
    apply h.smul_left
  · simp_all
  rw [symm_iff] at h ⊢
  simp only [hab, of_lt] at h ⊢
  convert h.smul_left _ _ _ _ using 1
  norm_num

/-! ### In the integrator -/

private theorem HasStieltjesIntegral'.const_right {f : ℝ → E} (c : F) :
    HasStieltjesIntegral' a b B f (fun _ ↦ c) 0 := by
  simp only [HasStieltjesIntegral', Fin.isValue, BoxAdditiveMap.ofDiff_const, hasIntegral_zero_vol]

theorem HasStieltjesIntegral.const_right {f : ℝ → E} (c : F) :
    HasStieltjesIntegral a b B f (fun _ ↦ c) 0 := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · simp only [of_lt, hab] at ⊢
    apply HasStieltjesIntegral'.const_right
  · simp_all
  rw [symm_iff] at ⊢
  simp only [neg_zero, hab, of_lt] at ⊢
  apply HasStieltjesIntegral'.const_right

theorem HasStieltjesIntegral.zero_right {f : ℝ → E} : HasStieltjesIntegral a b B f 0 0 :=
  const_right a b B 0

private theorem HasStieltjesIntegral'.add_right {f : ℝ → E} {g₁ g₂ : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral' a b B f g₁ L₁) (h₂ : HasStieltjesIntegral' a b B f g₂ L₂) :
    HasStieltjesIntegral' a b B f (g₁ + g₂) (L₁ + L₂) := by
  unfold HasStieltjesIntegral' at h₁ h₂ ⊢
  have h : (fun x : ℝ ↦ B.flip ((g₁ + g₂) x)) =
      (fun x ↦ B.flip (g₁ x)) + (fun x ↦ B.flip (g₂ x)) := by ext; simp
  rw [h, map_add]
  exact h₁.add_vol h₂

theorem HasStieltjesIntegral.add_right {f : ℝ → E} {g₁ g₂ : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral a b B f g₁ L₁) (h₂ : HasStieltjesIntegral a b B f g₂ L₂) :
    HasStieltjesIntegral a b B f (g₁ + g₂) (L₁ + L₂) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · simp only [of_lt, hab] at h₁ h₂ ⊢
    exact h₁.add_right _ _ _ h₂
  · simp_all
  rw [symm_iff] at h₁ h₂ ⊢
  simp only [hab, of_lt] at h₁ h₂ ⊢
  convert h₁.add_right _ _ _ h₂ using 1
  abel

private theorem HasStieltjesIntegral'.neg_right {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral' a b B f g L) :
    HasStieltjesIntegral' a b B f (-g) (-L) := by
  unfold HasStieltjesIntegral' at h ⊢
  have heq : (fun x : ℝ ↦ B.flip ((-g) x)) = -(fun x ↦ B.flip (g x)) := by ext; simp
  rw [heq, map_neg]
  exact h.neg_vol

theorem HasStieltjesIntegral.neg_right {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral a b B f (-g) (-L) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · simp only [of_lt, hab] at h ⊢
    apply h.neg_right
  · simp_all
  rw [symm_iff] at h ⊢
  simp only [hab, of_lt, neg_neg] at h ⊢
  convert h.neg_right _ _ _ using 1
  norm_num

theorem HasStieltjesIntegral'.sub_right {f : ℝ → E} {g₁ g₂ : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral' a b B f g₁ L₁) (h₂ : HasStieltjesIntegral' a b B f g₂ L₂) :
    HasStieltjesIntegral' a b B f (g₁ - g₂) (L₁ - L₂) := by
  unfold HasStieltjesIntegral' at h₁ h₂ ⊢
  have h : (fun x : ℝ ↦ B.flip ((g₁ - g₂) x)) =
      (fun x ↦ B.flip (g₁ x)) - (fun x ↦ B.flip (g₂ x)) := by ext; simp
  rw [h, map_sub]
  exact h₁.sub_vol h₂

theorem HasStieltjesIntegral.sub_right {f : ℝ → E} {g₁ g₂ : ℝ → F} {L₁ L₂ : G}
    (h₁ : HasStieltjesIntegral a b B f g₁ L₁) (h₂ : HasStieltjesIntegral a b B f g₂ L₂) :
    HasStieltjesIntegral a b B f (g₁ - g₂) (L₁ - L₂) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · simp only [of_lt, hab] at h₁ h₂ ⊢
    exact h₁.sub_right _ _ _ h₂
  · simp_all
  rw [symm_iff] at h₁ h₂ ⊢
  simp only [hab, of_lt] at h₁ h₂ ⊢
  convert h₁.sub_right _ _ _ h₂ using 1
  abel

private theorem HasStieltjesIntegral'.smul_right {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral' a b B f g L) (c : ℝ) :
    HasStieltjesIntegral' a b B f (c • g) (c • L) := by
  unfold HasStieltjesIntegral' at h ⊢
  have heq : (fun x : ℝ ↦ B.flip ((c • g) x)) = c • (fun x ↦ B.flip (g x)) := by ext; simp
  rw [heq, BoxIntegral.BoxAdditiveMap.ofDiff_smul]
  exact h.smul_vol c

theorem HasStieltjesIntegral.smul_right {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) (c : ℝ) :
    HasStieltjesIntegral a b B f (c • g) (c • L) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · simp only [of_lt, hab] at h ⊢
    apply h.smul_right
  · simp_all
  rw [symm_iff] at h ⊢
  simp only [hab, of_lt] at h ⊢
  convert h.smul_right _ _ _ _ using 1
  norm_num

/-! ### Splitting over adjacent intervals -/

/-- If `f` is Stieltjes-integrable from `a` to `c`, has Stieltjes integral `L` from `a` to `b`
and `L'` from `b` to `c` then `f` has Stieltjes integral `L + L'` from `a` to `c`.  No ordering
is assumed in `a`, `b`, `c` in the final statement of the theorem. -/
private theorem HasStieltjesIntegral'.add_adjacent [CompleteSpace G]
    {f : ℝ → E} {g : ℝ → F} {L L' : G} {c : ℝ}
    (hab : a < b) (hbc : b < c)
    (h : StieltjesIntegrable' a c B f g)
    (h₁ : HasStieltjesIntegral' a b B f g L)
    (h₂ : HasStieltjesIntegral' b c B f g L') :
    HasStieltjesIntegral' a c B f g (L + L') := by
  simp only [HasStieltjesIntegral', StieltjesIntegrable'] at h h₁ h₂ ⊢
  have hac : a < c := hab.trans hbc
  have hb_mem :
      b ∈ Set.Ioo ((Ioc a c).lower 0) ((Ioc a c).upper 0) := by
    simp [Ioc.lower hac, Ioc.upper hac, hab, hbc]
  refine HasIntegral.split 0 b ?_ ?_ h h₁ h₂
  · rw [Box.splitLower_def hb_mem, WithBot.coe_eq_coe]
    ext x
    simp [Ioc.lower hac, mem_Ioc hab]
  · rw [Box.splitUpper_def hb_mem, WithBot.coe_eq_coe]
    ext x
    simp [Ioc.upper hac, mem_Ioc hbc]

private theorem HasStieltjesIntegral.add_adjacent_prelim [CompleteSpace G]
    {f : ℝ → E} {g : ℝ → F} {L L' L'' : G} {c : ℝ}
    (hab : a < b) (hbc : b < c)
    (h₁ : HasStieltjesIntegral a b B f g L)
    (h₂ : HasStieltjesIntegral b c B f g L')
    (h₃ : HasStieltjesIntegral a c B f g L'') :
    L'' = L + L' := by
  apply unique a c B h₃
  simp only [hab, of_lt, hbc, hab.trans hbc] at h₁ h₂ h₃ ⊢
  exact HasStieltjesIntegral'.add_adjacent _ _ _ hab hbc ⟨L'', h₃⟩ h₁ h₂

/-- Note: the proof here has an excessive amount of case splitting. -/
theorem HasStieltjesIntegral.add_adjacent [CompleteSpace G]
    {f : ℝ → E} {g : ℝ → F} {L L' : G} {c : ℝ}
    (h : StieltjesIntegrable a c B f g)
    (h₁ : HasStieltjesIntegral a b B f g L)
    (h₂ : HasStieltjesIntegral b c B f g L') :
    HasStieltjesIntegral a c B f g (L + L') := by
  have h₃ := h.hasStieltjesIntegral _ _ B
  set L'' := ∫⟨B⟩ x in a..c, f x d g
  by_cases! hab : a = b
  · simp_all
  by_cases! hbc : b = c
  · simp_all
  by_cases! hac : a = c
  · simp_all
    simp [h₁.unique _ _ _ h₂.symm]
  have h₁' := h₁.symm
  have h₂' := h₂.symm
  have h₃' := h₃.symm
  convert h₃
  rcases lt_or_gt_of_ne hab with hab | hba <;>
  rcases lt_or_gt_of_ne hbc with hbc | hcb <;>
  rcases lt_or_gt_of_ne hac with hac | hca <;>
  try order
  · simp_all [add_adjacent_prelim _ _ _ hab hbc h₁ h₂ h₃]
  · have := add_adjacent_prelim _ _ _ hac hcb h₃ h₂' h₁
    grind
  · have := add_adjacent_prelim _ _ _ hca hab h₃' h₁ h₂'
    grind
  · have := add_adjacent_prelim _ _ _ hba hac h₁' h₃ h₂
    grind
  · have := add_adjacent_prelim _ _ _ hbc hca h₂ h₃' h₁'
    grind
  · have := add_adjacent_prelim _ _ _ hcb hba h₂' h₁' h₃'
    grind

theorem stieltjesIntegral.add_adjacent [CompleteSpace G]
    {f : ℝ → E} {g : ℝ → F} {c : ℝ}
    (h : StieltjesIntegrable a c B f g)
    (h₁ : StieltjesIntegrable a b B f g)
    (h₂ : StieltjesIntegrable b c B f g) :
    ∫⟨B⟩ x in a..c, f x d g = ∫⟨B⟩ x in a..b, f x d g + ∫⟨B⟩ x in b..c, f x d g := by
  have h₁' := h₁.hasStieltjesIntegral _ _ B
  have h₂' := h₂.hasStieltjesIntegral _ _ B
  have := HasStieltjesIntegral.add_adjacent _ _ _ h h₁' h₂'
  rwa [h.hasStieltjesIntegral_iff] at this

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

theorem StieltjesIntegrable.const_right {f : ℝ → E} (c : F) :
    StieltjesIntegrable a b B f (fun _ ↦ c) :=
  (HasStieltjesIntegral.const_right a b B c).stieltjesIntegrable

theorem StieltjesIntegrable.zero_right {f : ℝ → E} : StieltjesIntegrable a b B f 0 :=
  const_right a b B 0

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

theorem stieltjesIntegral_zero_left {g : ℝ → F} : ∫⟨B⟩ _ in a..b, 0 d g = 0 :=
  (HasStieltjesIntegral.zero_left a b B).stieltjesIntegral_eq

theorem stieltjesIntegral_add_left {f₁ f₂ : ℝ → E} {g : ℝ → F}
    (h₁ : StieltjesIntegrable a b B f₁ g) (h₂ : StieltjesIntegrable a b B f₂ g) :
    ∫⟨B⟩ x in a..b, (f₁ + f₂) x d g
      = ∫⟨B⟩ x in a..b, f₁ x d g + ∫⟨B⟩ x in a..b, f₂ x d g := by
  rw [(h₁.hasStieltjesIntegral.add_left a b B h₂.hasStieltjesIntegral).stieltjesIntegral_eq,
    h₁.hasStieltjesIntegral.stieltjesIntegral_eq,
    h₂.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem stieltjesIntegral_neg_left {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) :
    ∫⟨B⟩ x in a..b, (-f) x d g = -∫⟨B⟩ x in a..b, f x d g := by
  rw [(h.hasStieltjesIntegral.neg_left a b B).stieltjesIntegral_eq,
    h.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem stieltjesIntegral_sub_left {f₁ f₂ : ℝ → E} {g : ℝ → F}
    (h₁ : StieltjesIntegrable a b B f₁ g) (h₂ : StieltjesIntegrable a b B f₂ g) :
    ∫⟨B⟩ x in a..b, (f₁ - f₂) x d g
      = ∫⟨B⟩ x in a..b, f₁ x d g - ∫⟨B⟩ x in a..b, f₂ x d g := by
  rw [(h₁.hasStieltjesIntegral.sub_left a b B h₂.hasStieltjesIntegral).stieltjesIntegral_eq,
    h₁.hasStieltjesIntegral.stieltjesIntegral_eq,
    h₂.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem stieltjesIntegral_smul_left {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) (c : ℝ) :
    ∫⟨B⟩ x in a..b, (c • f) x d g = c • ∫⟨B⟩ x in a..b, f x d g := by
  rw [(h.hasStieltjesIntegral.smul_left a b B c).stieltjesIntegral_eq,
    h.hasStieltjesIntegral.stieltjesIntegral_eq]

/-! ### Integral linearity in the integrator -/

@[simp]
theorem stieltjesIntegral_const_right {f : ℝ → E} (c : F) : ∫⟨B⟩ x in a..b, f x d (fun _ ↦ c) = 0 :=
  (HasStieltjesIntegral.const_right a b B c).stieltjesIntegral_eq

@[simp]
theorem stieltjesIntegral_zero_right {f : ℝ → E} : ∫⟨B⟩ x in a..b, f x d 0 = 0 :=
  stieltjesIntegral_const_right a b B 0

theorem stieltjesIntegral_add_right {f : ℝ → E} {g₁ g₂ : ℝ → F}
    (h₁ : StieltjesIntegrable a b B f g₁) (h₂ : StieltjesIntegrable a b B f g₂) :
    ∫⟨B⟩ x in a..b, f x d (g₁ + g₂)
      = ∫⟨B⟩ x in a..b, f x d g₁ + ∫⟨B⟩ x in a..b, f x d g₂ := by
  rw [(h₁.hasStieltjesIntegral.add_right a b B h₂.hasStieltjesIntegral).stieltjesIntegral_eq,
    h₁.hasStieltjesIntegral.stieltjesIntegral_eq,
    h₂.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem stieltjesIntegral_neg_right {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) :
    ∫⟨B⟩ x in a..b, f x d (-g) = -∫⟨B⟩ x in a..b, f x d g := by
  rw [(h.hasStieltjesIntegral.neg_right a b B).stieltjesIntegral_eq,
    h.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem stieltjesIntegral_sub_right {f : ℝ → E} {g₁ g₂ : ℝ → F}
    (h₁ : StieltjesIntegrable a b B f g₁) (h₂ : StieltjesIntegrable a b B f g₂) :
    ∫⟨B⟩ x in a..b, f x d (g₁ - g₂)
      = ∫⟨B⟩ x in a..b, f x d g₁ - ∫⟨B⟩ x in a..b, f x d g₂ := by
  rw [(h₁.hasStieltjesIntegral.sub_right a b B h₂.hasStieltjesIntegral).stieltjesIntegral_eq,
    h₁.hasStieltjesIntegral.stieltjesIntegral_eq,
    h₂.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem stieltjesIntegral_smul_right {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) (c : ℝ) :
    ∫⟨B⟩ x in a..b, f x d (c • g) = c • ∫⟨B⟩ x in a..b, f x d g := by
  rw [(h.hasStieltjesIntegral.smul_right a b B c).stieltjesIntegral_eq,
    h.hasStieltjesIntegral.stieltjesIntegral_eq]

/-! ### Naturality: transporting along continuous linear maps -/

/-- If a bilinear pairing `B : E →L[ℝ] F →L[ℝ] G` and CLMs `φ : E →L[ℝ] E'`, `ψ : F →L[ℝ] F'`,
`Ψ : G →L[ℝ] G'` satisfy the compatibility `Ψ (B e y) = B' (φ e) (ψ y)` for all `e, y`, then
`HasStieltjesIntegral` transports along `(φ, ψ, Ψ)`: applying `φ` to the integrand, `ψ` to the
integrator and `Ψ` to the integral preserves the Stieltjes-integral relation. -/
private theorem HasStieltjesIntegral'.map {E' F' G' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {f : ℝ → E} {g : ℝ → F} {L : G}
    (φ : E →L[ℝ] E') (ψ : F →L[ℝ] F') (Ψ : G →L[ℝ] G')
    (B' : E' →L[ℝ] F' →L[ℝ] G')
    (hB : ∀ e y, Ψ (B e y) = B' (φ e) (ψ y))
    (h : HasStieltjesIntegral' a b B f g L) :
    HasStieltjesIntegral' a b B' (fun x ↦ φ (f x)) (fun x ↦ ψ (g x)) (Ψ L) := by
  unfold HasStieltjesIntegral' at h ⊢
  refine HasIntegral.map φ Ψ ?_ h
  intro J e
  simp only [BoxIntegral.BoxAdditiveMap.ofDiff_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.flip_apply, map_sub, hB]

theorem HasStieltjesIntegral.map {E' F' G' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {f : ℝ → E} {g : ℝ → F} {L : G}
    (φ : E →L[ℝ] E') (ψ : F →L[ℝ] F') (Ψ : G →L[ℝ] G')
    (B' : E' →L[ℝ] F' →L[ℝ] G')
    (hB : ∀ e y, Ψ (B e y) = B' (φ e) (ψ y))
    (h : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral a b B' (fun x ↦ φ (f x)) (fun x ↦ ψ (g x)) (Ψ L) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · simp only [of_lt, hab] at h ⊢
    exact h.map _ _ _ _ _ _ _ hB
  · simp_all
  rw [symm_iff] at h ⊢
  simp only [hab, of_lt] at h ⊢
  convert h.map _ _ _ _ _ _ _ hB using 1
  simp

/-- Existence-level naturality: if `(B, B', φ, ψ, Ψ)` are compatible in the sense of
`HasStieltjesIntegral.map`, then `StieltjesIntegrable` is preserved when transporting
the integrand along `φ` and the integrator along `ψ`. -/
theorem StieltjesIntegrable.map {E' F' G' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {f : ℝ → E} {g : ℝ → F}
    (φ : E →L[ℝ] E') (ψ : F →L[ℝ] F') (Ψ : G →L[ℝ] G')
    (B' : E' →L[ℝ] F' →L[ℝ] G')
    (hB : ∀ e y, Ψ (B e y) = B' (φ e) (ψ y))
    (h : StieltjesIntegrable a b B f g) :
    StieltjesIntegrable a b B' (fun x ↦ φ (f x)) (fun x ↦ ψ (g x)) :=
  (h.hasStieltjesIntegral.map a b B φ ψ Ψ B' hB).stieltjesIntegrable

/-- Function-level naturality of `stieltjesIntegral` under continuous linear maps. -/
theorem stieltjesIntegral_map {E' F' G' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {f : ℝ → E} {g : ℝ → F}
    (φ : E →L[ℝ] E') (ψ : F →L[ℝ] F') (Ψ : G →L[ℝ] G')
    (B' : E' →L[ℝ] F' →L[ℝ] G')
    (hB : ∀ e y, Ψ (B e y) = B' (φ e) (ψ y))
    (h : StieltjesIntegrable a b B f g) :
    ∫⟨B'⟩ x in a..b, φ (f x) d (fun x ↦ ψ (g x)) =
      Ψ (∫⟨B⟩ x in a..b, f x d g) := by
  rw [(h.hasStieltjesIntegral.map a b B φ ψ Ψ B' hB).stieltjesIntegral_eq,
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
    (f : ℝ → E) (g : ℝ → F) (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : BoundedVariationOn g (Set.Icc a b)) :
    StieltjesIntegrable a b B f g := by
  have hint := integrable_of_continuousOn_of_boundedVariationOn a b B f g hf hg
  rw [StieltjesIntegrable.of_lt _ _ _ _ _ hab]
  exact ⟨_, Integrable.hasIntegral hint⟩

/-- Theorem A.2 of Montgomery Vaughan: if ∫ₐᵇ f dg exists, then ∫ₐᵇ g df exists and
∫ₐᵇ g df = g(b) * f(b) - g(a) * f(a) - ∫ₐᵇ f dg. -/
theorem HasStieltjesIntegral.by_parts {f : ℝ → E} {g : ℝ → F} {L : G}
    (hL : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral a b B.flip g f (B (f b) (g b) - B (f a) (g a) - L) := by sorry

theorem StieltjesIntegrable.by_parts {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) :
    StieltjesIntegrable a b B.flip g f := by
  exact ⟨_, (h.hasStieltjesIntegral.by_parts a b B)⟩

theorem stieltjesIntegral.by_parts {f : ℝ → E} {g : ℝ → F}
    (h : StieltjesIntegrable a b B f g) :
    ∫⟨B.flip⟩ x in a..b, g x d f = B (f b) (g b) - B (f a) (g a) - ∫⟨B⟩ x in a..b, f x d g := by
  rw [(h.hasStieltjesIntegral.by_parts a b B).stieltjesIntegral_eq,
    h.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem HasStieltjesIntegral.of_const (c : E) (g : ℝ → F) :
    HasStieltjesIntegral a b B (fun _ ↦ c) g (B c (g b) - B c (g a)) := by
  convert by_parts a b B.flip (f := g) (g := fun _ ↦ c) (L := 0) (by simp [const_right]) using 1
  simp [flip_apply]

theorem StieltjesIntegrable.of_const (c : E) (g : ℝ → F) :
    StieltjesIntegrable a b B (fun _ ↦ c) g :=
  (HasStieltjesIntegral.of_const a b B c g).stieltjesIntegrable

@[simp]
theorem stieltjesIntegral.of_const (c : E) (g : ℝ → F) :
    ∫⟨B⟩ _ in a..b, c d g = B c (g b) - B c (g a) :=
  (HasStieltjesIntegral.of_const a b B c g).stieltjesIntegral_eq


/-- Lemma Subset given an interval [a,b], if c,d ∈ [a,b], then |c - d| < b -a
-/
lemma subset_smaller_distance {a b m n : ℝ} (hm : m ∈ Set.Icc a b)
  (hn : n ∈ Set.Icc a b) : |m - n| ≤ b - a := by
  rcases hm with ⟨ham, hmb⟩
  rcases hn with ⟨han, hnb⟩
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

abbrev RiemannIntegrable (f : ℝ → E) : Prop :=
  Integrable (Ioc a b) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) BoxAdditiveMap.volume

/-- Lemma MVT version using a bilinear form, this theorem is used in the proof of Theorem A3 (b)
Since the MVT is false in general (for higher dimensions), we prove a version where it is true up
to some error term.

For g : ℝ → F and f : ℝ → E, and B a bounded blinear from from E × F → G where E, F, and G are
normed. Then if g is C^1[a,b], and f is bounded on [a,b], then for any ε > 0, there is a δ > 0 such
that for all a',b' with a ≤ a' < b' ≤ b, we have for all c ∈ [a',b'] that
‖B(f(c),g(b') - g(a'))‖ ≤ ‖B(f(c),g'(c))‖ (b' - a') + ε (b' - a')
We remark that the theorem is most powerful when we take a' = a and b' = b. Since this is used to
say that if the mesh is fine enough (of size < δ), then we have this MVT with small error.

Remark: In the use of MV theorem A3, they assume that f is Riemann integrable on [a,b], and use the
fact that this will imply that f is bounded. However, for the MVT statement, we need only that f is
bounded. Furthermore, there is no statement in Mathlib that states that Riemann integrable functions
are bounded.
-/
lemma MVT_with_bilinear_form_and_error [CompleteSpace F] {f : ℝ → E} {g : ℝ → F} {ε : ℝ}
  {B : E →L[ℝ] F →L[ℝ] G} (hab : a < b) (hg : ContDiffOn ℝ 1 g (Set.Icc a b)) (hε : 0 < ε)
  (hB : B ≠ 0) (f_bounded : ∃ M > 0, ∀ x ∈ (Set.Icc a b), ‖f x‖ < M) : ∃ δ > 0, ∀ a' ≥ a, ∀ b' ≤ b,
  a' < b' → b' - a' < δ → ∀ c ∈ Set.Icc a' b', ‖B (f c) (g b' -g a')‖
    ≤ ‖B (f c) (derivWithin g (Set.Icc a' b') c)‖ * (b' - a') + ε * (b' - a') := by
  have hba_pos : 0 < b - a := by linarith
  have hderiv_ucont : UniformContinuousOn (derivWithin g (Set.Icc a b)) (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (ContDiffOn.continuousOn_derivWithin hg (uniqueDiffOn_Icc hab) le_rfl)
  have hB_norm_pos : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have huIcc_eq_Icc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab.le
  have hB_opNorm_bound : ∀ (y : F) (x : ℝ), ‖B (f x) y‖ ≤ ‖B‖ * ‖f x‖ * ‖y‖ :=
    fun y x => B.le_opNorm₂ (f x) y
  rw [Metric.uniformContinuousOn_iff] at hderiv_ucont
  obtain ⟨M, hM_pos, hM_bound⟩ := f_bounded
  let ε₂ := ε / (‖B‖ * M)
  have hε₂_pos : 0 < ε₂ := div_pos hε (by positivity)
  obtain ⟨δ, hδ_pos, hδ_prop⟩ := hderiv_ucont ε₂ hε₂_pos
  refine ⟨δ, hδ_pos, fun a' ha' b' hb' h_a'_lt_b' h_b'_sub_a'_lt_δ c hc => ?_⟩
  have hc_mem_big_Icc : c ∈ Set.Icc a b := by grind
  have h_sub_len_le : b' - a' ≤ b - a := by linarith
  have h_abs_sub_eq : |b' - a'| = b' - a' := by grind
  have huIoc_eq_Ioc : Set.uIoc a' b' = Set.Ioc a' b' := by grind
  have huIcc_eq_Icc' : Set.uIcc a' b' = Set.Icc a' b' := Set.uIcc_of_le h_a'_lt_b'.le
  have hIcc_subset : (Set.Icc a' b') ⊆ (Set.Icc a b) := by grind
  have hg_restricted : ContDiffOn ℝ 1 g (Set.Icc a' b') := hg.mono hIcc_subset
  have hderiv_ucont_sub : UniformContinuousOn (derivWithin g (Set.Icc a' b')) (Set.Icc a' b') :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (ContDiffOn.continuousOn_derivWithin hg_restricted (uniqueDiffOn_Icc h_a'_lt_b') le_rfl)
  have hderiv_integrable :
      IntervalIntegrable (derivWithin g (Set.uIcc a' b')) MeasureTheory.volume a' b' := by
    have : ContinuousOn (derivWithin g (Set.uIcc a' b')) (Set.uIcc a' b') := by
      rw [huIcc_eq_Icc']
      exact hderiv_ucont_sub.continuousOn
    exact this.intervalIntegrable
  have hg_ftc := intervalIntegral.integral_deriv_of_contDiffOn_Icc hg_restricted h_a'_lt_b'.le
  have hderiv_eq_on_interior : ∀ x ∈ Set.Ioo (min a' b') (max a' b'),
      derivWithin g (Set.uIcc a' b') x = deriv g x := by
    intro x hx
    rw [Set.uIcc_of_le h_a'_lt_b'.le]
    have hx_open : x ∈ Set.Ioo a' b' := by grind
    exact derivWithin_of_mem_nhds
      (Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hx_open) Set.Ioo_subset_Icc_self)
  have hintegral_deriv_congr : ∫ x in a'..b', deriv g x = ∫ x in a'..b',
      derivWithin g (Set.Icc a' b') x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (MeasureTheory.measure_singleton b')]
    with x hxb hx
    grind
  rw [← hg_ftc, hintegral_deriv_congr]
  have hintegrand_split_eq : ‖B (f c) (∫ x in a'..b', derivWithin g (Set.Icc a' b') x)‖ =
      ‖B (f c) (∫ x in a'..b', derivWithin g (Set.Icc a' b') c +
      (derivWithin g (Set.Icc a' b') x - derivWithin g (Set.Icc a' b') c))‖ := by grind
  rw [hintegrand_split_eq]
  have hintegral_add_split : (∫ x in a'..b', derivWithin g (Set.Icc a' b') c) +
      (∫ x in a'..b', (derivWithin g (Set.Icc a' b') x - derivWithin g (Set.Icc a' b') c))
      = ∫ x in a'..b', derivWithin g (Set.Icc a' b') c
        + (derivWithin g (Set.Icc a' b') x - derivWithin g (Set.Icc a' b') c) := by
    rw [intervalIntegral.integral_add]
    · exact intervalIntegrable_const
    · refine IntervalIntegrable.sub ?_ intervalIntegrable_const
      apply IntervalIntegrable.congr_ae hderiv_integrable
      rw [huIcc_eq_Icc']
  rw [← hintegral_add_split]
  have hderiv_diff_lt_ε₂ : ∀ x ∈ Set.Icc a' b',
      ‖derivWithin g (Set.Icc a' b') x - derivWithin g (Set.Icc a' b') c‖ < ε₂ := by
    intro x hx
    have hx_mem_big_Icc : x ∈ Set.Icc a b := by grind
    have hdist_lt_delta : dist x c < δ :=
      Std.lt_of_le_of_lt (subset_smaller_distance hx hc) h_b'_sub_a'_lt_δ
    specialize hδ_prop x hx_mem_big_Icc c hc_mem_big_Icc hdist_lt_delta
    rw [← dist_eq_norm]
    have hderiv_x_congr : derivWithin g (Set.Icc a' b') x = derivWithin g (Set.Icc a b) x :=
      derivWithin_subset hIcc_subset (uniqueDiffOn_Icc h_a'_lt_b' x hx)
        (hg.differentiableOn one_ne_zero x hx_mem_big_Icc)
    have hderiv_c_congr : derivWithin g (Set.Icc a' b') c = derivWithin g (Set.Icc a b) c :=
      derivWithin_subset hIcc_subset (uniqueDiffOn_Icc h_a'_lt_b' c hc)
        (hg.differentiableOn one_ne_zero c hc_mem_big_Icc)
    rw [hderiv_x_congr, hderiv_c_congr]
    exact hδ_prop
  have herror_norm_bound : ‖∫ x in a'..b',
        derivWithin g (Set.Icc a' b') x - derivWithin g (Set.Icc a' b') c‖ ≤ ε₂ * |b' - a'| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [huIoc_eq_Ioc] at hx
    exact (hderiv_diff_lt_ε₂ x ⟨hx.1.le, hx.2⟩).le
  rw [map_add]
  apply le_trans (norm_add_le _ _)
  apply add_le_add
  · rw [intervalIntegral.integral_const, map_smul, norm_smul, Real.norm_eq_abs, h_abs_sub_eq]
    ring_nf
    linarith
  · refine (hB_opNorm_bound _ c).trans ?_
    rw [h_abs_sub_eq] at herror_norm_bound
    field_simp at herror_norm_bound
    have hB_fc_times_error : ‖B‖ * ‖f c‖ * ‖∫ (x : ℝ) in a'..b', derivWithin g (Set.Icc a' b') x
        - derivWithin g (Set.Icc a' b') c‖ ≤ ‖B‖ * ‖f c‖ * (ε₂ * (b' - a')) :=
      mul_le_mul_of_nonneg_left herror_norm_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    refine hB_fc_times_error.trans ?_
    unfold ε₂
    specialize hM_bound c hc_mem_big_Icc
    have hBM_pos : 0 < ‖B‖ * M := mul_pos hB_norm_pos hM_pos
    have hfc_lt_bound : ‖B‖ * ‖f c‖ * (ε / (‖B‖ * M) * (b' - a')) <
        ‖B‖ * M * (ε / (‖B‖ * M) * (b' - a')) := by
      apply mul_lt_mul_of_pos_right
      · exact mul_lt_mul_of_pos_left hM_bound hB_norm_pos
      · exact mul_pos (div_pos hε hBM_pos) (sub_pos.mpr h_a'_lt_b')
    refine hfc_lt_bound.le.trans ?_
    field_simp
    linarith

/-- Lemma for a vector valued MVT with error since MVT is false for a general
funcion in higher dimensions, but is true up to some error for higher dimensions.
This lemma is used in the proof of Theorem A3 (a). We prove it by specializing the
bilinear form version of the statement. However, we must break into cases on whether
or not F is the trivial space.

For g C^1[a,b] and ε > 0, there is a δ > 0 such that for all a ≤ a' < b' ≤ b with
b' - a' < δ, we have that for all c ∈ [a',b'] that
‖g(b')-g(a')‖ ≤ ‖g'(c)‖ * (b' - a') + ε * (b' - a')
-/
lemma MVT_with_error [CompleteSpace F] {g : ℝ → F} {ε : ℝ} (hab : a < b)
    (hg : ContDiffOn ℝ 1 g (Set.Icc a b)) (hε : 0 < ε)
    : ∃ δ > 0, ∀ a' ≥ a, ∀ b' ≤ b, a' < b' → b' - a' < δ → ∀ c ∈ Set.Icc a' b',
    ‖g b' - g a'‖ ≤ ‖derivWithin g (Set.Icc a' b') c‖ * (b' - a') + ε * (b' - a') := by
  let f : ℝ → ℝ := fun _ => 1
  have f_bounded : ∃ M > 0, ∀ x ∈ (Set.Icc a b), ‖f x‖ < M := by
    use 2
    constructor
    · linarith
    · intro x hx
      unfold f
      simp
  let B := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)
  rcases subsingleton_or_nontrivial F with hF | hf
  · use 1, zero_lt_one
    intro a' ha' b' hb' hab' hdist c hc
    have : g b' - g a' = 0 := Subsingleton.elim _ _
    simp only [this, norm_zero]
    apply add_nonneg
    · exact mul_nonneg (norm_nonneg _) (sub_nonneg.mpr hab'.le)
    · exact mul_nonneg hε.le (sub_nonneg.mpr hab'.le)
  · have hB : B ≠ 0 := by
      -- Since F is nontrivial, there is some v ≠ 0. B(1, v) = v ≠ 0.
      intro h
      obtain ⟨v, hv⟩ := exists_ne (0 : F)
      have h_one_v := DFunLike.congr_fun (DFunLike.congr_fun h 1) v
      simp only [B, ContinuousLinearMap.lsmul_apply, one_smul] at h_one_v
      exact hv h_one_v
    obtain ⟨δ, hδ_pos, hδ⟩ := MVT_with_bilinear_form_and_error a b hab hg hε hB f_bounded
    use δ, hδ_pos
    intro a' ha' b' hb' hab' hdist c hc
    specialize hδ a' ha' b' hb' hab' hdist c hc
    simpa [B, f] using hδ

/--Theorem A.3 (a). If g' is C^1[a,b], then Var_[a,b] g = ∫_a^b |g'(x)|dx
-/
theorem variation_of_derivative {g : ℝ → F} (hab : a < b) (hg : ContDiffOn ℝ 1 g (Set.Icc a b)) :
    (eVariationOn g (Set.Icc a b)).toReal = ∫ x in a..b, ‖deriv g x‖ := by
    sorry

/-- Theorem A.3 (b).  If g′ is continuous on [a, b] and if in addition f is
Riemann integrable, then ∫ₐᵇ f(x) dg(x) = ∫ₐᵇ f(x) g′(x) dx. -/

theorem integral_of_derivative {f : ℝ → E} {g : ℝ → F} (hab : a < b)
    (hg : ContDiffOn ℝ 1 g (Set.Icc a b))
    (hf : RiemannIntegrable a b f) :
    HasStieltjesIntegral a b B f g (∫ x in a..b, B (f x) (deriv g x)) := byx
    sorry

/-- Theorem A.4. Suppose that g has bounded variation, and put g∗(x) = Varₐˣ g. Then
‖∫ₐᵇ f(x) dg(x)‖ ≤ ∫ₐᵇ ‖f(x)‖ dg∗(x),
provided that both integrals exist. -/
theorem integral_le_integral_of_variation {f : ℝ → E} {g : ℝ → F} {L : G} {L' : ℝ} (hab : a < b)
    (hg : BoundedVariationOn g (Set.Icc a b))
    (hfg : HasStieltjesIntegral a b B f g L)
    (hfabs_gstar : HasStieltjesIntegral a b (mul ℝ ℝ) (fun x ↦ ‖f x‖)
      (fun x ↦ (eVariationOn g (Set.Icc a x)).toReal) L') :
    ‖L‖ ≤ ‖B‖ * L' := by sorry

/-! ### Connection to standard integrals -/

/-- When the integrator is the identity, the Stieltjes integral with the scalar-multiplication
pairing `(lsmul ℝ ℝ).flip` reduces to the ordinary `BoxIntegral.HasIntegral` against the
Lebesgue volume on `(a, b]`. -/
theorem hasStieltjesIntegral_id_iff_hasIntegral_volume (hab : a < b) (f : ℝ → E) (L : E) :
    HasStieltjesIntegral a b (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip f id L ↔
      HasIntegral (Ioc a b) IntegrationParams.Riemann (fun x ↦ f (x 0))
        BoxAdditiveMap.volume L := by sorry

/-- Function-level form of Theorem A.3(b) (`integral_of_derivative`): when `g` is `C¹` on
`[a, b]` and `f` is Riemann integrable, the Stieltjes integral of `f` against `g` equals the
Riemann integral of `B (f x) (g' x)`. -/
theorem stieltjesIntegral_eq_intervalIntegral_of_contDiffOn {f : ℝ → E} {g : ℝ → F} (hab : a < b)
    (hg : ContDiffOn ℝ 1 g (Set.Icc a b)) (hf : RiemannIntegrable a b f) :
    stieltjesIntegral a b B f g = ∫ x in a..b, B (f x) (deriv g x) :=
  (integral_of_derivative a b B hab hg hf).stieltjesIntegral_eq

/-! ### Sums as Stieltjes integrals -/

/-- Relate sums ∑ f(n) with Stieltjes integrals ∫ f d ⌊x⌋ -/
theorem sum_eq_integral_nat_floor (hab : a < b) (f : ℝ → E) :
    HasStieltjesIntegral a b (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip f
      (fun x ↦ ⌊x⌋₊)
      (∑ n ∈ Finset.Ico ⌈a⌉₊ ⌈b⌉₊, f n) := by sorry

theorem sum_eq_integral_int_floor (hab : a < b) (f : ℝ → E) :
    HasStieltjesIntegral a b (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip f
      (fun x ↦ ⌊x⌋)
      (∑ n ∈ Finset.Ico ⌈a⌉ ⌈b⌉, f n) := by sorry

/-- Sum of pairings `B (f n) (g n)` over natural `n ∈ (⌊a⌋, ⌊b⌋]`, expressed as a Stieltjes
integral of `f` against the right-continuous summatory `x ↦ ∑ n ≤ x, g n`. -/
theorem sum_eq_integral_natSummatory_le (hab : a < b) (f : ℝ → E) (g : ℕ → F) :
    HasStieltjesIntegral a b B f
      (fun x ↦ ∑ n ∈ Finset.Iic ⌊x⌋₊, g n)
      (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, B (f n) (g n)) := by sorry

/-- Sum of pairings `B (f n) (g n)` over natural `n ∈ [⌈a⌉, ⌈b⌉)`, expressed as a Stieltjes
integral of `f` against the left-continuous summatory `x ↦ ∑ n < x, g n`. -/
theorem sum_eq_integral_natSummatory_lt (hab : a < b) (f : ℝ → E) (g : ℕ → F) :
    HasStieltjesIntegral a b B f
      (fun x ↦ ∑ n ∈ Finset.Iio ⌈x⌉₊, g n)
      (∑ n ∈ Finset.Ico ⌈a⌉₊ ⌈b⌉₊, B (f n) (g n)) := by sorry

end Stieltjes
