/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

/-! # Riemann–Stieltjes integral

In this file we define the (one-dimensional) Riemann–Stieltjes integral `∫⟨B⟩ x in a..b, f x ∂g`
from `a` to `b` of a function `f : ℝ → E` against an integrator `g : ℝ → F`, paired
by a continuous bilinear map `B : E →L[ℝ] F →L[ℝ] G`.  It is not required that `a < b`.

The notation here is deliberately chosen to mimic the notation `∫ x in a..b, f x ∂μ` for
`IntervalIntegral`.

The bilinear pairing `B` covers the three main variants of
Stieltjes integration that appear in practice:
* **`f` scalar, `g` vector-valued.** Here we take `B = ContinuousLinearMap.lsmul ℝ ℝ`
* **`f` vector-valued, `g` scalar.** Here we take `B = (ContinuousLinearMap.lsmul ℝ ℝ).flip`.
* **`f` and `g` are both real or both complex.** Here we take `B = ContinuousLinearMap.mul ℝ E`.

The development follows the treatment of Riemann–Stieltjes integration in
Montgomery–Vaughan, *Multiplicative Number Theory I: Classical Theory*, Appendix A.

## Key definitions

* `BoxIntegral.StieltjesIntegrable a b B f g`: the predicate that the integral
`∫⟨B⟩ x in a..b, f x ∂g` exists.
* `BoxIntegral.HasIntegral a b B f g L`: the predicate that the integral `∫⟨B⟩ x in a..b, f x ∂g`
exists and equals `L`.
* `BoxIntegral.stieltjesIntegral a b B f g`: the value of `∫⟨B⟩ x in a..b, f x ∂g` if it exists, or
the junk value of `0` otherwise.

## Implementation notes

Mathematically, one can define `∫⟨B⟩ x in a..b, f x ∂g` for `a < b` as the limit of
Riemann-Stieltjes sums `∑ B (f (π.tag x)) (g(x.upper) - g(x.lower))` as the mesh size of the
tagged partition `π` of `(a, b]` tends to `0`.  We implement this via the
`BoxIntegral.HasIntegral` predicate on `Box (Fin 1)`, relying in particular on the differential
`ofDiff g` of `g`, which is implemented as a `BoxAdditiveMap`.

The Riemann--Stieltjes integral is also extended to the `a = b` and `a > b` cases by antisymmetry.
In all cases, we denote the integral by `∫⟨B⟩ x in a..b, f x ∂g`.

## Tags

Stieltjes integral, Riemann–Stieltjes, bounded variation
-/

@[expose] public section

open scoped BigOperators
open BoxIntegral

open BoxIntegral ContinuousLinearMap

namespace BoxIntegral

/-! ## Definition of the Riemann--Stieltjes integral -/

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable (a b : ℝ) (B : E →L[ℝ] F →L[ℝ] G)

/-- The (Riemann--)Stieltjes integral of a function `f : ℝ → E` and `g : ℝ → F` given a bilinear
map `B : E → F → G` and endpoints `a`, `b` takes values in `G`.
Initially defined under the implicit assumption that `a < b`. -/
def HasStieltjesIntegral' (f : ℝ → E) (g : ℝ → F) (L : G) : Prop :=
  HasIntegral (Ioc a b) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) (BoxAdditiveMap.ofDiff (fun x ↦ B.flip (g x))) L

/-- Extension of the Stieltjes integral to cover the cases `a = b` and `a > b`.  Prefer this
notion over `HasStieltjesIntegral'`, as it has a more developed API. -/
def HasStieltjesIntegral (f : ℝ → E) (g : ℝ → F) (L : G) : Prop :=
  if a = b then L = 0 else
    if a < b then HasStieltjesIntegral' a b B f g L else
      HasStieltjesIntegral' b a B f g (-L)

@[simp]
lemma HasStieltjesIntegral.of_eq_iff_zero (f : ℝ → E) (g : ℝ → F) (L : G) :
    HasStieltjesIntegral a a B f g L ↔ L = 0 := by
  simp [HasStieltjesIntegral]

@[simp]
lemma HasStieltjesIntegral.of_lt {a b : ℝ} (f : ℝ → E) (g : ℝ → F) (L : G) (hab : a < b) :
    HasStieltjesIntegral a b B f g L ↔ HasStieltjesIntegral' a b B f g L := by
  simp [HasStieltjesIntegral, hab, hab.ne]

@[simp]
lemma HasStieltjesIntegral.of_gt {a b : ℝ} (f : ℝ → E) (g : ℝ → F) (L : G) (hba : b < a) :
    HasStieltjesIntegral a b B f g L ↔ HasStieltjesIntegral' b a B f g (-L) := by
  simp [HasStieltjesIntegral, Std.not_gt_of_lt hba, hba.ne.symm]

lemma HasStieltjesIntegral.symm_iff (f : ℝ → E) (g : ℝ → F) (L : G) :
    HasStieltjesIntegral a b B f g L ↔ HasStieltjesIntegral b a B f g (-L) := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [HasStieltjesIntegral, h, Std.not_gt_of_lt h, h.ne, h.ne.symm]
  · simp [HasStieltjesIntegral]
  simp [HasStieltjesIntegral, h, Std.not_gt_of_lt h, h.ne, h.ne.symm]

/-- Technically, this lemma is not currently usable by the `symm` tactic because it also maps
`L` to `-L`.  Adding the tag anyway in case a future version of `symm` is able to use this lemma. -/
@[symm]
lemma HasStieltjesIntegral.symm {a b : ℝ} {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral b a B f g (-L) := by
  rwa [← symm_iff]

/-- `StieltjesIntegrable' a b B f g` asserts that the Riemann–Stieltjes integral of `f` against `g`
paired by `B` over `(a, b]` exists, i.e. some `L` satisfies `HasStieltjesIntegral' a b B f g L`.
-/
def StieltjesIntegrable' (f : ℝ → E) (g : ℝ → F) : Prop :=
  ∃ L, HasStieltjesIntegral' a b B f g L

/-- `StieltjesIntegrable a b B f g` asserts that the Riemann–Stieltjes integral of `f` against `g`
paired by `B` from `a` to `b` exists, i.e. some `L` satisfies `HasStieltjesIntegral a b B f g L`.

Prefer this over `StieltjesIntegrable` as it has a better API and remains
useful even outside of the case `a < b`.
-/
def StieltjesIntegrable (f : ℝ → E) (g : ℝ → F) : Prop :=
  ∃ L, HasStieltjesIntegral a b B f g L

theorem stieltjesIntegrable'_iff_integrable {f : ℝ → E} {g : ℝ → F} :
  StieltjesIntegrable' a b B f g ↔
  Integrable (Ioc a b) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) (BoxAdditiveMap.ofDiff (fun x ↦ B.flip (g x))) :=
  ⟨ fun ⟨ _, hL ⟩ ↦ HasIntegral.integrable hL, fun h ↦ ⟨ _, h.hasIntegral ⟩ ⟩

@[simp]
lemma StieltjesIntegrable.of_eq (f : ℝ → E) (g : ℝ → F) :
  StieltjesIntegrable a a B f g := by
  simp [StieltjesIntegrable, HasStieltjesIntegral]

lemma StieltjesIntegrable.of_lt {a b : ℝ} (f : ℝ → E) (g : ℝ → F) (hab : a < b) :
    StieltjesIntegrable a b B f g ↔ StieltjesIntegrable' a b B f g := by
  simp [StieltjesIntegrable, StieltjesIntegrable', hab]

lemma StieltjesIntegrable.symm_iff (f : ℝ → E) (g : ℝ → F) :
    StieltjesIntegrable a b B f g ↔ StieltjesIntegrable b a B f g := by
  unfold StieltjesIntegrable
  constructor <;> rintro ⟨ L, h ⟩ <;> use -L <;> apply h.symm

@[symm]
lemma StieltjesIntegrable.symm {a b : ℝ} {B : E →L[ℝ] F →L[ℝ] G} {f : ℝ → E} {g : ℝ → F}
  (h : StieltjesIntegrable a b B f g) :  StieltjesIntegrable b a B f g := by
  rwa [← symm_iff]

lemma StieltjesIntegrable.iff_min_max {f : ℝ → E} {g : ℝ → F} :
    StieltjesIntegrable a b B f g ↔
    StieltjesIntegrable (min a b) (max a b) B f g := by
  rcases le_total a b with h | h <;> simp [h, symm_iff]

open Classical in
/-- The Riemann–Stieltjes integral of `f` against `g` paired by `B` from `a` to `b`.
Returns the junk value `0` if no such integral exists.
The integral remains meaningful outside of the case `a < b`. -/
noncomputable def stieltjesIntegral (f : ℝ → E) (g : ℝ → F) : G :=
  if h : StieltjesIntegrable a b B f g then h.choose else 0

/-- Notation for the Riemann–Stieltjes integral. `∫⟨B⟩ x in a..b, f x ∂g` is
`stieltjesIntegral a b B (fun x ↦ f x) g`.
The notation parallels Mathlib's `∫ x in a..b, f x ∂μ` for `intervalIntegral`. -/
scoped notation3 "∫⟨"B"⟩ "(...)" in "a".."b", "r:60:(scoped f => f)" ∂"g:70 =>
  stieltjesIntegral a b B r g

/-! ## Simple properties -/

/-- Uniqueness: the Riemann–Stieltjes integral, when it exists, is unique. -/
theorem HasStieltjesIntegral.unique {a b : ℝ} {B : E →L[ℝ] F →L[ℝ] G}
    {f : ℝ → E} {g : ℝ → F} {L₁ L₂ : G}
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
theorem HasStieltjesIntegral.stieltjesIntegrable {a b : ℝ} {B : E →L[ℝ] F →L[ℝ] G}
    {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) : StieltjesIntegrable a b B f g :=
  ⟨L, h⟩

/-- A chosen witness extracted from `StieltjesIntegrable`. -/
theorem StieltjesIntegrable.hasStieltjesIntegral {a b : ℝ} {B : E →L[ℝ] F →L[ℝ] G}
    {f : ℝ → E} {g : ℝ → F} (h : StieltjesIntegrable a b B f g) :
    HasStieltjesIntegral a b B f g (∫⟨B⟩ x in a..b, f x ∂g) := by
  simp [stieltjesIntegral, h, h.choose_spec]

/-- If `HasStieltjesIntegral a b B f g L`, then `stieltjesIntegral a b B f g = L`. -/
theorem HasStieltjesIntegral.stieltjesIntegral_eq {a b : ℝ} {B : E →L[ℝ] F →L[ℝ] G}
    {f : ℝ → E} {g : ℝ → F} {L : G}
    (h : HasStieltjesIntegral a b B f g L) : ∫⟨B⟩ x in a..b, f x ∂g = L := by
  classical
  have hI : StieltjesIntegrable a b B f g := h.stieltjesIntegrable
  simp only [stieltjesIntegral, dif_pos hI]
  exact hI.choose_spec.unique h

theorem StieltjesIntegrable.hasStieltjesIntegral_iff {a b : ℝ} {B : E →L[ℝ] F →L[ℝ] G}
    {f : ℝ → E} {g : ℝ → F} (h : StieltjesIntegrable a b B f g) (L : G) :
   HasStieltjesIntegral a b B f g L ↔ ∫⟨B⟩ x in a..b, f x ∂g = L
     := by
  grind [hasStieltjesIntegral, HasStieltjesIntegral.unique]

@[simp]
theorem stieltjesIntegral.of_eq (f : ℝ → E) (g : ℝ → F) :
    ∫⟨B⟩ x in a..a, f x ∂g = 0 := by
  simp only [stieltjesIntegral, StieltjesIntegrable.of_eq, ↓reduceDIte]
  rw [← HasStieltjesIntegral.of_eq_iff_zero a B f g]
  apply Exists.choose_spec

theorem stieltjesIntegral.integral_symm (f : ℝ → E) (g : ℝ → F) :
    ∫⟨B⟩ x in b..a, f x ∂g = -∫⟨B⟩ x in a..b, f x ∂g := by
  by_cases h_integ : StieltjesIntegrable a b B f g
  · exact (h_integ.hasStieltjesIntegral.symm.unique h_integ.symm.hasStieltjesIntegral).symm
  have h_integ_symm : ¬ StieltjesIntegrable b a B f g := by contrapose! h_integ; exact h_integ.symm
  simp [stieltjesIntegral, h_integ, h_integ_symm]

/-! ## The Riemann integral -/

def HasRiemannIntegral (f : ℝ → E) (L : E) :=
    HasStieltjesIntegral a b (lsmul ℝ ℝ).flip f id L

def RiemannIntegrable (f : ℝ → E) :=
  StieltjesIntegrable a b (lsmul ℝ ℝ).flip f id

noncomputable def riemannIntegral (f : ℝ → E) : E :=
  ∫⟨(lsmul ℝ ℝ).flip⟩ x in a..b, f x ∂id

theorem HasRiemannIntegral.iff_hasIntegral {a b : ℝ} (hab : a < b) (f : ℝ → E) (L : E) :
    HasRiemannIntegral a b f L ↔
      HasIntegral (Ioc a b) IntegrationParams.Riemann (fun x ↦ f (x 0))
        BoxAdditiveMap.volume L := by
    simp [HasRiemannIntegral, hab, HasStieltjesIntegral', BoxAdditiveMap.ofDiff_lsmul_eq_volume]

lemma RiemannIntegrable.def (f : ℝ → E) :
    RiemannIntegrable a b f ↔ ∃ L, HasRiemannIntegral a b f L := by rfl

lemma RiemannIntegrable.symm (f : ℝ → E) (h : RiemannIntegrable a b f) : RiemannIntegrable b a f :=
  StieltjesIntegrable.symm h

theorem RiemannIntegrable.iff_integrable {a b : ℝ} (hab : a < b) (f : ℝ → E) :
    RiemannIntegrable a b f ↔
      Integrable (Ioc a b) IntegrationParams.Riemann (fun x ↦ f (x 0)) BoxAdditiveMap.volume := by
    simp [RiemannIntegrable.def, Integrable, HasRiemannIntegral.iff_hasIntegral, hab]

end BoxIntegral
