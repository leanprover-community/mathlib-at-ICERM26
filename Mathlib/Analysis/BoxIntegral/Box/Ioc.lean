/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Box.Basic
public import Mathlib.Data.Prod.Lex

/-! # Ioc intervals as boxes

In this file we define the interval `(a, b]` as a `Box (Fin 1)`, and provide API for it

-/
@[expose] public section

namespace BoxIntegral

/-! ## One-dimensional boxes

We specialize some API for `Box` to `Box (Fin 1)`, subscripting with `₁` to indicate the
one-dimensionality.
-/

variable {a b c d : ℝ} (J K : Box (Fin 1))

/-- The left endpoint of a one-dimensional box. -/
def Box.lower₁ : ℝ := J.lower 0

/-- The right endpoint of a one-dimensional box. -/
def Box.upper₁ : ℝ := J.upper 0

lemma Box.lower_lt_upper₁ : J.lower₁ < J.upper₁ := J.lower_lt_upper 0

lemma Box.lower_le_upper₁ : J.lower₁ ≤ J.upper₁ := J.lower_le_upper 0

/-- The length of a one-dimensional box. -/
def Box.len : ℝ := J.upper₁ - J.lower₁

lemma Box.len_pos : 0 < J.len := by unfold len; linarith [J.lower_lt_upper₁]

lemma Box.len_nonneg : 0 ≤ J.len := J.len_pos.le

def Box.toSet₁ : Set ℝ := Set.Ioc J.lower₁ J.upper₁

@[simp]
lemma Box.toSet₁_def : J.toSet₁ = Set.Ioc J.lower₁ J.upper₁ := rfl

@[simp]
lemma Box.mem₁ (x : Fin 1 → ℝ) :
  x ∈ J ↔ x 0 ∈ J.toSet₁ := by simp [mem_def, lower₁, upper₁]

lemma Box.upper_mem₁ : J.upper₁ ∈ J.toSet₁ := by grind [toSet₁_def, upper₁, lower_lt_upper₁]

lemma Box.congr₁ : J = K ↔ J.lower₁ = K.lower₁ ∧ J.upper₁ = K.upper₁ :=
  ⟨ by grind, fun ⟨ hlow, hup ⟩ ↦ by ext; simp [hlow, hup] ⟩

lemma Box.le_iff₁ : J ≤ K ↔ K.lower₁ ≤ J.lower₁ ∧ J.upper₁ ≤ K.upper₁ := by
  simp [Box.le_iff_bounds, Pi.le_def, lower₁, upper₁]

lemma Box.disjoint_iff₁ {J J' : Box (Fin 1)} :
  Disjoint J.toSet J'.toSet ↔ J.upper₁ ≤ J'.lower₁ ∨ J'.upper₁ ≤ J.lower₁ := by
  simp only [Set.disjoint_left, mem_coe, mem₁, toSet₁_def, Fin.isValue, Set.mem_Ioc,
    not_and, not_le, and_imp]
  refine ⟨ fun h ↦ ?_, by grind ⟩
  specialize h (a := min J.upper J'.upper)
  simp at h; grind [lower_lt_upper₁, lower₁, upper₁]

lemma Box.disjoint_iff_disjoint₁ {J J' : Box (Fin 1)} :
  Disjoint J.toSet J'.toSet ↔ Disjoint J.toSet₁ J'.toSet₁ := by
  simp [disjoint_iff₁]; grind [lower_lt_upper₁]

/-- The closure of a one-dimensional box. -/
def Box.Icc₁ : Set ℝ := Set.Icc J.lower₁ J.upper₁

@[simp]
lemma Box.Icc₁_def : J.Icc₁ = Set.Icc J.lower₁ J.upper₁ := rfl

@[simp]
lemma Box.Icc₁_eq : J.Icc = {x | x 0 ∈ J.Icc₁ } := by
  ext; simp [Box.Icc_def, Pi.le_def, upper₁, lower₁]

lemma Box.upper_mem_Icc₁ : J.upper₁ ∈ J.Icc₁ := by grind [Icc₁_def, upper₁, lower_lt_upper₁]

lemma Box.lower_mem_Icc₁ : J.lower₁ ∈ J.Icc₁ := by grind [Icc₁_def, lower₁, lower_lt_upper₁]

lemma Box.toSet₁_subset_Icc₁ : J.toSet₁ ⊆ J.Icc₁ := by grind [toSet₁_def, Icc₁_def]

lemma Box.mem_Icc₁ (x : Fin 1 → ℝ) : x ∈ J.Icc ↔ x 0 ∈ J.Icc₁ := by simp

lemma Box.Icc₁_subset_Icc₁ {J J' : Box (Fin 1)} (h : J ≤ J') : J.Icc₁ ⊆ J'.Icc₁ := by
  grind [le_iff₁, Icc₁]

lemma Box.dist_le_len_of_mem_Icc₁ {x y : ℝ} (hx : x ∈ J.Icc₁) (hy : y ∈ J.Icc₁)
  : |x - y| ≤ J.len := by grind [len, Icc₁_def]

lemma Box.dist_lt_len_of_mem₁ {x y : ℝ} (hx : x ∈ J.toSet₁) (hy : y ∈ J.toSet₁)
  : |x - y| < J.len := by grind [len, toSet₁_def]

/--
## Ioc intervals

The interval `(a, b]` as a `Box (Fin 1)`. Returns the junk interval `(-1, 1]` if `a = b`,
and `(b, a]` if `a > b` (to give symmetry)).

Instances of `Box` are required to be non-empty, so one cannot use the empty set as the junk case.

This is analogous to `Set.Ioc` or `Finset.Ioc`, but is a distinct type from those two types. -/
noncomputable def Ioc (a b : ℝ) : Box (Fin 1) :=
  if h : a = b then ⟨ -1, 1, fun _ ↦ by norm_num ⟩
  else ⟨ fun _ ↦ min a b, fun _ ↦ max a b, fun _ ↦ by grind ⟩

lemma Ioc.of_lt (h : a < b) : Ioc a b = ⟨ fun _ ↦ a, fun _ ↦ b, fun _ ↦ h ⟩ := by
  simp [Ioc, h.ne, h.le]

lemma Ioc.of_gt (h : b < a) : Ioc a b = ⟨ fun _ ↦ b, fun _ ↦ a, fun _ ↦ h ⟩ := by
  simp [Ioc, h.ne.symm, h.le]

lemma Ioc.of_eq : Ioc a a = ⟨ fun _ ↦ -1, fun _ ↦ 1, fun _ ↦ by norm_num ⟩ := by
  simp [Ioc]; aesop

@[simp]
lemma Ioc.upper (h : a < b) (i : Fin 1) : (Ioc a b).upper i = b := by simp [h, of_lt]

@[simp]
lemma Ioc.upper₁ (h : a < b) : (Ioc a b).upper₁ = b := Ioc.upper h 0

@[simp]
lemma Ioc.lower (h : a < b) (i : Fin 1) : (Ioc a b).lower i = a := by simp [h, of_lt]

@[simp]
lemma Ioc.lower₁ (h : a < b) : (Ioc a b).lower₁ = a := Ioc.lower h 0

@[simp]
lemma Ioc.len (h : a < b) : (Ioc a b).len = b - a := by simp [Box.len, h]

@[simp]
lemma Ioc.upper_gt (h : b < a) (i : Fin 1) : (Ioc a b).upper i = a := by simp [h, of_gt]

@[simp]
lemma Ioc.upper_gt₁ (h : b < a) : (Ioc a b).upper₁ = a := Ioc.upper_gt h 0

@[simp]
lemma Ioc.lower_gt (h : b < a) (i : Fin 1) : (Ioc a b).lower i = b := by simp [h, of_gt]

@[simp]
lemma Ioc.lower_gt₁ (h : b < a) : (Ioc a b).lower₁ = b := Ioc.lower_gt h 0

@[simp]
lemma Ioc.len_gt (h : b < a) : (Ioc a b).len = a - b := by simp [Box.len, h]

lemma Ioc.symm : Ioc a b = Ioc b a := by
  by_cases! h : a = b
  · simp [h]
  simp [Ioc]; grind

lemma Box.eq_Ioc (J : Box (Fin 1)) : J = Ioc J.lower₁ J.upper₁ := by
  ext; simp [mem₁, Ioc.of_lt J.lower_lt_upper₁]

lemma mem_Ioc (hab : a < b) (x : Fin 1 → ℝ) : x ∈ Ioc a b ↔ x 0 ∈ Set.Ioc a b := by simp [hab]

@[simp]
lemma Ioc_le_Ioc_iff (hab : a < b) (hcd : c < d) : Ioc c d ≤ Ioc a b ↔ a ≤ c ∧ d ≤ b := by
  simp [Box.le_iff₁, hab, hcd]

lemma Icc_of_Ioc (hab : a < b) : Box.Icc (Ioc a b) = { x | x 0 ∈ Set.Icc a b } := by simp [hab]

lemma Box.le_Ioc_iff (hab : a < b) (J : Box (Fin 1)) :
  J ≤ Ioc a b ↔ a ≤ J.lower₁ ∧ J.upper₁ ≤ b := by simp [Box.le_iff₁, hab]

lemma Box.ge_Ioc_iff (hab : a < b) (J : Box (Fin 1)) :
  Ioc a b ≤ J ↔ J.lower₁ ≤ a ∧ b ≤ J.upper₁ := by simp [Box.le_iff₁, hab]

lemma Box.mem_of_le (hab : a < b) {J : Box (Fin 1)} (hJ : J ≤ Ioc a b) :
  J.lower₁ ∈ Set.Icc a b ∧ J.upper₁ ∈ Set.Icc a b := by
  have := J.lower_lt_upper₁
  grind [le_Ioc_iff]

lemma Icc_subset_of_box_le_Ioc {a b : ℝ} {J : Box (Fin 1)} (hab : a < b) (hJ : J ≤ Ioc a b) :
    J.Icc₁ ⊆ Set.Icc a b := by simp; grind [Box.le_Ioc_iff]

/-! ## Mapping an interval -/

variable (φ : ℝ → ℝ)

noncomputable def Ioc.comp (J : Box (Fin 1)) := Ioc (φ J.lower₁) (φ J.upper₁)

@[simp]
lemma Ioc.comp_apply (hab : a < b) : comp φ (Ioc a b) = Ioc (φ a) (φ b) := by simp [comp, hab]

/-- The map `Ioc.comp φ` is injective on any set of boxes contained in `Ioc a b`, provided `φ` is
strictly monotone on `[a, b]`. -/
lemma Ioc.comp_injOn_of_strictMonoOn {φ : ℝ → ℝ} {S : Set (Box (Fin 1))}
    (hab : a < b) (hS : ∀ J ∈ S, J ≤ Ioc a b) (hmono : StrictMonoOn φ (Set.Icc a b)) :
    Set.InjOn (Ioc.comp φ) S := by
  intro I hI J hJ hIJ
  have hI' := Box.mem_of_le hab (hS I hI)
  have hJ' := Box.mem_of_le hab (hS J hJ)
  have hIlt := hmono hI'.1 hI'.2 I.lower_lt_upper₁
  have hJlt := hmono hJ'.1 hJ'.2 J.lower_lt_upper₁
  rw [Box.congr₁]; refine ⟨hmono.injOn hI'.1 hJ'.1 ?_, hmono.injOn hI'.2 hJ'.2 ?_⟩
  · simpa [Ioc.comp, hIlt, hJlt] using congrArg Box.lower₁ hIJ
  · simpa [Ioc.comp, hIlt, hJlt] using congrArg Box.upper₁ hIJ

end BoxIntegral
