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

/-! ## Intervals -/

variable {a b c d : ℝ}

def Box.lower₁ (J : Box (Fin 1)) : ℝ := J.lower 0

def Box.upper₁ (J : Box (Fin 1)) : ℝ := J.upper 0

lemma Box.lower_lt_upper₁ (J : Box (Fin 1)) : J.lower₁ < J.upper₁ := J.lower_lt_upper 0

def Box.toSet₁ (J : Box (Fin 1)) : Set ℝ := Set.Ioc J.lower₁ J.upper₁

@[simp]
lemma Box.toSet₁_def (J : Box (Fin 1)) :
    J.toSet₁ = Set.Ioc J.lower₁ J.upper₁ := rfl

@[simp]
lemma Box.mem₁ (x : Fin 1 → ℝ) (J : Box (Fin 1)) :
  x ∈ J ↔ x 0 ∈ J.toSet₁ := by simp [mem_def, lower₁, upper₁]

lemma Box.congr₁ (J K : Box (Fin 1)) :
    J = K ↔ J.lower₁ = K.lower₁ ∧ J.upper₁ = K.upper₁ :=
  ⟨ by grind, fun ⟨ hlow, hup ⟩ ↦ by ext; simp [hlow, hup] ⟩

lemma Box.le_iff₁ (J K : Box (Fin 1)) :
    J ≤ K ↔ K.lower₁ ≤ J.lower₁ ∧ J.upper₁ ≤ K.upper₁ := by
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

def Box.Icc₁ (J : Box (Fin 1)) : Set ℝ := Set.Icc J.lower₁ J.upper₁

@[simp]
lemma Box.Icc₁_def (J : Box (Fin 1)) :
    J.Icc₁ = Set.Icc J.lower₁ J.upper₁ := rfl

@[simp]
lemma Box.Icc₁_eq (J : Box (Fin 1)) : J.Icc = {x | x 0 ∈ J.Icc₁ } := by
  ext; simp [Box.Icc_def, Pi.le_def, upper₁, lower₁]

lemma Box.mem_Icc₁ (x : Fin 1 → ℝ) (J : Box (Fin 1)) :
    x ∈ J.Icc ↔ x 0 ∈ J.Icc₁ := by simp


/-- The interval `(a, b]` as a `Box (Fin 1)`. Returns the junk interval `(-1, 1]` if `a = b`,
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
lemma Ioc.upper_gt (h : b < a) (i : Fin 1) : (Ioc a b).upper i = a := by simp [h, of_gt]

@[simp]
lemma Ioc.upper_gt₁ (h : b < a) : (Ioc a b).upper₁ = a := Ioc.upper_gt h 0

@[simp]
lemma Ioc.lower_gt (h : b < a) (i : Fin 1) : (Ioc a b).lower i = b := by simp [h, of_gt]

@[simp]
lemma Ioc.lower_gt₁ (h : b < a) : (Ioc a b).lower₁ = b := Ioc.lower_gt h 0

lemma Ioc.symm : Ioc a b = Ioc b a := by
  by_cases! h : a = b
  · simp [h]
  simp [Ioc]; grind

lemma Box.eq_Ioc (J : Box (Fin 1)) : J = Ioc J.lower₁ J.upper₁ := by
  ext
  rw [Ioc.of_lt J.lower_lt_upper₁]
  simp [mem₁]

lemma mem_Ioc (hab : a < b) (x : Fin 1 → ℝ) : x ∈ Ioc a b ↔ x 0 ∈ Set.Ioc a b := by
  simp [hab]

@[simp]
lemma Ioc_le_Ioc_iff (hab : a < b) (hcd : c < d) : Ioc c d ≤ Ioc a b ↔ a ≤ c ∧ d ≤ b := by
  simp [Box.le_iff₁, hab, hcd]

lemma Icc_of_Ioc (hab : a < b) : Box.Icc (Ioc a b) = { x | x 0 ∈ Set.Icc a b } := by
  simp [hab]

lemma Box.le_Ioc_iff (hab : a < b) (J : Box (Fin 1)) :
  J ≤ Ioc a b ↔ a ≤ J.lower₁ ∧ J.upper₁ ≤ b := by
  simp [Box.le_iff₁, hab]

lemma Box.ge_Ioc_iff (hab : a < b) (J : Box (Fin 1)) :
  Ioc a b ≤ J ↔ J.lower₁ ≤ a ∧ b ≤ J.upper₁ := by
  simp [Box.le_iff₁, hab]

lemma Box.mem_of_le (hab : a < b) {J : Box (Fin 1)} (hJ : J ≤ Ioc a b) :
  J.lower₁ ∈ Set.Icc a b ∧ J.upper₁ ∈ Set.Icc a b := by
  rw [le_Ioc_iff hab] at hJ
  have := J.lower_lt_upper₁
  grind


/-! ## Mapping or reflecting an interval -/

variable (φ : ℝ → ℝ)

noncomputable def Ioc.comp (J : Box (Fin 1)) := Ioc (φ J.lower₁) (φ J.upper₁)

@[simp]
lemma Ioc.comp_apply (hab : a < b) : comp φ (Ioc a b) = Ioc (φ a) (φ b) := by
  simp [comp, hab]

noncomputable def Ioc.reflect (J : Box (Fin 1)) := Ioc (-J.upper₁) (-J.lower₁)

@[simp]
lemma Ioc.reflect_upper (J : Box (Fin 1)) : (reflect J).upper₁ = -J.lower₁ := by
  have : -J.upper₁ < -J.lower₁ := by grind [Box.lower_lt_upper₁]
  simp [reflect, this]

@[simp]
lemma Ioc.reflect_lower (J : Box (Fin 1)) : (reflect J).lower₁ = -J.upper₁ := by
  have : -J.upper₁ < -J.lower₁ := by grind [Box.lower_lt_upper₁]
  simp [reflect, this]

@[simp]
lemma Ioc.reflect_reflect (J : Box (Fin 1)) : reflect (reflect J) = J := by
  simp [Box.congr₁]

@[simp]
lemma Ioc.reflect_eq : reflect (Ioc a b) = Ioc (-b) (-a) := by
  rcases lt_trichotomy a b with (hab | rfl | hab)
  · simp [reflect, hab]
  · simp [reflect, Ioc, Box.upper₁, Box.lower₁]; aesop
  simp [reflect, hab, symm]


/-! ## Lexicographic ordering of one-dimensional boxes -/

def Box.lexKey (J : Box (Fin 1)) : ℝ ×ₗ ℝ :=
  toLex (J.lower₁, J.upper₁)

lemma Box.lexKey_injective : Function.Injective Box.lexKey := by
  intro J K h
  simpa [Box.lexKey, Box.congr₁] using h

def Box.lex_le (J K : Box (Fin 1)) : Prop :=
  Box.lexKey J ≤ Box.lexKey K

noncomputable instance Box.instDecidableLexLe : DecidableRel Box.lex_le := by
  classical
  infer_instance

instance Box.instIsTransLexLe : IsTrans _ lex_le := ⟨fun _ _ _ ↦ le_trans⟩

instance Box.instIsAntisymmLexLe : Std.Antisymm lex_le :=
  ⟨fun _ _ h₁ h₂ ↦ lexKey_injective (le_antisymm h₁ h₂)⟩

instance Box.instIsTotalLexLe : Std.Total lex_le :=
  ⟨fun _ _ ↦ le_total _ _⟩

instance Box.instIsReflLexLe : Std.Refl lex_le :=
  ⟨fun _ ↦ le_rfl⟩

/-- Disjoint one-dimensional boxes have disjoint underlying real half-open intervals. -/
lemma disjoint_Ioc_of_disjoint_box {J K : Box (Fin 1)}
    (h : Disjoint J.toSet K) :
    Disjoint (Set.Ioc (J.lower₁) (J.upper₁)) (Set.Ioc (K.lower₁) (K.upper₁)) := by
  simp [Box.disjoint_iff₁, Set.Ioc_disjoint_Ioc] at h ⊢
  grind

/-- If two disjoint one-dimensional boxes are ordered by lower endpoint, then the first lies to the
left of the second. -/
lemma upper_le_lower_of_disjoint_box_of_lower_le {J K : Box (Fin 1)}
    (hdisj : Disjoint J.toSet K) (hlower : J.lower₁ ≤ K.lower₁) :
    J.upper₁ ≤ K.lower₁ := by
  simp [Box.disjoint_iff₁] at hdisj
  grind [Box.lower_lt_upper₁]

lemma Icc_subset_of_box_le_Ioc {J : Box (Fin 1)} (hab : a < b) (hJ : J ≤ Ioc a b) :
    J.Icc₁ ⊆ Set.Icc a b := by
  simp; grind [Box.le_Ioc_iff]

end BoxIntegral
