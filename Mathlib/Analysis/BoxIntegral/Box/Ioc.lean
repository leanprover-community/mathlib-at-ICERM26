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
lemma Ioc.lower (h : a < b) (i : Fin 1) : (Ioc a b).lower i = a := by simp [h, of_lt]

@[simp]
lemma Ioc.upper_gt (h : b < a) (i : Fin 1) : (Ioc a b).upper i = a := by simp [h, of_gt]

@[simp]
lemma Ioc.lower_gt (h : b < a) (i : Fin 1) : (Ioc a b).lower i = b := by simp [h, of_gt]

lemma Ioc.symm : Ioc a b = Ioc b a := by
  by_cases! h : a = b
  · simp [h]
  simp [Ioc]; grind

lemma Box.eq_Ioc (J : Box (Fin 1)) : J = Ioc (J.lower 0) (J.upper 0) := by
  ext
  rw [Ioc.of_lt (J.lower_lt_upper 0)]
  simp [Box.mem_def]

lemma Box.mem_fin_one (x : Fin 1 → ℝ) (J : Box (Fin 1)) :
  x ∈ J ↔ J.lower 0 < x 0 ∧ x 0 ≤ J.upper 0 := by
  simp [Box.mem_def]

lemma Box.congr_fin_one (J K : Box (Fin 1)) :
  J = K ↔ J.lower 0 = K.lower 0 ∧ J.upper 0 = K.upper 0 := by
  refine ⟨ by grind, fun ⟨ hlow, hup ⟩ ↦ ?_ ⟩
  ext x; simp [Box.mem_fin_one, hlow, hup]

@[simp]
lemma mem_Ioc (hab : a < b) (x : Fin 1 → ℝ) : x ∈ Ioc a b ↔ a < x 0 ∧ x 0 ≤ b := by
  simp [Box.mem_def, hab, Ioc.of_lt]

@[simp]
lemma Ioc_le_Ioc_iff (hab : a < b) (hcd : c < d) :
    Ioc c d ≤ Ioc a b ↔ a ≤ c ∧ d ≤ b := by
  rw [Ioc.of_lt hab, Ioc.of_lt hcd]
  simp [Box.le_iff_bounds, Pi.le_def]

lemma mem_Icc_fin_one (x : Fin 1 → ℝ) (J : Box (Fin 1)) :
    x ∈ Box.Icc J ↔ J.lower 0 ≤ x 0 ∧ x 0 ≤ J.upper 0 := by simp [Box.Icc_def, Pi.le_def]

@[simp]
lemma Icc_of_Ioc (hab : a < b) : Box.Icc (Ioc a b) = { x | x 0 ∈ Set.Icc a b } := by
  simp only [Box.Icc_def, Fin.isValue, Set.mem_Icc]; ext x
  simp [Pi.le_def, Ioc.lower hab, Ioc.upper hab]

lemma Ioc.le_Ioc_iff (hab : a < b) (hcd : c < d) :
  Ioc c d ≤ Ioc a b ↔ a ≤ c ∧ d ≤ b := by
  simp [Box.le_iff_bounds, Pi.le_def, hab, hcd]

lemma Box.le_Ioc_iff (hab : a < b) (J : Box (Fin 1)) :
  J ≤ Ioc a b ↔ a ≤ J.lower 0 ∧ J.upper 0 ≤ b := by
  nth_rw 1 [J.eq_Ioc]
  exact Ioc.le_Ioc_iff hab (J.lower_lt_upper 0)

lemma Box.ge_Ioc_iff (hab : a < b) (J : Box (Fin 1)) :
  Ioc a b ≤ J ↔ J.lower 0 ≤ a ∧ b ≤ J.upper 0 := by
  nth_rw 1 [J.eq_Ioc]
  exact Ioc.le_Ioc_iff (J.lower_lt_upper 0) hab

lemma Box.mem_of_le (hab : a < b) {J : Box (Fin 1)} (hJ : J ≤ Ioc a b) :
  J.lower 0 ∈ Set.Icc a b ∧ J.upper 0 ∈ Set.Icc a b := by
  rw [le_Ioc_iff hab] at hJ
  have := J.lower_lt_upper 0
  grind

lemma Box.disjoint_iff {J J' : Box (Fin 1)} :
  Disjoint J.toSet J'.toSet ↔ J.upper 0 ≤ J'.lower 0 ∨ J'.upper 0 ≤ J.lower 0 := by
  have := J.lower_lt_upper 0
  have := J'.lower_lt_upper 0
  rw [← not_iff_not]
  simp only [Set.not_disjoint_iff_nonempty_inter, Fin.isValue, not_or, not_le]
  refine ⟨ fun h ↦ ?_, fun h ↦ ?_ ⟩
  · obtain ⟨ x, hx ⟩ := h
    simp [Box.mem_def] at hx
    grind
  use min J.upper J'.upper
  simp [Box.mem_def, h]

/-! ## Mapping or reflecting an interval -/

variable (φ : ℝ → ℝ)

noncomputable def Ioc.comp (J : Box (Fin 1)) := Ioc (φ (J.lower 0)) (φ (J.upper 0))

@[simp]
lemma Ioc.comp_apply (hab : a < b) : comp φ (Ioc a b) = Ioc (φ a) (φ b) := by
  simp [comp, hab]

noncomputable def Ioc.reflect (J : Box (Fin 1)) := Ioc (-J.upper 0) (-J.lower 0)

@[simp]
lemma Ioc.reflect_upper (J : Box (Fin 1)) : (reflect J).upper 0 = -J.lower 0 := by
  simp [reflect]

@[simp]
lemma Ioc.reflect_lower (J : Box (Fin 1)) : (reflect J).lower 0 = -J.upper 0 := by
  simp [reflect]

@[simp]
lemma Ioc.reflect_reflect (J : Box (Fin 1)) : reflect (reflect J) = J := by
  ext; simp [reflect, Box.mem_fin_one]

@[simp]
lemma Ioc.reflect_eq : reflect (Ioc a b) = Ioc (-b) (-a) := by
  rcases lt_trichotomy a b with (hab | rfl | hab)
  · simp [reflect, hab]
  · simp [reflect, Ioc]; aesop
  simp [reflect, hab, symm]

def boxLexKey (J : Box (Fin 1)) : ℝ ×ₗ ℝ :=
  toLex (J.lower 0, J.upper 0)

lemma boxLexKey_injective : Function.Injective boxLexKey := by
  intro J K h
  simpa [boxLexKey, Box.congr_fin_one] using h

instance instIsTransBoxLexKey :
    IsTrans (Box (Fin 1)) (fun J K ↦ boxLexKey J ≤ boxLexKey K) :=
  ⟨fun _ _ _ ↦ le_trans⟩

instance instIsAntisymmBoxLexKey :
    Std.Antisymm (fun J K ↦ boxLexKey J ≤ boxLexKey K) :=
  ⟨fun _ _ h₁ h₂ ↦ boxLexKey_injective (le_antisymm h₁ h₂)⟩

instance instIsTotalBoxLexKey :
    Std.Total (fun J K ↦ boxLexKey J ≤ boxLexKey K) :=
  ⟨fun _ _ ↦ le_total _ _⟩

instance instIsReflBoxLexKey :
    Std.Refl (fun J K ↦ boxLexKey J ≤ boxLexKey K) :=
  ⟨fun _ ↦ le_rfl⟩

/-- Disjoint one-dimensional boxes have disjoint underlying real half-open intervals. -/
lemma disjoint_Ioc_of_disjoint_box {J K : Box (Fin 1)}
    (h : Disjoint J.toSet K) :
    Disjoint (Set.Ioc (J.lower 0) (J.upper 0)) (Set.Ioc (K.lower 0) (K.upper 0)) := by
  rw [Set.disjoint_left]
  intro x hxJ hxK
  let x' : Fin 1 → ℝ := fun _ ↦ x
  exact h.le_bot ⟨show x' ∈ J by simpa [Box.mem_def] using hxJ,
    by simpa [Box.mem_def] using hxK⟩

/-- If two disjoint one-dimensional boxes are ordered by lower endpoint, then the first lies to the
left of the second. -/
lemma upper_le_lower_of_disjoint_box_of_lower_le {J K : Box (Fin 1)}
    (hdisj : Disjoint J.toSet K) (hlower : J.lower 0 ≤ K.lower 0) :
    J.upper 0 ≤ K.lower 0 := by
  have := disjoint_Ioc_of_disjoint_box hdisj
  have := K.lower_lt_upper 0
  grind [Set.Ioc_disjoint_Ioc]

end BoxIntegral
