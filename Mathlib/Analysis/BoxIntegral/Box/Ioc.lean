/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Box.Basic

/-! # Ioc intervals as boxes

In this file we define the interval `(a, b]` as a `Box (Fin 1)`, and provide API for it

-/
@[expose] public section

namespace BoxIntegral

/-! ## Intervals -/

/-- The interval `(a, b]` as a `Box (Fin 1)`. Returns the junk interval `(0, 1]` if `a ≥ b`.

Instances of `Box` are required to be non-empty, so one cannot use the empty set as the junk case.

This is analogous to `Set.Ioc` or `Finset.Ioc`, but is a distinct type from those two types. -/
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
lemma Ioc.upper {a b : ℝ} (h : a < b) (i : Fin 1) : (Ioc a b).upper i = b := by simp [Ioc, h]

@[simp]
lemma Ioc.lower {a b : ℝ} (h : a < b) (i : Fin 1) : (Ioc a b).lower i = a := by simp [Ioc, h]

lemma Box.eq_Ioc (J : Box (Fin 1)) : J = Ioc (J.lower 0) (J.upper 0) := by
  ext
  simp [Ioc, Box.mem_def]

@[simp]
lemma mem_Ioc {a b : ℝ} (hab : a < b) (x : Fin 1 → ℝ) : x ∈ Ioc a b ↔ a < x 0 ∧ x 0 ≤ b := by
  simp [Box.mem_def, Ioc.upper hab, Ioc.lower hab]

@[simp]
lemma Ioc_le_Ioc_iff {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Ioc c d ≤ Ioc a b ↔ a ≤ c ∧ d ≤ b := by
  simp [Ioc, hab, hcd, Box.le_iff_bounds, Pi.le_def]

@[simp]
lemma Icc_of_Ioc {a b : ℝ} (hab : a < b) : Box.Icc (Ioc a b) = { x | x 0 ∈ Set.Icc a b } := by
  simp only [Box.Icc_def, Fin.isValue, Set.mem_Icc]; ext x
  simp [Pi.le_def, Ioc.lower hab, Ioc.upper hab]
  
end BoxIntegral
