/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Box.Ioc
public import Mathlib.Analysis.BoxIntegral.Partition.Additive

/-! # One-dimensional partitions

This file defines some basic API for one-dimensional partitions.
-/

@[expose] public section

namespace BoxIntegral

open Prepartition Finset

/-! ## One-dimensional mesh size -/

/-- In one dimension, the mesh size simplifies to the longest length of an interval
in the partition. -/
theorem mesh_size₁ {I : Box (Fin 1)} (π : Prepartition I) : π.mesh_size
    = π.boxes.sup (fun B ↦ NNReal.mk (B.upper₁ - B.lower₁) (by linarith [B.lower_lt_upper₁]))
    := by simp [mesh_size]; congr

@[simp]
theorem mesh_size_le_iff₁ {I : Box (Fin 1)} (π : Prepartition I) (ε : NNReal) :
    π.mesh_size ≤ ε ↔ ∀ B ∈ π.boxes, B.upper₁ - B.lower₁ ≤ ε := by
  simp [mesh_size_le_iff, Box.upper₁, Box.lower₁]

namespace Prepartition

/-! ## Evenly spaced partitions
-/

/-- We use a bundled `Even` class to represent an evenly spaced partition of an interval
`Ioc a b` into `N` equally spaced subintervals, arranged in a grid.
-/
class Even where
  a : ℝ
  b : ℝ
  N : ℤ
  hab : a < b
  hN : 0 < N

namespace Even

variable (e : Even)

theorem b_sub_a_pos : 0 < e.b - e.a := by linarith [e.hab]

/-- We use `δ` to denote the spacing of the grid. -/
noncomputable def δ : ℝ := (e.b - e.a) / e.N

theorem delta_pos : 0 < e.δ := div_pos e.b_sub_a_pos (by exact_mod_cast e.hN)

/-- The grid points of the partition. -/
noncomputable def grid : ℤ → ℝ := (e.a + · * e.δ)

@[simp]
theorem grid_zero : e.grid 0 = e.a := by simp [grid]

@[simp]
theorem grid_N : e.grid (e.N) = e.b := by have := e.hN; simp [grid, δ]; field_simp; abel

theorem grid_succ_eq (n : ℤ) : e.grid (n + 1) = e.grid n + e.δ := by simp [grid]; ring

theorem grid_succ_gt (n : ℤ) : e.grid (n + 1) > e.grid n := by
  linarith [e.grid_succ_eq n, e.delta_pos]

theorem grid_strictMono : StrictMono e.grid :=
  fun _ _ h ↦ by simp [grid, add_lt_add_iff_left, mul_lt_mul_iff_left₀ e.delta_pos, h]

theorem grid_mono : Monotone e.grid := e.grid_strictMono.monotone

@[simp]
theorem a_le_grid_iff (n : ℤ) : e.a ≤ e.grid n ↔ 0 ≤ n := by
  simp [←grid_zero, e.grid_strictMono.le_iff_le]

@[simp]
theorem a_lt_grid_iff (n : ℤ) : e.a < e.grid n ↔ 0 < n := by
  simp [←grid_zero, e.grid_strictMono.lt_iff_lt]

@[simp]
theorem grid_le_b_iff (n : ℤ) : e.grid n ≤ e.b ↔ n ≤ e.N := by
  simp [←grid_N, e.grid_strictMono.le_iff_le]

@[simp]
theorem grid_lt_b_iff (n : ℤ) : e.grid n < e.b ↔ n < e.N := by
  simp [←grid_N, e.grid_strictMono.lt_iff_lt]

theorem grid_mem_Ioc_iff (n : ℤ) : e.grid n ∈ Set.Ioc e.a e.b ↔ n ∈ Set.Ioc 0 e.N := by
  simp

theorem grid_mem_Ioo_iff (n : ℤ) : e.grid n ∈ Set.Ioo e.a e.b ↔ n ∈ Set.Ioo 0 e.N := by
  simp

theorem grid_mem_Ico_iff (n : ℤ) : e.grid n ∈ Set.Ico e.a e.b ↔ n ∈ Set.Ico 0 e.N := by
  simp

theorem grid_mem_Icc_iff (n : ℤ) : e.grid n ∈ Set.Icc e.a e.b ↔ n ∈ Set.Icc 0 e.N := by
  simp

/-- The index set for the partition. -/
noncomputable def indices := Finset.Ico 0 e.N

instance indices_nonempty : Nonempty e.indices := ⟨ 0, by simp [indices, hN] ⟩

theorem Ioc_subset_Ioc {n : ℤ} (hn : n ∈ e.indices) :
  Set.Ioc (e.grid n) (e.grid (n + 1)) ⊆ .Ioc e.a e.b := by
  simp [indices] at hn
  apply Set.Ioc_subset_Ioc (by simp; grind) (by simp; grind)

theorem Ioo_subset_Ioo {n : ℤ} (hn : n ∈ e.indices) :
  Set.Ioo (e.grid n) (e.grid (n + 1)) ⊆ .Ioo e.a e.b := by
  simp [indices] at hn
  apply Set.Ioo_subset_Ioo (by simp; grind) (by simp; grind)

theorem Ico_subset_Ico {n : ℤ} (hn : n ∈ e.indices) :
  Set.Ico (e.grid n) (e.grid (n + 1)) ⊆ .Ico e.a e.b := by
  simp [indices] at hn
  apply Set.Ico_subset_Ico (by simp; grind) (by simp; grind)

theorem Icc_subset_Icc {n : ℤ} (hn : n ∈ e.indices) :
  Set.Icc (e.grid n) (e.grid (n + 1)) ⊆ .Icc e.a e.b := by
  simp [indices] at hn
  apply Set.Icc_subset_Icc (by simp; grind) (by simp; grind)

/-- The box representing the entire interval. -/
noncomputable def box := Ioc e.a e.b

@[simp]
theorem box_lower₁ : e.box.lower₁ = e.a := by simp [box, hab]

@[simp]
theorem box_upper₁ : e.box.upper₁ = e.b := by simp [box, hab]

/-- The grid boxes comprising the partition. -/
noncomputable def gridbox : ℤ → Box (Fin 1) := fun n ↦ Ioc (e.grid n) (e.grid (n + 1))

@[simp]
theorem gridbox_upper (n : ℤ) : (e.gridbox n).upper₁ = e.grid (n + 1) := by
  simp [gridbox, grid_succ_gt]

@[simp]
theorem gridbox_lower (n : ℤ) : (e.gridbox n).lower₁ = e.grid n := by
  simp [gridbox, grid_succ_gt]

theorem gridbox_Icc₁ (n : ℕ) : (e.gridbox n).Icc₁ = Set.Icc (e.grid n) (e.grid (n + 1)) := by simp

theorem gridbox_toSet₁ (n : ℕ) : (e.gridbox n).toSet₁ = Set.Ioc (e.grid n) (e.grid (n + 1)) :=
  by simp

theorem gridbox_le_box {n : ℤ} (hn : n ∈ e.indices) : e.gridbox n ≤ e.box := by
  simpa [gridbox, box, Ioc_le_Ioc_iff, e.hab, e.grid_succ_gt n, indices] using hn

noncomputable def index : ℝ → ℤ := fun x ↦ ⌈(x - e.a) / e.δ⌉ - 1

theorem grid_lt_iff (x : ℝ) (n : ℤ) : e.grid n < x ↔ n ≤ e.index x := by
  have := e.delta_pos
  simp [index, grid, Int.le_sub_one_iff, Int.lt_ceil]; field_simp; grind

theorem grid_index_lt (x : ℝ) : e.grid (e.index x) < x := by simp [grid_lt_iff]

theorem le_grid_iff (x : ℝ) (n : ℤ) : x ≤ e.grid n ↔ e.index x < n := by
  have := e.delta_pos
  simp [index, grid, Int.sub_one_lt_iff, Int.ceil_le]; field_simp; grind

theorem le_grid_succ_index (x : ℝ) : x ≤ e.grid (e.index x + 1) := by simp [le_grid_iff]

theorem mem_gridbox_iff₁ (x : ℝ) (n : ℤ) : x ∈ (e.gridbox n).toSet₁ ↔ e.index x = n := by
  simp [grid_lt_iff, le_grid_iff]; omega

theorem mem_gridbox_iff (x : Fin 1 → ℝ) (n : ℤ) : x ∈ e.gridbox n ↔ e.index (x 0) = n := by
  simp [grid_lt_iff, le_grid_iff]; omega

theorem mem_box_iff (x : ℝ) : x ∈ e.box.toSet₁ ↔ e.index x ∈ e.indices := by
  simp [indices, ←grid_zero, ←grid_N, grid_lt_iff, le_grid_iff]

open Classical in
noncomputable def toPrepartition : Prepartition e.box :=
  {
    boxes := (e.indices).image e.gridbox
    le_of_mem' J hJ := by
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hJ
      exact e.gridbox_le_box hj
    pairwiseDisjoint I hI J hJ hdisj := by
      simp only [coe_image, Set.mem_image] at hI hJ
      obtain ⟨i, hi, rfl⟩ := hI
      obtain ⟨j, hj, rfl⟩ := hJ
      simp [Box.disjoint_iff₁, e.grid_strictMono.le_iff_le]
      grind
  }

theorem toPrepartition_isPartition : (e.toPrepartition).IsPartition := by
  intro x hx
  simp [box, hab] at hx
  sorry

@[simp]
theorem mem_toPrepartition_iff (J : Box (Fin 1)) :
    J ∈ e.toPrepartition ↔ ∃ n ∈ e.indices, e.gridbox n = J := by simp [toPrepartition]

@[simp]
theorem forall_in_set_const {p : Prop} {α : Type*} (S : Set α) [Nonempty S] : (∀ x ∈ S, p) ↔ p :=
  by aesop

@[simp]
theorem forall_in_finset_const {p : Prop} {α : Type*} (S : Finset α) [Nonempty S] :
  (∀ x ∈ S, p) ↔ p := by aesop

theorem mesh_size_toPrepartition : (e.toPrepartition).mesh_size = e.δ.toNNReal
  := by
  apply eq_of_forall_ge_iff
  intro ε
  simp only [mesh_size_le_iff₁, toPrepartition, mem_image, tsub_le_iff_right, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, gridbox_upper, gridbox_lower, grid_succ_eq, add_comm _ e.δ,
    add_le_add_iff_right, forall_in_finset_const, Real.toNNReal_le_iff_le_coe]

end Even

end Prepartition

end BoxIntegral
