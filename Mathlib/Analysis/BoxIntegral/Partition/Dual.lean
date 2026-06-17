/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.OrderedDivision

/-! # Dual tagged divisions

This file defines the dual tagged division used for finite summation by parts.
-/

@[expose] public section

namespace BoxIntegral
namespace TaggedDivision

/-! ## Dual tagged divisions -/

namespace dual

/-- The division points of the dual tagged division used in summation by parts: it inserts the
tags of `π` between the two endpoints. -/
def x (π : TaggedDivision) : Fin (π.N + 2) → ℝ :=
  Fin.cons (π.x 0) (Fin.snoc π.tag (π.x (Fin.last π.N)))

@[simp]
theorem x_first (π : TaggedDivision) : x π 0 = π.x 0 := by
  simp [x]

@[simp]
theorem x_last (π : TaggedDivision) : x π (Fin.last (π.N + 1)) = π.x (Fin.last π.N) := by
  simp [x]

end dual

/-- The dual tagged division used for finite summation by parts. Its division points are the
original endpoints and tags, and its tags are the original division points. -/
def dual (π : TaggedDivision) : TaggedDivision where
  N := π.N + 1
  tag := π.x
  x := dual.x π

@[simp]
theorem dual_first (π : TaggedDivision) : π.dual.x 0 = π.x 0 := by
  exact dual.x_first π

@[simp]
theorem dual_last (π : TaggedDivision) :
    π.dual.x (Fin.last π.dual.N) = π.x (Fin.last π.N) := by
  exact dual.x_last π

/-- The dual tagged division has valid tags whenever the original tagged division does. -/
theorem dual_validTags (π : TaggedDivision) (hπ : π.ValidTags) :
    π.dual.ValidTags := by
  sorry

/-- The coarseness of the dual partition is controlled by the coarseness of the original partition:
its mesh size is at most twice the original mesh size. -/
theorem dual_mesh_size_le_two_mul
    {a b : ℝ} (π : TaggedDivision) (hπ_tag : π.ValidTags)
    (ha : π.x 0 = a) (hb : π.x (Fin.last π.N) = b) :
    (π.dual.toTaggedPrepartition (π.dual_validTags hπ_tag)
      (π.dual_first.trans ha)
      (π.dual_last.trans hb)).mesh_size ≤
      2 * (π.toTaggedPrepartition hπ_tag ha hb).mesh_size := by
  sorry

end TaggedDivision

namespace TaggedPrepartition

/-! ## Dual tagged prepartitions -/

variable {a b : ℝ}

/-- The unordered tagged prepartition associated to the dual of a Henstock partition of
`Ioc a b`. This is the tagged-prepartition version of `TaggedDivision.dual`, obtained by
ordering the original partition, dualizing it, and forgetting the ordering again. -/
noncomputable def dual (π : TaggedPrepartition (Ioc a b)) (hab : a < b)
    (hπ_hen : π.IsHenstock) (hπ_part : π.IsPartition) :
    TaggedPrepartition (Ioc a b) := by
  let ρ := π.toTaggedDivision
  have hρ : ρ.ValidTags := π.toTaggedDivision_validTags hπ_hen hπ_part
  exact ρ.dual.toTaggedPrepartition (ρ.dual_validTags hρ)
    (by simpa using ρ.dual_first.trans (π.toTaggedDivision_first hab hπ_part))
    (by simpa using ρ.dual_last.trans (π.toTaggedDivision_last hab hπ_part))

/-- The dual of a Henstock partition is Henstock. -/
theorem dual_isHenstock (π : TaggedPrepartition (Ioc a b)) (hab : a < b)
    (hπ_hen : π.IsHenstock) (hπ_part : π.IsPartition) :
    (π.dual hab hπ_hen hπ_part).IsHenstock := by
  dsimp [dual]
  apply TaggedDivision.toTaggedPrepartition_isHenstock

/-- The dual of a partition is a partition. -/
theorem dual_isPartition (π : TaggedPrepartition (Ioc a b)) (hab : a < b)
    (hπ_hen : π.IsHenstock) (hπ_part : π.IsPartition) :
    (π.dual hab hπ_hen hπ_part).IsPartition := by
  dsimp [dual]
  apply TaggedDivision.toTaggedPrepartition_isPartition

/-- The mesh size of the dual tagged prepartition is at most twice the mesh size of the original
tagged prepartition. -/
theorem dual_mesh_size_le_two_mul
    (π : TaggedPrepartition (Ioc a b)) (hab : a < b)
    (hπ_hen : π.IsHenstock) (hπ_part : π.IsPartition) :
    (π.dual hab hπ_hen hπ_part).mesh_size ≤ 2 * π.mesh_size := by
  let ρ := π.toTaggedDivision
  have hρ : ρ.ValidTags := π.toTaggedDivision_validTags hπ_hen hπ_part
  have hρ_first : ρ.x 0 = a := π.toTaggedDivision_first hab hπ_part
  have hρ_last : ρ.x (Fin.last ρ.N) = b := π.toTaggedDivision_last hab hπ_part
  have hmesh := TaggedDivision.dual_mesh_size_le_two_mul ρ hρ hρ_first hρ_last
  have hround := π.toTaggedDivision_toTaggedPrepartition_mesh_size hab hπ_hen hπ_part
  simpa [dual, ρ, hround] using hmesh

end TaggedPrepartition

end BoxIntegral
