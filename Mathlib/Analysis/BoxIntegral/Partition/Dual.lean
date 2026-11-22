/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.OrderedDivision

/-! # Dual tagged divisions

This file defines the dual tagged division used for finite summation by parts, following the
proof of Theorem A.2 in Montgomery–Vaughan: the division points of the dual are the endpoints
and the tags of the original division, and its tags are the original division points.

## AI usage

The proofs of `TaggedDivision.dual_validTags` and `TaggedDivision.dual_mesh_size_le_two_mul`
were written by Claude (Anthropic) in November 2026, as were the lemmas `dual.x_castSucc_succ`
and `dual.x_succ_castSucc`. They compile, but have not been reviewed by a human.
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

theorem x_castSucc_succ (π : TaggedDivision) (i : Fin π.N) : x π i.castSucc.succ = π.tag i := by
  rw [x, Fin.cons_succ, Fin.snoc_castSucc]

theorem x_succ_castSucc (π : TaggedDivision) (i : Fin π.N) : x π i.succ.castSucc = π.tag i :=
  x_castSucc_succ π i

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
  intro (i : Fin (π.N + 1))
  change dual.x π i.castSucc ≤ π.x i ∧ π.x i ≤ dual.x π i.succ
  constructor
  · cases i using Fin.cases with
    | zero => simp
    | succ j => rw [dual.x_succ_castSucc]; exact (hπ j).2
  · cases i using Fin.lastCases with
    | last => simp
    | cast j => rw [dual.x_castSucc_succ]; exact (hπ j).1

/-- The coarseness of the dual partition is controlled by the coarseness of the original partition:
its mesh size is at most twice the original mesh size. -/
theorem dual_mesh_size_le_two_mul
    {a b : ℝ} (π : TaggedDivision) (hπ_tag : π.ValidTags)
    (ha : π.x 0 = a) (hb : π.x (Fin.last π.N) = b) :
    (π.dual.toTaggedPrepartition (π.dual_validTags hπ_tag)
      (π.dual_first.trans ha)
      (π.dual_last.trans hb)).mesh_size ≤
      2 * (π.toTaggedPrepartition hπ_tag ha hb).mesh_size := by
  -- Every gap of `π` is at most the mesh size `M`.
  have hM : ∀ i : Fin π.N, π.x i.succ - π.x i.castSucc ≤
      ((π.toTaggedPrepartition hπ_tag ha hb).mesh_size : ℝ) := by
    intro i
    rw [toTaggedPrepartition_mesh_size]
    exact NNReal.coe_le_coe.2 (Finset.le_sup (f := fun i ↦ NNReal.mk (π.x i.succ - π.x i.castSucc)
      (sub_nonneg.mpr ((hπ_tag i).1.trans (hπ_tag i).2))) (Finset.mem_univ i))
  rw [toTaggedPrepartition_mesh_size π.dual]
  generalize (π.toTaggedPrepartition hπ_tag ha hb).mesh_size = M at hM ⊢
  refine Finset.sup_le fun (k : Fin (π.N + 1)) _ ↦ ?_
  rw [← NNReal.coe_le_coe]
  change dual.x π k.succ - dual.x π k.castSucc ≤ ((2 * M : NNReal) : ℝ)
  push_cast
  -- The `k`th gap of the dual straddles the `k`th division point of `π`; each half lies inside
  -- a single gap of `π`.
  have hU : dual.x π k.succ - π.x k ≤ M := by
    cases k using Fin.lastCases with
    | last => simp
    | cast j => rw [dual.x_castSucc_succ]; linarith [(hπ_tag j).2, hM j]
  have hL : π.x k - dual.x π k.castSucc ≤ M := by
    cases k using Fin.cases with
    | zero => simp
    | succ j => rw [dual.x_succ_castSucc]; linarith [(hπ_tag j).1, hM j]
  linarith

end TaggedDivision

namespace TaggedPrepartition

/-! ## Dual tagged prepartitions -/

variable {a b : ℝ}

/-- The unordered tagged prepartition associated to the dual of a Henstock partition of
`Ioc a b`. This is the tagged-prepartition version of `TaggedDivision.dual`, obtained by
ordering the original partition, dualizing it, and forgetting the ordering again. -/
noncomputable def dual (π : TaggedPrepartition (Ioc a b)) (hab : a < b)
    (hπ_hen : π.IsHenstock) (hπ_part : π.IsPartition) :
    TaggedPrepartition (Ioc a b) :=
  π.toTaggedDivision.dual.toTaggedPrepartition
    (π.toTaggedDivision.dual_validTags (π.toTaggedDivision_validTags hπ_hen hπ_part))
    (π.toTaggedDivision.dual_first.trans (π.toTaggedDivision_first hab hπ_part))
    (π.toTaggedDivision.dual_last.trans (π.toTaggedDivision_last hab hπ_part))

/-- The dual of a Henstock partition is Henstock. -/
theorem dual_isHenstock (π : TaggedPrepartition (Ioc a b)) (hab : a < b)
    (hπ_hen : π.IsHenstock) (hπ_part : π.IsPartition) :
    (π.dual hab hπ_hen hπ_part).IsHenstock :=
  TaggedDivision.toTaggedPrepartition_isHenstock _ _ _ _

/-- The dual of a partition is a partition. -/
theorem dual_isPartition (π : TaggedPrepartition (Ioc a b)) (hab : a < b)
    (hπ_hen : π.IsHenstock) (hπ_part : π.IsPartition) :
    (π.dual hab hπ_hen hπ_part).IsPartition :=
  TaggedDivision.toTaggedPrepartition_isPartition _ _ _ _ hab

/-- The mesh size of the dual tagged prepartition is at most twice the mesh size of the original
tagged prepartition. -/
theorem dual_mesh_size_le_two_mul
    (π : TaggedPrepartition (Ioc a b)) (hab : a < b)
    (hπ_hen : π.IsHenstock) (hπ_part : π.IsPartition) :
    (π.dual hab hπ_hen hπ_part).mesh_size ≤ 2 * π.mesh_size := by
  have h := TaggedDivision.dual_mesh_size_le_two_mul π.toTaggedDivision
    (π.toTaggedDivision_validTags hπ_hen hπ_part) (π.toTaggedDivision_first hab hπ_part)
    (π.toTaggedDivision_last hab hπ_part)
  rwa [π.toTaggedDivision_toTaggedPrepartition_mesh_size hab hπ_hen hπ_part] at h

end TaggedPrepartition

end BoxIntegral
