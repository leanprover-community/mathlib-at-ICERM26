/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Dual
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Algebra.BigOperators.Fin

/-! # Finite Riemann-Stieltjes sums attached to tagged divisions

## AI usage

The proofs of `TaggedDivision.RiemannStieltjesSum.by_parts`,
`TaggedDivision.toTaggedPrepartition_RiemannStieltjesSum`,
`TaggedPrepartition.toTaggedDivision_RiemannStieltjesSum` and
`TaggedPrepartition.dual_sum_by_parts` were written by Claude (Anthropic) in November 2026,
replacing `sorry`s and an earlier LLM-generated proof of `dual_sum_by_parts`. They compile, but
have not been reviewed by a human.
-/

@[expose] public section

open scoped BigOperators

namespace BoxIntegral
namespace TaggedDivision

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The finite Riemann-Stieltjes sum associated to a tagged division. -/
noncomputable def RiemannStieltjesSum (π : TaggedDivision) (B : E →L[ℝ] F →L[ℝ] G)
    (f : ℝ → E) (g : ℝ → F) : G :=
  ∑ i : Fin π.N, B (f (π.tag i)) (g (π.x i.succ) - g (π.x i.castSucc))

namespace RiemannStieltjesSum

@[simp]
theorem eq_zero_of_N_eq_zero (π : TaggedDivision) (hπ : π.N = 0)
    (B : E →L[ℝ] F →L[ℝ] G) (f : ℝ → E) (g : ℝ → F) :
    π.RiemannStieltjesSum B f g = 0 := by
  rcases π with ⟨⟨N, x⟩, tag⟩
  dsimp at hπ ⊢
  subst N
  simp [TaggedDivision.RiemannStieltjesSum]

theorem eq_dropLast_add
    (π : TaggedDivision) (hN : 0 < π.N) (B : E →L[ℝ] F →L[ℝ] G)
    (f : ℝ → E) (g : ℝ → F) :
      π.RiemannStieltjesSum B f g =
      π.dropLast.RiemannStieltjesSum B f g +
      B (f (π.tag ⟨π.N - 1, by omega⟩))
        (g (π.x (Fin.last π.N)) - g (π.x ⟨π.N - 1, by omega⟩)) := by
  rcases π with ⟨⟨N, x⟩, tag⟩
  dsimp [RiemannStieltjesSum, dropLast] at hN ⊢
  cases N with
  | zero => omega
  | succ n =>
      rw [Fin.sum_univ_castSucc]
      congr

theorem snoc (π : TaggedDivision) (c t : ℝ) (B : E →L[ℝ] F →L[ℝ] G)
    (f : ℝ → E) (g : ℝ → F) :
    (π.snoc c t).RiemannStieltjesSum B f g =
      π.RiemannStieltjesSum B f g + B (f t) (g c - g (π.x (Fin.last π.N))) := by
  rcases π with ⟨⟨N, x⟩, tag⟩
  dsimp [RiemannStieltjesSum, TaggedDivision.snoc, BoxIntegral.OrderedDivision.snoc]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hs : i.castSucc.succ = i.succ.castSucc := by ext; simp
    have hxs : @Fin.snoc (N + 1) (fun _ => ℝ) x c i.castSucc.succ = x i.succ := by
      rw [hs, Fin.snoc_castSucc]
    rw [hxs]
    simp [Fin.snoc_castSucc]
  · simp [Fin.snoc_last, Fin.snoc_castSucc]

theorem removeDuplicates
    (π : TaggedDivision) (B : E →L[ℝ] F →L[ℝ] G) (f : ℝ → E) (g : ℝ → F) :
    π.removeDuplicates.RiemannStieltjesSum B f g =
      π.RiemannStieltjesSum B f g := by
  revert B f g
  induction π using TaggedDivision.recOnDropLast with
  | zero π h0 =>
    intro B f g
    rw [TaggedDivision.removeDuplicates.of_N_eq_zero π h0]
  | step π hN ih =>
    intro B f g
    have h0 : ¬π.N = 0 := by omega
    let y := π.x ⟨π.N - 1, by omega⟩
    let z := π.x (Fin.last π.N)
    let t := π.tag ⟨π.N - 1, by omega⟩
    let σ := π.dropLast.removeDuplicates
    have hσ_last : σ.x (Fin.last σ.N) = y := by
      dsimp [σ]
      rw [TaggedDivision.removeDuplicates.last π.dropLast]
      exact π.dropLast_last
    have hrec :
        σ.RiemannStieltjesSum B f g =
          π.dropLast.RiemannStieltjesSum B f g := by
      dsimp [σ]
      exact ih B f g
    have hdrop := eq_dropLast_add π hN B f g
    by_cases h : y = z
    · rw [TaggedDivision.removeDuplicates.of_last_eq π hN (by simpa [y, z] using h)]
      rw [hrec, hdrop]
      simp [y, z, h]
    · rw [TaggedDivision.removeDuplicates.of_last_ne π hN (by simpa [y, z] using h)]
      rw [snoc σ z t B f g, hrec, hdrop]
      simp [hσ_last, y, z, t]

/-- Finite summation by parts (the identity behind the proof of Theorem A.2 of
Montgomery–Vaughan): the Riemann–Stieltjes sum of `g` against `f` over a tagged division equals
the boundary term minus the Riemann–Stieltjes sum of `f` against `g` over the dual division. -/
theorem by_parts (π : TaggedDivision) (B : E →L[ℝ] F →L[ℝ] G)
    (f : ℝ → E) (g : ℝ → F) :
    π.RiemannStieltjesSum B.flip g f =
      B (f (π.x (Fin.last π.N))) (g (π.x (Fin.last π.N))) - B (f (π.x 0)) (g (π.x 0)) -
        π.dual.RiemannStieltjesSum B f g := by
  have hdual : π.dual.RiemannStieltjesSum B f g =
      ∑ j : Fin (π.N + 1), B (f (π.x j)) (g (dual.x π j.succ) - g (dual.x π j.castSucc)) := rfl
  rw [hdual]
  simp only [RiemannStieltjesSum, ContinuousLinearMap.flip_apply, map_sub,
    Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (fun j ↦ B (f (π.x j)) (g (dual.x π j.succ))),
    Fin.sum_univ_succ (fun j ↦ B (f (π.x j)) (g (dual.x π j.castSucc)))]
  simp only [dual.x_castSucc_succ, dual.x_succ_castSucc, Fin.succ_last, dual.x_last,
    Fin.castSucc_zero, dual.x_first]
  abel

end RiemannStieltjesSum

/-- The finite sum over the tagged prepartition associated to a tagged division is its
Riemann-Stieltjes sum. -/
theorem toTaggedPrepartition_RiemannStieltjesSum {a b : ℝ}
    (π : TaggedDivision) (hπ : π.ValidTags)
    (ha : π.x 0 = a) (hb : π.x (Fin.last π.N) = b)
    (B : E →L[ℝ] F →L[ℝ] G) (f : ℝ → E) (g : ℝ → F) :
    (∑ J ∈ (π.toTaggedPrepartition hπ ha hb).boxes,
      B (f ((π.toTaggedPrepartition hπ ha hb).tag J 0)) (g J.upper₁ - g J.lower₁)) =
      π.RiemannStieltjesSum B f g := by
  classical
  rw [toTaggedPrepartition_boxes, Finset.sum_image (box_injOn (π.validTags_monotone hπ)),
    RiemannStieltjesSum, ← Finset.sum_subset (Finset.subset_univ π.posIdx)]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := mem_posIdx.1 hi
    rw [toTaggedPrepartition_tag π hπ ha hb hi]
    simp [OrderedDivision.box, Box.upper₁, Box.lower₁, hi']
  · -- Degenerate intervals contribute nothing.
    intro i _ hi
    have : π.x i.succ = π.x i.castSucc :=
      le_antisymm (not_lt.1 fun h ↦ hi (mem_posIdx.2 h)) ((hπ i).1.trans (hπ i).2)
    simp [this]

end TaggedDivision

namespace TaggedPrepartition

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {a b : ℝ} {B : E →L[ℝ] F →L[ℝ] G} {f : ℝ → E} {g : ℝ → F}

/-- The finite sum over a tagged partition is the Riemann-Stieltjes sum of the associated
ordered tagged division. -/
theorem toTaggedDivision_RiemannStieltjesSum
    (π : TaggedPrepartition (Ioc a b)) (hπ_part : π.IsPartition) :
    π.toTaggedDivision.RiemannStieltjesSum B f g =
      ∑ J ∈ π.boxes, B (f (π.tag J 0)) (g J.upper₁ - g J.lower₁) := by
  rw [← OrderedDivision.fromPartition_map (π := π.toPrepartition) hπ_part,
    OrderedDivision.boxMap, Finset.sum_map, TaggedDivision.RiemannStieltjesSum]
  refine Finset.sum_congr rfl
    fun (i : Fin (OrderedDivision.fromPartition π.toPrepartition).N) _ ↦ ?_
  have hmono : _root_.StrictMono (OrderedDivision.fromPartition π.toPrepartition).x :=
    OrderedDivision.fromPartition_strictMono π.toPrepartition
  have hlt := hmono (Fin.castSucc_lt_succ (i := i))
  simp [toTaggedDivision, OrderedDivision.box, Box.upper₁, Box.lower₁, hlt]

/-- Finite summation by parts for the dual tagged prepartition. -/
theorem dual_sum_by_parts (π : TaggedPrepartition (Ioc a b)) (hab : a < b)
    (hπ_hen : π.IsHenstock) (hπ_part : π.IsPartition) :
    (∑ J ∈ π.boxes, B.flip (g (π.tag J 0)) (f J.upper₁ - f J.lower₁)) =
      B (f b) (g b) - B (f a) (g a) -
        ∑ J ∈ (π.dual hab hπ_hen hπ_part).boxes,
          B (f ((π.dual hab hπ_hen hπ_part).tag J 0))
            (g J.upper₁ - g J.lower₁) := by
  rw [← π.toTaggedDivision_RiemannStieltjesSum hπ_part,
    TaggedDivision.RiemannStieltjesSum.by_parts, π.toTaggedDivision_first hab hπ_part,
    π.toTaggedDivision_last hab hπ_part, dual,
    TaggedDivision.toTaggedPrepartition_RiemannStieltjesSum]

end TaggedPrepartition

end BoxIntegral
