/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Dual
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Algebra.BigOperators.Fin

/-! # Finite Riemann-Stieltjes sums attached to tagged divisions -/

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

theorem by_parts (π : TaggedDivision) (B : E →L[ℝ] F →L[ℝ] G)
    (f : ℝ → E) (g : ℝ → F) :
    π.RiemannStieltjesSum B.flip g f =
      B (f (π.x (Fin.last π.N))) (g (π.x (Fin.last π.N))) - B (f (π.x 0)) (g (π.x 0)) -
        π.dual.RiemannStieltjesSum B f g := by
  induction π using TaggedDivision.recOnDropLast with
  | zero π h0 => sorry
  | step π hN ih => sorry

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
  sorry

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
  sorry

/-- Finite summation by parts for the dual tagged prepartition. -/
theorem dual_sum_by_parts (π : TaggedPrepartition (Ioc a b)) (hab : a < b)
    (hπ_hen : π.IsHenstock) (hπ_part : π.IsPartition) :
    (∑ J ∈ π.boxes, B.flip (g (π.tag J 0)) (f J.upper₁ - f J.lower₁)) =
      B (f b) (g b) - B (f a) (g a) -
        ∑ J ∈ (π.dual hab hπ_hen hπ_part).boxes,
          B (f ((π.dual hab hπ_hen hπ_part).tag J 0))
            (g J.upper₁ - g J.lower₁) := by
  -- This proof is AI nonsense and should be cleaned up
  let ρ := π.toTaggedDivision
  have hρ : ρ.ValidTags := π.toTaggedDivision_validTags hπ_hen hπ_part
  have hρ_first : ρ.x 0 = a := π.toTaggedDivision_first hab hπ_part
  have hρ_last : ρ.x (Fin.last ρ.N) = b := π.toTaggedDivision_last hab hπ_part
  have hleft :
      ρ.RiemannStieltjesSum B.flip g f =
        ∑ J ∈ π.boxes, B.flip (g (π.tag J 0)) (f J.upper₁ - f J.lower₁) := by
    simpa [ρ] using
      (π.toTaggedDivision_RiemannStieltjesSum (B := B.flip) (f := g) (g := f) hπ_part)
  have hright :
      (∑ J ∈ (π.dual hab hπ_hen hπ_part).boxes,
        B (f ((π.dual hab hπ_hen hπ_part).tag J 0)) (g J.upper₁ - g J.lower₁)) =
        ρ.dual.RiemannStieltjesSum B f g := by
    simpa [TaggedPrepartition.dual, ρ] using
      (TaggedDivision.toTaggedPrepartition_RiemannStieltjesSum
        (hπ := ρ.dual_validTags hρ)
        (ha := by simpa using ρ.dual_first.trans hρ_first)
        (hb := by simpa using ρ.dual_last.trans hρ_last)
        (B := B) (f := f) (g := g))
  rw [← hleft, hright]
  simpa [hρ_first, hρ_last] using
    (TaggedDivision.RiemannStieltjesSum.by_parts ρ B f g)

end TaggedPrepartition

end BoxIntegral
