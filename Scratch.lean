import Mathlib.Analysis.BoxIntegral.Stieltjes

open scoped Topology NNReal Filter Uniformity BoxIntegral

open BoxIntegral ContinuousLinearMap

namespace Stieltjes

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable (B : E →L[ℝ] F →L[ℝ] G)

/-! Scratch work for a concrete construction of the integration-by-parts refinement. -/

/-- Split a one-dimensional box at `x`, tagging the lower piece by the left endpoint and the upper
piece by the right endpoint. If `x` is outside the open interval, the split is the one-box
partition and the tag is the endpoint that makes the integration-by-parts identity below
degenerate correctly. -/
noncomputable def endpointSplit (J : Box (Fin 1)) (x : ℝ) : TaggedPrepartition J where
  toPrepartition := Prepartition.split J 0 x
  tag K := if K.upper 0 ≤ x then J.lower else J.upper
  tag_mem_Icc K := by
    by_cases hK : K.upper 0 ≤ x
    · simp [hK, Box.lower_mem_Icc]
    · simp [hK, Box.upper_mem_Icc]

@[simp]
lemma endpointSplit_isPartition (J : Box (Fin 1)) (x : ℝ) :
    (endpointSplit J x).IsPartition :=
  Prepartition.isPartitionSplit J 0 x

/-- The refinement of a tagged partition used in integration by parts: each box is split at its
original tag, then the two pieces are tagged by the left and right endpoints. -/
noncomputable def byPartsRefinement {I : Box (Fin 1)}
    (π : TaggedPrepartition I) : TaggedPrepartition I :=
  π.toPrepartition.biUnionTagged fun J ↦ endpointSplit J (π.tag J 0)

lemma byPartsRefinement_isPartition {I : Box (Fin 1)} {π : TaggedPrepartition I}
    (hπ : π.IsPartition) : (byPartsRefinement π).IsPartition :=
  hπ.biUnionTagged fun J _ ↦ endpointSplit_isPartition J (π.tag J 0)

/-- The concrete finite-sum identity to prove later. -/
lemma integralSum_byPartsRefinement {I : Box (Fin 1)} (π : TaggedPrepartition I)
    (hπ : π.IsPartition) (f : ℝ → E) (g : ℝ → F) :
    integralSum (fun x ↦ f (x 0)) (BoxAdditiveMap.ofDiff (fun x ↦ B.flip (g x)))
        (byPartsRefinement π) =
      B (f (I.upper 0)) (g (I.upper 0)) - B (f (I.lower 0)) (g (I.lower 0)) -
        integralSum (fun x ↦ g (x 0)) (BoxAdditiveMap.ofDiff (fun x ↦ B (f x))) π := by
  sorry

/-- The concrete endpoint-tagged refinement should preserve the Riemann partition filter. -/
lemma tendsto_byPartsRefinement (I : Box (Fin 1)) :
    Filter.Tendsto (byPartsRefinement : TaggedPrepartition I → TaggedPrepartition I)
      (IntegrationParams.Riemann.toFilteriUnion I ⊤)
      (IntegrationParams.Riemann.toFilteriUnion I ⊤) := by
  sorry

end Stieltjes
