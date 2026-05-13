/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module

public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Topology.ContinuousOn

open Set
open scoped Topology

public section
lemma ContinuousOn.finset_iUnion_of_isClosed
    {α β ι : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (S : Finset ι) (s : ι → Set α)
    (hf : ∀ i ∈ S, ContinuousOn f (s i))
    (hs : ∀ i ∈ S, IsClosed (s i)) :
    ContinuousOn f (⋃ i ∈ S, s i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, continuousOn_empty]
  | insert a S ha ih =>
      have hfa : ContinuousOn f (s a) := hf a (by simp)
      have hsa : IsClosed (s a) := hs a (by simp)

      have hfS : ContinuousOn f (⋃ i ∈ S, s i) := by
        exact ih
          (fun i hi => hf i (by simp [hi]))
          (fun i hi => hs i (by simp [hi]))

      have hsS : IsClosed (⋃ i ∈ S, s i) := by
        exact isClosed_biUnion_finset fun i hi => hs i (by simp [hi])

      rw [Finset.set_biUnion_insert]
      exact hfa.union_of_isClosed hfS hsa hsS



