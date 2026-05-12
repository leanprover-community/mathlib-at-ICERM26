module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Homotopy.Basic

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open scoped unitInterval Topology

namespace IsSmoothlySimplyConnected

structure IsC2PathIn {x y : E} (γ : Path x y) (s : Set E) : Prop where
  range_subset : Set.range γ ⊆ s
  contDiffOn : ContDiffOn ℝ 2 γ.extend I

structure IsC2HomotopyIn {γ₁ γ₂ : C(I, E)} (φ : γ₁.Homotopy γ₂) (s : Set E) (ε : ℝ) : Prop where
  range_subset : Set.range φ ⊆ s
  contDiffOn :
    ContDiffOn ℝ 2
      (fun (x, y) ↦ φ (Set.projIcc 0 1 zero_le_one x, Set.projIcc 0 1 zero_le_one y)) (I ×ˢ I)
  dist_eval_at_zero : ∀ t : I, dist (φ (t, 0)) (γ₁ 0) < ε
  dist_eval_at_one : ∀ t : I, dist (φ (t, 1)) (γ₁ 1) < ε

end IsSmoothlySimplyConnected

open IsSmoothlySimplyConnected

structure IsSmoothlySimplyConnected (s : Set E) : Prop where
  exists_smooth_path : ∀ x ∈ s, ∀ y ∈ connectedComponentIn s x, ∃ γ : Path x y, IsC2PathIn γ s
  exists_smooth_homotopy : ∀ x ∈ s, ∀ y ∈ connectedComponentIn s x, ∀ ε > (0 : ℝ), ∀ᶠ z in 𝓝[s] y,
    ∀ γ₁ : Path x y, IsC2PathIn γ₁ s → ∀ γ₂ : Path x z, IsC2PathIn γ₂ s →
    ∃ φ : ContinuousMap.Homotopy γ₁ γ₂, IsC2HomotopyIn φ s ε
