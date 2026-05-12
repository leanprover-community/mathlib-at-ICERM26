import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homotopy.Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

open scoped unitInterval Topology

namespace IsSmoothlySimplyConnected

structure IsC2PathIn {x y : E} (γ : Path x y) (s : Set E) : Prop where
  range_subset : Set.range γ ⊆ s
  contDiffOn : ContDiffOn ℝ 2 γ.extend I

structure IsC2AffineHomotopyIn {γ₁ γ₂ : C(I, E)} (φ : γ₁.Homotopy γ₂) (s : Set E) : Prop where
  range_subset : Set.range φ ⊆ s
  contDiffOn :
    ContDiffOn ℝ 2
      (fun (x, y) ↦ φ (Set.projIcc 0 1 zero_le_one x, Set.projIcc 0 1 zero_le_one y)) (I ×ˢ I)
  eval_at_zero : ∀ t : I, φ (t, 0) = AffineMap.lineMap (γ₁ 0) (γ₂ 0) (t : ℝ)
  eval_at_one : ∀ t : I, φ (t, 1) = AffineMap.lineMap (γ₁ 1) (γ₂ 1) (t : ℝ)

end IsSmoothlySimplyConnected

open IsSmoothlySimplyConnected

structure IsSmoothlySimplyConnected (s : Set E) : Prop where
  exists_smooth_path : ∀ x ∈ s, ∀ y ∈ connectedComponentIn s x, ∃ γ : Path x y, IsC2PathIn γ s
  exists_smooth_homotopy : ∀ x ∈ s, ∀ y ∈ connectedComponentIn s x, ∀ᶠ z in 𝓝[s] y,
    ∀ γ₁ : Path x y, IsC2PathIn γ₁ s → ∀ γ₂ : Path x y, IsC2PathIn γ₂ s →
    ∃ φ : ContinuousMap.Homotopy γ₁ γ₂, IsC2AffineHomotopyIn φ s
