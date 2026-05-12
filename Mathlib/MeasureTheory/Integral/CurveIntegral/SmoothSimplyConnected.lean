import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Complex.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

open scoped ContDiff unitInterval Topology

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
    ∀ γ₁ : Path x y, IsC2PathIn γ₁ s → ∀ γ₂ : Path x z, IsC2PathIn γ₂ s →
    ∃ φ : ContinuousMap.Homotopy γ₁ γ₂, IsC2AffineHomotopyIn φ s

theorem IsOpen.isSmoothlySimplyConnected {s : Set ℂ} (hs : IsOpen s) (hs' : IsSimplyConnected s) :
    IsSmoothlySimplyConnected s where
      exists_smooth_path x hx y hy := by
        set sx := connectedComponentIn s x with hsx
        have hCompOpen : IsOpen sx := hs.connectedComponentIn
        have hCompConn : IsConnected sx := isConnected_connectedComponentIn_iff.mpr hx
        have hCompPC : IsPathConnected sx := hCompOpen.isConnected_iff_isPathConnected.mp hCompConn
        have hJoined : JoinedIn sx x y := hCompPC.joinedIn x (mem_connectedComponentIn hx) y hy
        let γ₀ : Path x y := hJoined.somePath
        have hγ₀_range : Set.range γ₀ ⊆ s :=
          (Set.range_subset_iff.mpr hJoined.somePath_mem).trans (connectedComponentIn_subset s x)
        obtain ⟨δ, hδ, hδs⟩ :=
          (isCompact_range γ₀.continuous).exists_thickening_subset_open hs hγ₀_range
        obtain ⟨g, hg_smooth, hg_dist⟩ :=
          γ₀.uniformContinuous_extend.exists_contDiff_dist_le (by linarith : 0 < δ / 3)
        let h : ℝ → ℂ := fun t ↦ g t + (1 - t) • (x - g 0) + t • (y - g 1)
        have hh0 : h 0 = x := by simp [h]
        have hh1 : h 1 = y := by simp [h]
        have hh_smooth : ContDiff ℝ ∞ h := by fun_prop
        have hh_range (t : I) : h t ∈ s := by

          sorry
        let γ : Path x y :=
          { toFun := fun t ↦ h t
            continuous_toFun := hh_smooth.continuous.comp continuous_subtype_val
            source' := hh0
            target' := hh1 }
        refine ⟨γ, Set.range_subset_iff.mpr hh_range, ?_⟩
        sorry
      exists_smooth_homotopy x hx y hy := by

        sorry
