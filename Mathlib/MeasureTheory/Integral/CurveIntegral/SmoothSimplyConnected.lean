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
          apply hδs
          rw [Metric.mem_thickening_iff]
          refine ⟨γ₀ t, Set.mem_range_self t, ?_⟩
          -- h t - g t = (1-t)•(x - g 0) + t•(y - g 1)
          have hdist_hg : dist (h ↑t) (g ↑t) =
              ‖(1 - (t : ℝ)) • (x - g 0) + (t : ℝ) • (y - g 1)‖ := by
            simp only [h, dist_eq_norm]; congr 1; ring
          -- g t is within δ/3 of γ₀ t
          have hgt : dist (g ↑t) (γ₀ t) < δ / 3 := by
            have := hg_dist (t : ℝ)
            rwa [Path.extend_extends' γ₀ t] at this
          -- endpoints: x - g 0 and y - g 1 are each < δ/3 in norm
          have hx_err : ‖x - g 0‖ < δ / 3 := by
            have := hg_dist 0; rw [Path.extend_zero, dist_comm] at this
            rwa [dist_eq_norm] at this
          have hy_err : ‖y - g 1‖ < δ / 3 := by
            have := hg_dist 1; rw [Path.extend_one, dist_comm] at this
            rwa [dist_eq_norm] at this
          -- correction is a convex combination, so also < δ/3
          have hcorr : ‖(1 - (t : ℝ)) • (x - g 0) + (t : ℝ) • (y - g 1)‖ < δ / 3 := by
            have ht0 : 0 ≤ (t : ℝ) := t.2.1
            have ht1 : (t : ℝ) ≤ 1 := t.2.2
            have hmax : max ‖x - g 0‖ ‖y - g 1‖ < δ / 3 := max_lt hx_err hy_err
            calc ‖(1 - (t : ℝ)) • (x - g 0) + (t : ℝ) • (y - g 1)‖
                ≤ ‖(1 - (t : ℝ)) • (x - g 0)‖ + ‖(t : ℝ) • (y - g 1)‖ := norm_add_le _ _
              _ = (1 - (t : ℝ)) * ‖x - g 0‖ + (t : ℝ) * ‖y - g 1‖ := by
                    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
                        Real.norm_of_nonneg ht0]
              _ ≤ (1 - (t : ℝ)) * max ‖x - g 0‖ ‖y - g 1‖ +
                    (t : ℝ) * max ‖x - g 0‖ ‖y - g 1‖ := by
                    gcongr
                    · exact le_max_left _ _
                    · exact le_max_right _ _
              _ = max ‖x - g 0‖ ‖y - g 1‖ := by ring
              _ < δ / 3 := hmax
          -- combine
          calc dist (h ↑t) (γ₀ t)
              ≤ dist (h ↑t) (g ↑t) + dist (g ↑t) (γ₀ t) := dist_triangle _ _ _
            _ < δ / 3 + δ / 3 := by rw [hdist_hg]; linarith
            _ < δ := by linarith
        let γ : Path x y :=
          { toFun := fun t ↦ h t
            continuous_toFun := hh_smooth.continuous.comp continuous_subtype_val
            source' := hh0
            target' := hh1 }
        refine ⟨γ, Set.range_subset_iff.mpr hh_range, ?_⟩
        exact (hh_smooth.of_le (by norm_cast)).contDiffOn.congr
          (fun t ht ↦ Path.extend_extends' γ ⟨t, ht⟩)
      exists_smooth_homotopy x hx y hy := by

        sorry
