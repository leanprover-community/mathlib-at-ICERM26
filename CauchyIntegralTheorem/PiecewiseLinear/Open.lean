/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module

public import PiecewiseLinear.Approximation
public import PiecewiseC1.Basic

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

/--
In an open connected subset of `ℂ`, any two points can be joined by a piecewise-linear path
staying in the set.
-/
lemma exists_isPiecewiseLinear_mapsInto_of_isOpen_isConnected
    {U : Set ℂ} (hU_open : IsOpen U) (hU_connected : IsConnected U)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    ∃ γ : Path x y, γ.IsPiecewiseLinear ∧ γ.MapsInto U := by
  have hU_path : IsPathConnected U :=
    (hU_open.isConnected_iff_isPathConnected).mp hU_connected
  rcases hU_path.joinedIn x hx y hy with ⟨γ, hγU⟩
  let K : Set ℂ := Set.range γ
  have hK_compact : IsCompact K := isCompact_range γ.continuous
  have hK_subset : K ⊆ U := by
    rintro z ⟨t, rfl⟩
    exact hγU t
  rcases hK_compact.exists_thickening_subset_open hU_open hK_subset with
    ⟨ε, hεpos, hεU⟩
  rcases Path.exists_isPiecewiseLinear_forall_dist_lt γ ε hεpos with
    ⟨γ', hγ'PL, hγ'close⟩
  refine ⟨γ', hγ'PL, ?_⟩
  intro t
  apply hεU
  rw [Metric.mem_thickening_iff]
  exact ⟨γ t, ⟨t, rfl⟩, by simpa [dist_comm] using hγ'close t⟩


