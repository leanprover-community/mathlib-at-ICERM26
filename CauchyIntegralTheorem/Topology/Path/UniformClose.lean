/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module

public import PiecewiseC1.Basic

open scoped unitInterval

public section

namespace Path

/-- Two complex paths with the same endpoints are uniformly close at scale `ε` if their
pointwise distance is less than `ε` on the unit interval. -/
public abbrev UniformClose {a b : ℂ} (γ γ' : Path a b) (ε : ℝ) : Prop :=
  ∀ t : I, dist (γ t) (γ' t) < ε

end Path
