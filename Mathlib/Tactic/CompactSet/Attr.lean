/-
Copyright (c) 2026 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

module

public import Lean.Meta.Tactic.Grind.RegisterCommand
public import Mathlib.Init

/-!
Mark a lemma to be used in the `compact_set` tactic.
-/
register_grind_attr compact_set
