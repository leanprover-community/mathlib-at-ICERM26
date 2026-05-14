/-
Copyright (c) 2026 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

module

public import Lean.Meta.Tactic.Grind.RegisterCommand
public import Mathlib.Init

/-!
Mark a lemma to be used in the `compactness` tactic.
-/
register_grind_attr compactness

open Lean Parser Tactic
/--
A simple tactic that tries various lemmas to prove that a set is compact.
The explicitly marked lemmas are a temporary workaround to
https://github.com/leanprover/lean4/issues/13725. -/
macro "compactness" config:optConfig : tactic =>
  let attr : Ident := mkIdent `compactness
  `(tactic|grind $config only [$attr:term, isCompact_Icc, Ici_inter_Iic])
