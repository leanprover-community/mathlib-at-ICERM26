module

public import Lean.Meta.Tactic.Grind.RegisterCommand

public meta section

/-- A grind set for simplifying expressions involving `⊤`. -/
register_grind_attr untopify_top

/-- A grind set for pushing coercions from `α` to `WithTop α`, or type synonyms of that. -/
register_grind_attr untopify_coe
