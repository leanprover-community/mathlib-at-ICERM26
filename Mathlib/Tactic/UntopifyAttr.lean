module

public import Mathlib.Tactic.Attr.Register

public meta section

/-- A simp set for simplifying expressions involving `⊤`. -/
register_simp_attr untopify_top

/-- A simp set for pushing coercions from `α` to `WithTop α`, or type synonyms of that. -/
register_simp_attr untopify_coe
