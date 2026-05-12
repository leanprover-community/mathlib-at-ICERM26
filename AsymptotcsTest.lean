module

import Mathlib

open Real Topology

namespace Asymptotics

variable {α β γ δ E : Type*} [Norm E] (l : Filter α)

-- Do we always want this to be an existential? Maybe on the LHS of an inequality we'd
-- interpret O(O(f)) = ... as ∀ g =O f, O(g) = ..., or: ∀ g =O f, ∀ h =O g, h = ...
def bigO (s : Set (α → E)) : Set (α → E) :=
  { f | ∃ g ∈ s, f =O[l] g }

/-
To spell it out more explicitly, I'm not sure the interpretation of O(O(s)) makes sense
if we interpret it in terms of universal / existential quantifiers. In that setting,
`O(O(s) + f x) ⊆ g x + O(x)`

should be the same as

`∀ f₁, f₁ = O(s) → ∀ f₂, f₂ = O(f₁ x + f x) → ∃ g₁, g₁ = O(x) ∧ f₂ x = g x + g₁ x`

so `O(O(s) + f x)` consists of `f₂` such that `∀ f₁ ∈ O(s), f₂ ∈ O(f₁ x + f x)`

If we reverse the equation, we would get

`∀ g₁, g₁ = O(x) → ∃ f₁, f₁ = O(s) ∧ ∃ f₂, f₂ = O(f₁ x + f x) ∧ f₂ x = g x + g₁ x`

so `O(O(s) + f x)` consists of `f₂` such that `∃ f₁ ∈ O(s), f₂ ∈ O(f₁ x + f x)`

- Arend
-/

/-

Additional things we need to support:

- Other relations rather than just =, for example ≤, =ᶠ[l], ≪. That is,
  `f x ≤ g x + O(1)`
  `n ! =ᶠ[𝓟 {n | n ≠ 0}] (1 + o(n)) * f n` i.e. the equation holds on some subset.
  `f x =ᶠ[atTop] (1 + o(n)) * g n` i.e. `f` and `g` are equivalent
  `f x ≪ g x + O(x)`

- Constants that are allowed to depend on some specific subset of the variables, i.e.
  $O_{A, ε}(f(x))$

-/


@[simp]
lemma mem_bigO (f : α → E) (s : Set (α → E)) : f ∈ bigO l s ↔ ∃ g ∈ s, f =O[l] g := .rfl

def map (s₁ : Set (α → β → γ)) (s₂ : Set (α → β)) : Set (α → γ) :=
  { g | ∃ f₁ ∈ s₁, ∃ f₂ ∈ s₂, g = fun x ↦ f₁ x (f₂ x) }

def pure (x : β) : Set (α → β) := {fun _ ↦ x}

@[gcongr]
lemma map_subset_map {s₁ s₁' : Set (α → β → γ)} {s₂ s₂' : Set (α → β)}
    (h₁ : s₁ ⊆ s₁') (h₂ : s₂ ⊆ s₂') : map s₁ s₂ ⊆ map s₁' s₂' := by
  rintro g ⟨f₁, hf₁, f₂, hf₂, rfl⟩
  exact ⟨f₁, h₁ hf₁, f₂, h₂ hf₂, rfl⟩

@[simp]
lemma mem_pure (x : α → β) (y : β) : x ∈ pure y ↔ x = fun _ ↦ y := by
  simp [pure]

-- Question: Is this meaningful if we replace {id} with a different `Set (ℝ → ℝ)`?
-- exp x = 1 + O[𝓝 0](x)
lemma exp_at_one : map (pure exp) {id} ⊆ map (pure <| HAdd.hAdd 1) (bigO (𝓝 0) {id}) := by
  have := Real.exp_sub_sum_range_isBigO_pow 1
  simp at this
  intro y
  unfold map
  simp
  rintro rfl
  use fun x ↦ Real.exp x - 1
  refine ⟨this, by ring_nf⟩

lemma exp_at_one' {l : Filter ℝ} {f : ℝ → ℝ} (hf : Filter.Tendsto f l (𝓝 0)) :
    map (pure exp) {f} ⊆ map (pure <| HAdd.hAdd 1) (bigO l {f}) := by
  have := Real.exp_sub_sum_range_isBigO_pow 1
  have := this.comp_tendsto hf
  simp at this
  intro y
  unfold map
  simp
  rintro rfl
  use fun x ↦ Real.exp (f x) - 1
  refine ⟨this, by ring_nf⟩

section comp

-- These are helper lemmas for composing a function on both sides of an equation involving bigO s

@[simp, push]
lemma Set.image_comp_map (s₁ : Set (α → β → γ)) (s₂ : Set (α → β)) (f : δ → α) :
    Set.image (· ∘ f) (map s₁ s₂) = map (Set.image (· ∘ f) s₁) (Set.image (· ∘ f) s₂) := by
  simp [map, Set.image]
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · simp only [forall_exists_index, and_imp]
    intro f₁ f₂ hf₁ hf₂ rfl
    grind
  · grind

@[simp, push]
lemma Set.image_pure {f : γ → α} (x : β) :
    (pure x).image (· ∘ f) = pure x :=  by
  simp [pure]
  rfl

@[simp]
lemma Set.image_comp_isBigO {l' : Filter γ} {g : α → E} {f : γ → α} (hg : Filter.Tendsto f l' l) :
    (bigO l {g}).image (· ∘ f) ⊆ bigO l' {g ∘ f} :=  by
  intro f₀
  simp
  rintro w h rfl
  apply h.comp_tendsto hg

end comp

-- same as exp_at_one' but deduced directly from exp_at_one
lemma exp_at_one'' {l : Filter ℝ} {f : ℝ → ℝ} (hf : Filter.Tendsto f l (𝓝 0)) :
    map (pure exp) {f} ⊆ map (pure <| HAdd.hAdd 1) (bigO l {f}) := by
  have h := exp_at_one
  let : Set (ℝ → ℝ) → Set (ℝ → ℝ) := (Set.image (· ∘ f))
  -- Take `h` and compose on the right with `f`, then push into expressions until you
  -- reach bigO.
  rw [← Set.le_iff_subset] at h
  apply_fun this at h
  · simp only [Set.le_eq_subset, this] at h
    simp [Set.image_comp_map] at h
    grw [Set.image_comp_isBigO _ hf] at h
    exact h
  · apply Set.monotone_image


-- O[l](f x) + O[l](f x) = O[l](f x)
lemma bigO_add_bigO (f : α → ℝ) : map (map (pure HAdd.hAdd) (bigO l {f})) (bigO l {f}) = bigO l {f} := by
  unfold map
  ext y
  push _ ∈ _
  constructor
  · simp +contextual
    rintro g hg g' hg' -
    apply hg.add hg'
  · simp +contextual
    intro hy
    refine ⟨y, hy, fun _ ↦ 0, ?_⟩
    simp only [add_zero, and_true]
    exact isBigO_zero f l

set_option autoImplicit false
/-
  (n+1)^(e^(1/n))
  = (n+1)^(1 + O(1/n)) := _
  = exp ( (log n + O(1/n)) * (1 + O(1/n)) ) := _
  = exp (log n + O(log n/n)) := _
  = n * (1 + O(log n/n)) := _
  = n + O(log n) := _
-/

open Filter -- Why can't I say atTop???

example :
    map (map (pure HPow.hPow) (map (map (pure HAdd.hAdd) {id}) (pure 1))) (map (pure Real.exp) (map (pure Inv.inv) {id})) ⊆
      map (map (pure HAdd.hAdd) {id}) (bigO Filter.atTop {Real.log}) := by

  -- This entire calc block is generated by claude.
  calc map (map (pure HPow.hPow) (map (map (pure HAdd.hAdd) {id}) (pure 1)))
          (map (pure Real.exp) (map (pure Inv.inv) {id}))
      -- (n+1)^(exp(1/n)) ⊆ (n+1)^(1 + O(1/n))
      _ ⊆ map (map (pure HPow.hPow) (map (map (pure HAdd.hAdd) {id}) (pure 1)))
            (map (pure <| HAdd.hAdd (1:ℝ)) (bigO Filter.atTop (map (pure Inv.inv) {id}))) := by
        sorry
      -- (n+1)^(1 + O(1/n)) ⊆ exp ( (log n + O(1/n)) * (1 + O(1/n)) )
      _ ⊆ map (pure Real.exp) (map (map (pure HMul.hMul)
            (map (map (pure HAdd.hAdd) {Real.log}) (bigO Filter.atTop (map (pure Inv.inv) {id}))))
            (map (pure <| HAdd.hAdd 1) (bigO Filter.atTop (map (pure Inv.inv) {id})))) := by
        sorry
      -- exp ( (log n + O(1/n)) * (1 + O(1/n)) ) ⊆ exp (log n + O(log n / n))
      -- Interseting choice: It's using the map language inside the big-O
      -- It's correct, but not what I would have written by hand.
      _ ⊆ map (pure Real.exp) (map (map (pure HAdd.hAdd) {Real.log})
            (bigO Filter.atTop (map (map (pure HDiv.hDiv) {Real.log}) {id}))) := by
        sorry
      -- exp (log n + O(log n / n)) ⊆ n * (1 + O(log n / n))
      _ ⊆ map (map (pure HMul.hMul) {id})
            (map (pure <| HAdd.hAdd 1)
              (bigO Filter.atTop (map (map (pure HDiv.hDiv) {Real.log}) {id}))) := by
        sorry
      -- n * (1 + O(log n / n)) ⊆ n + O(log n)
      _ ⊆ map (map (pure HAdd.hAdd) {id}) (bigO Filter.atTop {Real.log}) := by
        sorry

-- -- Aha!, this is true if we define O(s) to be {f | ∀ g ∈ s, f =O[l] g}. Is this what we really want? It's not! O(f) contains 0, so O(O(f)) becomes {0}.
-- -- O[l](f x) + O[l](f x) = O[l](f x)
-- lemma bigO_add_bigO' (x : Set (α → ℝ)) : map (map (pure HAdd.hAdd) (bigO l x)) (bigO l x) = bigO l x := by
--   unfold map
--   ext y
--   push _ ∈ _
--   constructor
--   · simp +contextual
--     rintro g hg g' hg' rfl f' hf'
--     apply (hg _ hf').add (hg' _ hf')
--   · simp +contextual
--     intro hy
--     refine ⟨y, hy, fun _ ↦ 0, ?_⟩
--     simp only [add_zero, and_true]
--     intros
--     exact isBigO_zero _ _
