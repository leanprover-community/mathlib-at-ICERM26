module

public import Mathlib

open Real Topology
open Filter

namespace Asymptotics


set_option linter.all false

variable {α β γ δ E : Type*} [Norm E] (l : Filter α)

def bigO (s : Set (α → E)) : Set (α → E) :=
  { f | ∃ g ∈ s, f =O[l] g }

-- TODO: figure out the > 0 in this definition. It's not necessary, but
-- very helpful to have while proving things about bigO.
def bigO' (s : Set (α → E)) : Set (α → E) :=
  { f | ∃ g : Finset (α → E), (g : Set _) ⊆ s ∧ f =O[l] (fun x ↦ ⨆ i ∈ g, ‖i x‖) }

@[simp, push]
lemma mem_bigO' (f : α → E) (s : Set (α → E)) :
    f ∈ bigO' l s ↔ ∃ c > 0, ∀ᶠ x in l, ∃ g ∈ s, ‖f x‖ ≤ c * ‖g x‖ := .rfl


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

def RightSerial (r : α → β → Prop) (s₁ : Set α) (s₂ : Set β) : Prop :=
  ∀ x₁ ∈ s₁, ∃ x₂ ∈ s₂, r x₁ x₂

notation3 x " RS[" r "] " y => RightSerial r x y

universe u v w

instance (r : α → β → Prop) (s : β → γ → Prop) (t : α → γ → Prop) [Trans r s t] :
  Trans (RightSerial r) (RightSerial s) (RightSerial t) where
  trans hab hbc := by
    simp only [RightSerial] at hab hbc ⊢
    have := @Trans.trans (r := r) (s := s) (t := t) _ _ _ _
    grind

@[simp]
lemma rightSerial_eq (a b : Set α) : (a RS[Eq] b) ↔ a ⊆ b := by
  unfold RightSerial
  grind

@[simp, gcongr]
lemma RightSerial.singleton_RS_singleton {r : α → α → Prop} (a : α) (b : α) :
    ({a} RS[r] {b}) ↔ r a b := by
  unfold RightSerial
  simp

@[simp, push]
lemma mem_bigO (f : α → E) (s : Set (α → E)) : f ∈ bigO l s ↔ ∃ g ∈ s, f =O[l] g := .rfl

@[gcongr]
lemma bigO_mono_set (s₁ s₂ : Set (α → E)) (h : s₁ ⊆ s₂) : bigO l s₁ ⊆ bigO l s₂ := by
  intro x
  simp only [mem_bigO, forall_exists_index, and_imp]
  grind

/- Written by Claude -/
@[simp]
lemma bigO_bigO (s : Set (α → ℝ)) : bigO l (bigO l s) = bigO l s := by
  ext f
  simp only [mem_bigO]
  refine ⟨?_, ?_⟩
  · rintro ⟨g, ⟨h, hh, hgh⟩, hfg⟩
    exact ⟨h, hh, IsBigO.trans hfg hgh⟩
  · rintro ⟨g, hg, hfg⟩
    exact ⟨g, ⟨g, hg, isBigO_refl _ _⟩, hfg⟩


def map (s₁ : Set (α → β → γ)) (s₂ : Set (α → β)) : Set (α → γ) :=
  { g | ∃ f₁ ∈ s₁, ∃ f₂ ∈ s₂, g = fun x ↦ f₁ x (f₂ x) }

@[simp, push]
lemma mem_map (g : α → γ) (s₁ : Set (α → β → γ)) (s₂ : Set (α → β)) :
    g ∈ map s₁ s₂ ↔ ∃ f₁ ∈ s₁, ∃ f₂ ∈ s₂, g = fun x ↦ f₁ x (f₂ x) := .rfl

def pure (x : β) : Set (α → β) := {fun _ ↦ x}

@[gcongr]
lemma map_subset_map {s₁ s₁' : Set (α → β → γ)} {s₂ s₂' : Set (α → β)}
    (h₁ : s₁ ⊆ s₁') (h₂ : s₂ ⊆ s₂') : map s₁ s₂ ⊆ map s₁' s₂' := by
  rintro g ⟨f₁, hf₁, f₂, hf₂, rfl⟩
  exact ⟨f₁, h₁ hf₁, f₂, h₂ hf₂, rfl⟩

/- Written by Claude -/
@[simp, push]
lemma map_iUnion_left {ι : Sort*} (s : ι → Set (α → β → γ)) (t : Set (α → β)) :
    map (⋃ i, s i) t = ⋃ i, map (s i) t := by
  ext g
  simp only [map, Set.mem_setOf_eq, Set.mem_iUnion]
  grind

/- Written by Claude -/
@[simp, push]
lemma map_iUnion_right {ι : Sort*} (s : Set (α → β → γ)) (t : ι → Set (α → β)) :
    map s (⋃ i, t i) = ⋃ i, map s (t i) := by
  ext g
  simp only [map, Set.mem_setOf_eq, Set.mem_iUnion]
  grind

/- Written by Claude -/
@[gcongr]
lemma RSerial.iUnion_RS_iUnion {ι : Sort*} {r : α → β → Prop} {s : ι → Set α} {t : ι → Set β}
    (h : ∀ i, s i RS[r] t i) : (⋃ i, s i) RS[r] (⋃ i, t i) := by
  rintro x ⟨_, ⟨i, rfl⟩, hx⟩
  obtain ⟨y, hy, hxy⟩ := h i x hx
  exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, hxy⟩

class MapClass {α β γ : Type*} (r : (α → γ) → (α → γ) → Prop)
    (r₁ : outParam ((α → β → γ) → (α → β → γ) → Prop)) (r₂ : outParam ((α → β) → (α → β) → Prop)) where
  imp {f₁ f₂ f₁' f₂'} : r₁ f₁ f₁' → r₂ f₂ f₂' → r (fun x ↦ f₁ x (f₂ x)) (fun x ↦ f₁' x (f₂' x))

@[gcongr]
lemma map_rightSerial_map {s₁ s₁' : Set (α → β → γ)} {s₂ s₂' : Set (α → β)} {r r₁ r₂} [MapClass r r₁ r₂]
    (h₁ : s₁ RS[r₁] s₁') (h₂ : s₂ RS[r₂] s₂') : map s₁ s₂ RS[r] map s₁' s₂' := by
  rintro g ⟨f₁, hf₁, f₂, hf₂, rfl⟩
  obtain ⟨f₁', hf₁', hff₁⟩ := h₁ f₁ hf₁
  obtain ⟨f₂', hf₂', hff₂⟩ := h₂ f₂ hf₂
  refine ⟨fun x ↦ f₁' x (f₂' x), ⟨f₁', hf₁', f₂', hf₂', rfl⟩, ?_⟩
  exact MapClass.imp hff₁ hff₂

instance {l : Filter α} : MapClass (α := α) (β := β) (γ := γ) (EventuallyEq l) (EventuallyEq l) (EventuallyEq l) where
  imp h₁ h₂ := by
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    simp [hx₁, hx₂]

instance : MapClass (α := α) (β := β) (γ := γ) Eq Eq Eq where
  imp h₁ h₂ := by simp [h₁, h₂]

@[simp]
lemma mem_pure (x : α → β) (y : β) : x ∈ pure y ↔ x = fun _ ↦ y := by
  simp [pure]

-- Question: Is this meaningful if we replace {fun x ↦ x} with a different `Set (ℝ → ℝ)`?
-- exp x = 1 + O[𝓝 0](x)
lemma exp_at_one : map (pure exp) {fun x ↦ x} ⊆ map (pure <| HAdd.hAdd 1) (bigO (𝓝 0) {fun x ↦ x}) := by
  have := Real.exp_sub_sum_range_isBigO_pow 1
  simp at this
  intro y
  simp
  rintro rfl
  use fun x ↦ Real.exp x - 1
  refine ⟨this, by ring_nf⟩

lemma exp_at_one_ : map (pure exp) {fun x ↦ x} ⊆ map (map (pure HAdd.hAdd) (pure 1)) (bigO (𝓝 0) {fun x ↦ x}) := by
  have := Real.exp_sub_sum_range_isBigO_pow 1
  simp at this
  intro y
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

lemma exp_at_one_set {l : Filter ℝ} {s : Set (ℝ → ℝ)}
    (hs : ∀ f ∈ s, Filter.Tendsto f l (𝓝 0)) :
    map (pure exp) s ⊆ map (pure <| HAdd.hAdd 1) (bigO l s) := by
  /- Written partly using Claude, but I want to see if we can do this more systematically? -/
  conv_lhs => rw [← Set.biUnion_of_singleton s]
  push map
  simp only [map_iUnion_right, Set.iUnion_subset_iff]
  rintro f hf
  grw [exp_at_one'' (hs _ hf), bigO_mono_set]
  simp [hf]

-- O[l](f x) + O[l](f x) = O[l](f x)
lemma bigO_add_bigO_self (f : α → ℝ) : map (map (pure HAdd.hAdd) (bigO l {f})) (bigO l {f}) = bigO l {f} := by
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

lemma bigO_add_bigO_set_eq_union (s₁  s₂ : Set (α → ℝ)) : map (map (pure HAdd.hAdd) (bigO' l s₁)) (bigO' l s₂) ⊆ bigO' l (s₁ ∪ s₂) := by
  intro y
  push _ ∈ _
  simp
  rintro f₀ c₀ hc₀ hf₀ f₁ c₁ hc₁ hf₁ rfl
  use c₀ + c₁, (by linarith)
  filter_upwards [hf₀, hf₁]
  intro x ⟨g₀, hg₀s, hg₀⟩ ⟨g₁, hg₁s, hg₁⟩
  grw [abs_add_le, hg₀, hg₁]
  simp_rw [add_mul]
  by_cases! h : |g₀ x| ≤ |g₁ x|
  · grw [h]
    use g₁, (.inr hg₁s)
  · grw [h]
    use g₀, (.inl hg₀s)

-- O[l](f x) + O[l](f x) = O[l](f x)
lemma bigO_add_bigO_set (f : Set (α → ℝ)) : map (map (pure HAdd.hAdd) (bigO' l f)) (bigO' l f) ⊆ bigO' l f := by
  grw [bigO_add_bigO_set_eq_union, Set.union_self]

-- Do we even need this? It's just a grw?
lemma bigO_add_bigO_eq_left (s₁ s₂ : Set (α → ℝ)) (h : bigO' l s₂ ⊆ bigO' l s₁) : map (map (pure HAdd.hAdd) (bigO' l s₁)) (bigO' l s₂) ⊆ bigO' l s₁ := by
  grw [h, bigO_add_bigO_set]

set_option autoImplicit false
/-
  (n+1)^(e^(1/n))
  = (n+1)^(1 + O(1/n)) := _
  = exp ( (log n + O(1/n)) * (1 + O(1/n)) ) := _
  = exp (log n + O(log n/n)) := _
  = n * (1 + O(log n/n)) := _
  = n + O(log n) := _
-/

lemma map_eq (s₁ : Set (α → β → γ)) (s₂ : Set (α → β)) :
    map s₁ s₂ = ⋃ i₁ ∈ s₁, ⋃ i₂ ∈ s₂, {fun x ↦ i₁ x (i₂ x)} := by
  ext x
  simp [map]

lemma singleton_eq_map_singleton_singleton (f : α → β → γ) (a : α → β) :
    ({fun x ↦ f x (a x)} : Set (α → γ)) = map {f} {a} := by
  simp [map_eq, pure]

opaque dummyBigO [Norm E] (l : Filter α) (a : E) : E := a

open Qq Lean Meta in
partial def mappify (x : FVarId) (e : Expr) : MetaM Expr := do
  match_expr e with
  | dummyBigO α E instNormE l e' =>
    mkAppOptM ``bigO #[α, E, instNormE, l, ← mappify x e']
  | _ =>
  if let .app f a := e then
    let fType ← inferType f
    if let .forallE _ _ _ .default := fType then
      let f ← mappify x f
      let a ← mappify x a
      return ← mkAppM ``map #[f, a]
  let e ← mkForallFVars #[.fvar x] e
  mkAppM ``singleton #[e]

macro "magic_tac" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [map_eq, mem_pure, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left,
    Set.mem_iUnion, exists_prop, Set.iUnion_exists, Set.biUnion_and'] $[$loc]?)

lemma mul_bigO {f g : Set (ℝ → ℝ)} {l : Filter ℝ} :
    map (map (pure HMul.hMul) f) (bigO l g) ⊆ bigO l (map (map (pure HMul.hMul) f) g) := by
  magic_tac
  intro x
  push _ ∈ _
  simp only [exists_prop, ↓existsAndEq, true_and, forall_exists_index, and_imp]
  rintro p hp r q hq hr rfl
  use p, hp, q, hq
  exact IsBigO.mul (isBigO_refl p l) hr

lemma bigO_mul {f g : Set (ℝ → ℝ)} {l : Filter ℝ} :
    map (map (pure HMul.hMul) (bigO l f)) g ⊆ bigO l (map (map (pure HMul.hMul) f) g) := by
  magic_tac
  intro x
  push _ ∈ _
  simp only [exists_prop, ↓existsAndEq, true_and, forall_exists_index, and_imp]
  rintro r p hp hr q hq rfl
  use p, hp, q, hq
  exact IsBigO.mul hr (isBigO_refl q l)
attribute [refl] isBigO_refl

@[gcongr]
lemma bigO_subset_bigO {l : Filter ℝ} {s₁ s₂ : Set (ℝ → ℝ)} (h : ∀ f ∈ s₁, ∃ g ∈ s₂, f =O[l] g) :
    bigO l s₁ ⊆ bigO l s₂ := by
  intro f
  simp only [mem_bigO, forall_exists_index, and_imp]
  intro f' hf's hf'
  specialize h f' hf's
  grw [hf']
  exact h

theorem terry :
    map (map (pure HPow.hPow) (map (map (pure HAdd.hAdd) {fun x ↦ x}) (pure 1))) (map (pure Real.exp) (map (pure Inv.inv) {fun x ↦ x})) RS[EventuallyEq atTop]
      map (map (pure HAdd.hAdd) {fun x ↦ x}) (bigO Filter.atTop {Real.log}) := by
  -- This entire calc block is generated by claude.
  calc map (map (pure HPow.hPow) (map (map (pure HAdd.hAdd) {fun x ↦ x}) (pure 1)))
          (map (pure Real.exp) (map (pure Inv.inv) {fun x ↦ x}))
      -- asymp% n => (n+1)^(exp(1/n)) =ᶠ[atTop] (n+1)^(1 + O(1/n))
      _ RS[Eq] map (map (pure HPow.hPow) (map (map (pure HAdd.hAdd) {fun x ↦ x}) (pure 1)))
            (map (pure <| HAdd.hAdd (1:ℝ)) (bigO Filter.atTop (map (pure Inv.inv) {fun x ↦ x}))) := by
        sorry
      -- (n+1)^(1 + O(1/n)) ⊆ exp ( (log n + O(1/n)) * (1 + O(1/n)) )
      _ RS[Eq] map (pure Real.exp) (map (map (pure HMul.hMul)
            (map (map (pure HAdd.hAdd) {Real.log}) (bigO Filter.atTop (map (pure Inv.inv) {fun x ↦ x}))))
            (map (pure <| HAdd.hAdd 1) (bigO Filter.atTop (map (pure Inv.inv) {fun x ↦ x})))) := by
        sorry
      -- exp ( (log n + O(1/n)) * (1 + O(1/n)) ) ⊆ exp (log n + O(log n / n))
      -- Interseting choice: It's using the map language inside the big-O
      -- It's correct, but not what I would have written by hand.
      _ RS[Eq] map (pure Real.exp) (map (map (pure HAdd.hAdd) {Real.log})
            (bigO Filter.atTop (map (map (pure HDiv.hDiv) {Real.log}) {fun x ↦ x}))) := by
        sorry
      -- exp (log n + O(log n / n)) ⊆ n * (1 + O(log n / n))
      _ RS[EventuallyEq atTop] map (map (pure HMul.hMul) ({fun x ↦ x})) (map (pure Real.exp) (bigO Filter.atTop (map (map (pure HDiv.hDiv) {fun x ↦ Real.log x}) {fun x ↦ x}))) := by
        magic_tac
        gcongr with f
        filter_upwards [eventually_gt_atTop 0]
        intro x hx
        rw [Real.exp_add, Real.exp_log hx]
      _ RS[Eq] map (map (pure HMul.hMul) {fun x ↦ x})
            (map (pure <| HAdd.hAdd 1)
              (bigO Filter.atTop (map (map (pure HDiv.hDiv) {Real.log}) {fun x ↦ x}))) := by
        rw [rightSerial_eq]
        -- magic_tac
        grw [exp_at_one_set (l := atTop), bigO_bigO]
        · simp
          intro f hf
          apply hf.trans_tendsto
          have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1
          simpa [ne_eq, one_ne_zero, not_false_eq_true, pow_one, one_mul, add_zero,
            forall_const] using this
      _ RS[Eq] map (map (pure HAdd.hAdd) {fun x ↦ x}) (map (map (pure HMul.hMul) {fun x ↦ x}) (bigO Filter.atTop {fun x ↦ Real.log x / x})) := by
        rw [rightSerial_eq]
        magic_tac
        ring_nf
        rfl
      _ RS[Eq] map (map (pure HAdd.hAdd) {fun x ↦ x}) (bigO Filter.atTop {fun x ↦ Real.log x}) := by
        rw [rightSerial_eq]
        grw [mul_bigO]
        gcongr
        simp
        apply Filter.EventuallyEq.isBigO
        filter_upwards [Filter.eventually_ne_atTop 0]
        intros
        field_simp

-- -- Aha!, this is true if we define O(s) to be {f | ∀ g ∈ s, f =O[l] g}. Is this what we really want? It's not! O(f) contains 0, so O(O(f)) becomes {0}.
-- -- O[l](f x) + O[l](f x) = O[l](f x)
-- lemma bigO_add_bigO' (x : Set (α → ℝ)) : map (map (pure HAdd.hAdd) (bigO l x)) (bigO l x) = bigO l x := by
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
