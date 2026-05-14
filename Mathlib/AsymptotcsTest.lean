module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Positivity
public import Mathlib

/-!
# Big O and little o notation
Additional things we need to support:

- Other relations rather than just =, for example ≤, =ᶠ[l], ≪. That is,
  `f x ≤ g x + O(1)`
  `n ! =ᶠ[𝓟 {n | n ≠ 0}] (1 + o(n)) * f n` i.e. the equation holds on some subset.
  `f x =ᶠ[atTop] (1 + o(n)) * g n` i.e. `f` and `g` are equivalent
  `f x ≪ g x + O(x)`

- Constants that are allowed to depend on some specific subset of the variables, i.e.
  $O_{A, ε}(f(x))$
-/

public section

open Real Topology
open Filter

namespace Asymptotics

attribute [refl] isBigO_refl

variable {α β γ δ E : Type*} [SeminormedAddCommGroup E] (l : Filter α)

def bigO (s : Set (α → E)) : Set (α → E) :=
  { f | ∃ (ι : Type) (_ : Fintype ι) (g : ι → (α → E)),
      (∀ i, g i ∈ s) ∧ f =O[l] fun j ↦ ∑ i, ‖g i j‖ }

attribute [push] Classical.skolem

lemma mem_bigO (f : α → E) (s : Set (α → E)) :
    f ∈ bigO l s ↔ ∃ (ι : Type) (_ : Fintype ι) (g : ι → (α → E)),
      (∀ i, g i ∈ s) ∧ f =O[l] fun j ↦ ∑ i, ‖g i j‖ :=
  .rfl

lemma bigO_subset_bigO (s₁ s₂ : Set (α → E)) (h : s₁ ⊆ s₂) : bigO l s₁ ⊆ bigO l s₂ := by
  unfold bigO
  gcongr

@[gcongr]
lemma mem_bigO_mono (s : Set (α → E)) {f g : α → E} (h : f =O[l] g) :
    g ∈ bigO l s → f ∈ bigO l s := by
  simp only [mem_bigO]
  gcongr
  exact h.trans

lemma mem_bigO_empty {f : α → E} : f ∈ bigO l ∅ ↔ f =O[l] fun _ ↦ (0 : ℝ) := by
  rw [mem_bigO]
  constructor
  · rintro ⟨ι, instι, z, hz, hf⟩
    simp only [Set.mem_empty_iff_false] at hz
    have (i : ι) : z i = 0 := by exfalso; exact hz i
    simpa [this] using hf
  · intro h
    use Empty, inferInstance, fun _ _ ↦ 0, nofun
    simpa

lemma subset_bigO (s : Set (α → E)) : s ⊆ bigO l s := by
  intro f hf
  rw [mem_bigO]
  use Unit, inferInstance
  use fun _ ↦ f, fun _ ↦ hf
  simp
  rfl

@[simp, push]
lemma mem_bigO_singleton (f g : α → E) :
    f ∈ bigO l {g} ↔ f =O[l] g := by
  constructor
  · rw [mem_bigO]
    rintro ⟨ι, instι, z, hz, hf⟩
    refine hf.trans ?_
    apply IsBigO.sum
    rintro i -
    apply IsBigO.norm_left
    simp only [Set.mem_singleton_iff] at hz
    rw [hz]
  · intro h
    grw [h, ← subset_bigO]
    exact Set.mem_singleton _

@[simp]
lemma bigO_bigO (s : Set (α → ℝ)) : bigO l (bigO l s) = bigO l s := by
  ext f
  constructor
  · rw [mem_bigO]
    rintro ⟨ι, instι, z, hz, hf⟩
    simp_rw [mem_bigO] at hz
    push ∀ _, _ at hz
    obtain ⟨ι', instι', z', hz', hz⟩ := hz
    rw [mem_bigO]
    use (i : ι) × ι' i, inferInstance
    use fun i ↦ z' i.1 i.2, fun i ↦ hz' i.1 i.2
    grw [hf]
    simp_rw [Fintype.sum_sigma]
    convert IsBigO.sum_congr ?_ using 3
    · symm; exact abs_of_nonneg (by positivity)
    rintro i -
    exact IsBigO.abs_left (hz i)
  · gcongr
    apply subset_bigO

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

@[simp, push]
lemma mem_pure (x : α → β) (y : β) : x ∈ pure y ↔ x = fun _ ↦ y := by
  simp [pure]

-- Question: Is this meaningful if we replace {fun x ↦ x} with a different `Set (ℝ → ℝ)`?
-- exp x = 1 + O[𝓝 0](x)
lemma exp_at_one :
    map (pure exp) {fun x ↦ x} ⊆ map (pure <| HAdd.hAdd 1) (bigO (𝓝 0) {fun x ↦ x}) := by
  intro y
  push _ ∈ _
  simp only [exists_eq_left]
  rintro rfl
  use fun x ↦ Real.exp x - 1
  constructor
  · simpa using Real.exp_sub_sum_range_isBigO_pow 1
  · ring_nf

lemma exp_at_one_ :
    map (pure exp) {fun x ↦ x} ⊆ map (map (pure HAdd.hAdd) (pure 1)) (bigO (𝓝 0) {fun x ↦ x}) := by
  intro y
  push _ ∈ _
  simp only [↓existsAndEq, true_and, and_self]
  rintro rfl
  use fun x ↦ Real.exp x - 1
  constructor
  · simpa using Real.exp_sub_sum_range_isBigO_pow 1
  · ring_nf

lemma exp_at_one' {l : Filter ℝ} {f : ℝ → ℝ} (hf : Filter.Tendsto f l (𝓝 0)) :
    map (pure exp) {f} ⊆ map (pure <| HAdd.hAdd 1) (bigO l {f}) := by
  intro y
  push _ ∈ _
  simp only [exists_eq_left]
  rintro rfl
  use fun x ↦ Real.exp (f x) - 1
  refine ⟨?_, by ring_nf⟩
  simpa using (Real.exp_sub_sum_range_isBigO_pow 1).comp_tendsto hf

section comp

-- These are helper lemmas for composing a function on both sides of an equation involving bigO s

@[simp, push]
lemma Set.image_comp_map (s₁ : Set (α → β → γ)) (s₂ : Set (α → β)) (f : δ → α) :
    Set.image (· ∘ f) (map s₁ s₂) = map (Set.image (· ∘ f) s₁) (Set.image (· ∘ f) s₂) := by
  ext g
  push _ ∈ _
  simp only [↓existsAndEq, and_true, Function.comp_apply]
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
  push _ ∈ _
  rintro ⟨w, h, rfl⟩
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
  · simp only [Set.le_eq_subset, this, Set.image_comp_map, Set.image_pure, Set.image_singleton] at h
    grw [Set.image_comp_isBigO _ hf] at h
    exact h
  · apply Set.monotone_image

lemma exp_at_one_set {l : Filter ℝ} {s : Set (ℝ → ℝ)}
    (hs : ∀ f ∈ s, Filter.Tendsto f l (𝓝 0)) :
    map (pure exp) s ⊆ map (pure <| HAdd.hAdd 1) (bigO l s) := by
  /- Written partly using Claude, but I want to see if we can do this more systematically? -/
  conv_lhs => rw [← Set.biUnion_of_singleton s]
  push map
  simp only [Set.iUnion_subset_iff]
  rintro f hf
  grw [exp_at_one'' (hs _ hf), bigO_subset_bigO]
  simp [hf]

-- O[l](f x) + O[l](f x) = O[l](f x)
lemma bigO_add_bigO_self (f : α → ℝ) :
    map (map (pure HAdd.hAdd) (bigO l {f})) (bigO l {f}) = bigO l {f} := by
  ext y
  push _ ∈ _
  constructor
  · simp only [↓existsAndEq, and_true, true_and]
    rintro ⟨g, hg, g', hg', rfl⟩
    exact hg.add hg'
  · intro hy
    simp only [↓existsAndEq, and_true, true_and]
    use y, hy, fun _ ↦ 0
    simp only [add_zero, and_true]
    exact isBigO_zero f l

lemma map_eq (s₁ : Set (α → β → γ)) (s₂ : Set (α → β)) :
    map s₁ s₂ = ⋃ i₁ ∈ s₁, ⋃ i₂ ∈ s₂, {fun x ↦ i₁ x (i₂ x)} := by
  ext x
  simp [map]

lemma singleton_eq_map_singleton_singleton (f : α → β → γ) (a : α → β) :
    ({fun x ↦ f x (a x)} : Set (α → γ)) = map {f} {a} := by
  simp [map_eq]

macro "magic_tac" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [map_eq, mem_pure, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left,
    Set.mem_iUnion, exists_prop, Set.iUnion_exists, Set.biUnion_and'] $[$loc]?)

lemma mul_bigO {s₁ s₂ : Set (α → ℝ)} :
    map (map (pure HMul.hMul) s₁) (bigO l s₂) ⊆ bigO l (map (map (pure HMul.hMul) s₁) s₂) := by
  magic_tac
  intro x
  push _ ∈ _
  rw [mem_bigO] at *
  rintro ⟨p, hp, f, ⟨ι, instι, g, hg, hf⟩, rfl⟩
  use ι, instι
  use fun i x ↦ p x * g i x
  constructor
  · intro i
    push _ ∈ _
    use p, hp, g i, hg i
  · simp_rw [norm_mul, ← Finset.mul_sum]
    apply IsBigO.mul (IsBigO.norm_right (by rfl)) hf

lemma bigO_mul {s₁ s₂ : Set (α → ℝ)} :
    map (map (pure HMul.hMul) (bigO l s₁)) s₂ ⊆ bigO l (map (map (pure HMul.hMul) s₁) s₂) := by
  have := mul_bigO (s₁ := s₂) (s₂ := s₁) (l := l)
  magic_tac at *
  convert this using 1 <;>
  · rw [Set.iUnion₂_comm]
    simp_rw [mul_comm]

lemma bigO_add_bigO (s₁ s₂ : Set (α → E)) :
    map (map (pure HAdd.hAdd) (bigO l s₁)) (bigO l s₂) = bigO l (s₁ ∪ s₂) := by
  magic_tac
  ext f
  push _ ∈ _
  simp_rw [mem_bigO]
  constructor
  · rintro ⟨f₁, ⟨ι₁, instι₁, g₁, hg₁, hf₁⟩, f₂, ⟨ι₂, instι₂, g₂, hg₂, hf₂⟩, rfl⟩
    use ι₁ ⊕ ι₂, inferInstance
    use Sum.rec g₁ g₂, by simp [*]
    simp only [Fintype.sum_sum_type]
    convert IsBigO.add_add ?_ ?_ using 3
    · symm; exact abs_of_nonneg (by positivity)
    · symm; exact abs_of_nonneg (by positivity)
    · exact hf₁
    · exact hf₂
  · rintro ⟨ι, instι, g, hg, hf⟩
    rw [isBigO_iff'] at hf
    obtain ⟨c, hc, hf⟩ := hf
    simp (disch := positivity) only [norm_eq_abs, abs_of_nonneg] at hf
    classical
    let ι₁ : Type := {i // g i ∈ s₁}
    let ι₂ : Type := {i // g i ∉ s₁}
    let g₁ := fun j ↦ ∑ i : ι₁, ‖g i j‖
    let g₂ := fun j ↦ ∑ i : ι₂, ‖g i j‖
    have (j : α) : ∑ i : ι, ‖g i j‖ = g₁ j + g₂ j := by
      symm
      rw [Fintype.sum_subtype_add_sum_subtype (f := (‖g · j‖))]
    simp_rw [this] at hf
    use fun j ↦ if g₁ j < g₂ j then 0 else f j
    constructor; swap
    · use ι₁, inferInstance, fun i ↦ g i, fun ⟨i, hi⟩ ↦ by simpa using hi
      simp_rw [isBigO_iff, norm_eq_abs]
      use c * 2
      filter_upwards [hf] with i hf
      by_cases h : g₁ i < g₂ i <;> simp only [h, ↓reduceIte, norm_zero]
      · positivity
      · grw [hf, le_of_not_gt h, ← two_mul, mul_assoc, ← le_abs_self]
    use fun j ↦ if g₁ j < g₂ j then f j else 0
    constructor; swap
    · use ι₂, inferInstance, fun i ↦ g i, fun ⟨i, hi⟩ ↦ by grind
      simp_rw [isBigO_iff, norm_eq_abs]
      use c * 2
      filter_upwards [hf] with i hf
      by_cases h : g₁ i < g₂ i <;> simp only [h, ↓reduceIte, norm_zero]
      · grw [hf, h, ← two_mul, mul_assoc, ← le_abs_self]
      · positivity
    ext i
    by_cases h : g₁ i < g₂ i <;> simp [h]

section RightSerial

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

lemma rightSerial_of_subset {r : α → α → Prop} {a b : Set α} (refl : ∀ x, r x x) (hab : a ⊆ b) :
    a RS[r] b := by
  intro x hx
  exact ⟨x, hab hx, refl x⟩

open Lean Meta
@[gcongr_forward]
public meta def _root_.Mathlib.Tactic.GCongr.exactRSOfSubset :
    Mathlib.Tactic.GCongr.ForwardExt where
  eval h goal := do
    let pf ← mkConstWithFreshMVarLevels ``rightSerial_of_subset
    let (xs, _, _) ← forallMetaTelescope (← inferType pf)
    xs.back!.mvarId!.assignIfDefEq h
    goal.assignIfDefEq (mkAppN pf xs)
    let (_, reflGoal) ← xs[4]!.mvarId!.intro `x
    reflGoal.applyRfl

@[refl]
lemma rightSerial_rfl {r : α → α → Prop} [Std.Refl r] {a : Set α} : a RS[r] a :=
  rightSerial_of_subset refl subset_rfl

@[simp]
lemma rightSerial_eq (a b : Set α) : (a RS[Eq] b) ↔ a ⊆ b := by
  unfold RightSerial
  grind

@[simp, gcongr]
lemma RightSerial.singleton_RS_singleton {r : α → α → Prop} (a : α) (b : α) :
    ({a} RS[r] {b}) ↔ r a b := by
  unfold RightSerial
  simp

/- Written by Claude -/
@[gcongr]
lemma RightSerial.iUnion_RS_iUnion {ι : Sort*} {r : α → β → Prop} {s : ι → Set α} {t : ι → Set β}
    (h : ∀ i, s i RS[r] t i) : (⋃ i, s i) RS[r] (⋃ i, t i) := by
  rintro x ⟨_, ⟨i, rfl⟩, hx⟩
  obtain ⟨y, hy, hxy⟩ := h i x hx
  exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, hxy⟩

class MapClass {α β γ : Type*} (r : (α → γ) → (α → γ) → Prop)
    (r₁ : outParam ((α → β → γ) → (α → β → γ) → Prop))
    (r₂ : outParam ((α → β) → (α → β) → Prop)) where
  imp {f₁ f₂ f₁' f₂'} : r₁ f₁ f₁' → r₂ f₂ f₂' → r (fun x ↦ f₁ x (f₂ x)) (fun x ↦ f₁' x (f₂' x))

@[gcongr]
lemma map_rightSerial_map {s₁ s₁' : Set (α → β → γ)} {s₂ s₂' : Set (α → β)}
    {r r₁ r₂} [MapClass r r₁ r₂] (h₁ : s₁ RS[r₁] s₁') (h₂ : s₂ RS[r₂] s₂') :
    map s₁ s₂ RS[r] map s₁' s₂' := by
  rintro g ⟨f₁, hf₁, f₂, hf₂, rfl⟩
  obtain ⟨f₁', hf₁', hff₁⟩ := h₁ f₁ hf₁
  obtain ⟨f₂', hf₂', hff₂⟩ := h₂ f₂ hf₂
  refine ⟨fun x ↦ f₁' x (f₂' x), ⟨f₁', hf₁', f₂', hf₂', rfl⟩, ?_⟩
  exact MapClass.imp hff₁ hff₂

instance :
    MapClass (α := α) (β := β) (γ := γ) (EventuallyEq l) (EventuallyEq l) (EventuallyEq l) where
  imp h₁ h₂ := by
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    simp [hx₁, hx₂]

instance : MapClass (α := α) (β := β) (γ := γ) Eq Eq Eq where
  imp h₁ h₂ := by simp [h₁, h₂]

@[gcongr]
lemma bigO_subset_bigO' {s₁ s₂ : Set (α → ℝ)} (h : s₁ RS[(· =O[l] ·)] s₂) :
    bigO l s₁ ⊆ bigO l s₂ := by
  nth_rw 2 [← bigO_bigO]
  apply bigO_subset_bigO
  intro f hf
  obtain ⟨g, hg, hf⟩ := h f hf
  grw [hf, ← subset_bigO]
  exact hg

@[gcongr]
lemma RightSerial.bigO_mono {s₁ s₂ : Set (α → ℝ)} (h : s₁ RS[(· =O[l] ·)] s₂) :
    bigO l s₁ RS[Eq] bigO l s₂ := by
  rw [rightSerial_eq]
  exact bigO_subset_bigO' l h

end RightSerial

-- O[l](f x) + O[l](f x) = O[l](f x)
lemma bigO_add_bigO_set (f : Set (α → ℝ)) :
    map (map (pure HAdd.hAdd) (bigO l f)) (bigO l f) = bigO l f := by
  rw [bigO_add_bigO, Set.union_self]

lemma bigO_add_bigO_eq_left (s₁ s₂ : Set (α → ℝ)) (h : bigO l s₂ ⊆ bigO l s₁) :
    map (map (pure HAdd.hAdd) (bigO l s₁)) (bigO l s₂) = bigO l s₁ := by
  apply subset_antisymm
  · grw [h, bigO_add_bigO_set]
  · grw [bigO_add_bigO, ← Set.subset_union_left]

lemma bigO_add_bigO_eq_right (s₁ s₂ : Set (α → ℝ)) (h : bigO l s₁ ⊆ bigO l s₂) :
    map (map (pure HAdd.hAdd) (bigO l s₁)) (bigO l s₂) = bigO l s₂ := by
  apply subset_antisymm
  · grw [h, bigO_add_bigO_set]
  · grw [bigO_add_bigO, ← Set.subset_union_right]


section Meta

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

end Meta

/-
  (n+1)^(e^(1/n))
  = (n+1)^(1 + O(1/n)) := _
  = exp ( (log n + O(1/n)) * (1 + O(1/n)) ) := _
  = exp (log n + O(log n/n)) := _
  = n * (1 + O(log n/n)) := _
  = n + O(log n) := _
-/
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
        magic_tac
        ring_nf
        rfl
      _ RS[Eq] map (map (pure HAdd.hAdd) {fun x ↦ x}) (bigO Filter.atTop {fun x ↦ Real.log x}) := by
        grw [mul_bigO]
        gcongr
        simp [RightSerial]
        apply Filter.EventuallyEq.isBigO
        filter_upwards [Filter.eventually_ne_atTop 0]
        intros
        field_simp

end Asymptotics
