module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

public import Mathlib.SecToFun

@[expose] public noncomputable section

open Bundle NormedSpace Set Trivialization
open scoped Manifold ContDiff Topology

-- V is a vector bundle over M, with model fiber F
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : B, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] (n : WithTop ℕ∞)
  -- future? ContMDiffVectorBundle also?

-- let s, t be sections of V
variable {f : B → 𝕜} {a : 𝕜} {s t : Π x : B, V x} {u : Set B} {k : ℕ} {x₀ : B}


-- given local trivialisation Ψ,
variable {Ψ : Trivialization F (TotalSpace.proj : TotalSpace F V → B)} [MemTrivializationAtlas Ψ]


-- s vanishes to order k at x relative to Ψ if ...
variable (Ψ s k) in
def vanishesRelativeToOrder (γ : 𝕜 → B) : Prop :=
  ∀ i ≤ k, iteratedDeriv i (secToFun Ψ s ∘ γ) 0 = (0 : F)

variable {γ γ' : 𝕜 → B}

/- `vanishesRelativeToOrder` is independent of the choice of trivialisation -/
lemma vanishesRelativeToOrder_change_triv
  {Ψ Ψ' : Trivialization F (TotalSpace.proj : TotalSpace F V → B)}
  [MemTrivializationAtlas Ψ] [MemTrivializationAtlas Ψ'] {γ : 𝕜 → B} :
  vanishesRelativeToOrder s k Ψ γ ↔ vanishesRelativeToOrder s k Ψ' γ := sorry

/- `vanishesRelativeToOrder` only depends on the curve `γ` near `0` -/
-- TODO bad name!
lemma vanishesRelativeToOrder_congr_of_eventuallyEq_γ (heq : γ =ᶠ[𝓝 0] γ') :
  vanishesRelativeToOrder s k Ψ γ ↔ vanishesRelativeToOrder s k Ψ γ' := sorry

-- XXX: is this actually true? the lemma below certainly is
/- `vanishesRelativeToOrder` only depends on the section `s` near `x₀` -/
lemma vanishesRelativeToOrder_congr_of_eventuallyEq (heq : (T% s) =ᶠ[𝓝 x₀] (T% t)) :
  vanishesRelativeToOrder s k Ψ γ ↔ vanishesRelativeToOrder t k Ψ γ := sorry

/- `vanishesRelativeToOrder` is monotone in the order of vanishing -/
-- TODO: this is only true/easy to prove under certain conditions!
lemma vanishesRelativeToOrder_mono {l : ℕ} (hs : vanishesRelativeToOrder s k Ψ γ) (hkl : l ≤ k) :
   vanishesRelativeToOrder t l Ψ γ := sorry

variable (I F s k x₀) in
/-- `s` vanishes to order `k` at `x₀` -/
def vanishesToOrderAt : Prop :=
  ∀ (Ψ : Trivialization F (TotalSpace.proj : TotalSpace F V → B)), ∀ (γ : 𝕜 → B),
  MemTrivializationAtlas Ψ → x₀ ∈ Ψ.baseSet → γ 0 = x₀ → CMDiffAt k γ 0 →
  vanishesRelativeToOrder s k Ψ γ

section Deriv

-- see Filter.EventuallyEq.iteratedDerivWithin and iteratedDerivWithin_congr,
-- find the right statement and complete the proof!
lemma iteratedDerivWithin_congr_of_eventually
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f₁ f₂ : 𝕜 → F} {s : Set 𝕜} {x : 𝕜} (hxt : x ∈ s) (h : ∀ x ∈ s, f₁ x = f₂ x) (n : ℕ) :
    iteratedDerivWithin n f₁ s x = iteratedDerivWithin n f₂ s x := by
  apply iteratedDerivWithin_congr h hxt

lemma iteratedDeriv_congr_of_eventually
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f₁ f₂ : 𝕜 → F} {s : Set 𝕜} {x : 𝕜} (hs : s ∈ 𝓝 x) (h : ∀ x ∈ s, f₁ x = f₂ x) (n : ℕ) :
    iteratedDeriv n f₁ x = iteratedDeriv n f₂ x := by -- not quite the right statement yet!
  simp_all [← nhdsWithin_univ, ← iteratedDerivWithin_univ]
  sorry -- apply iteratedDerivWithin_congr_of_eventually (t := s) (s := univ) --(by simp)

end Deriv

/- `vanishesToOrderAt` only depends on the section `s` near `x₀` -/
lemma vanishesToOrderAt.congr_of_eventually (hs : vanishesToOrderAt I F s k x₀)
    {u : Set B} (hu : u ∈ 𝓝 x₀) (heq : ∀ x ∈ u, s x = t x) :
    vanishesToOrderAt I F t k x₀ := by
  intro Ψ γ hΨ hxΨ hγ0 hγ i hik
  specialize hs Ψ γ hΨ hxΨ hγ0 hγ i hik
  let u' := γ ⁻¹' u
  have hu' : u' ∈ 𝓝 0 := hγ.continuousAt.preimage_mem_nhds (hγ0 ▸ hu)
  have heq' : ∀ y ∈ u', (Ψ.secToFun t ∘ γ) y = (Ψ.secToFun s ∘ γ) y := by
    intro y hy
    have heq'' : ∀ y' ∈ u, Ψ.secToFun s y' = Ψ.secToFun t y' := by
      intro y' hy'
      -- missing API lemma:
      simp [secToFun, heq _ hy']
    exact (heq'' (γ y) (by grind)).symm
  rw [← hs]
  exact iteratedDeriv_congr_of_eventually hu' heq' _

/- `vanishesToOrderAt` only depends on the section `s` near `x₀` -/
lemma vanishesToOrderAt_congr_iff_eventuallyEq
    {u : Set B} (hu : u ∈ 𝓝 x₀) (heq : ∀ x ∈ u, s x = t x) :
    vanishesToOrderAt I F s k x₀ ↔ vanishesToOrderAt I F t k x₀ :=
  ⟨fun hs ↦ hs.congr_of_eventually hu heq, fun ht ↦ ht.congr_of_eventually hu (by grind)⟩

/- `vanishesToOrderAt` is monotone in the order of vanishing -/
-- TODO: this is only true/easy to prove under certain conditions!
lemma vanishesToOrderAt_mono {l : ℕ} (hs : vanishesToOrderAt I F s k x₀) (hkl : l ≤ k) :
    vanishesToOrderAt I F s l x₀ := by
  sorry

variable (I)

-- Note. This particular definition doesn't work in the holomorphic category,
-- would need to switch to a germ-based definition.

-- TODO: this seems to be the wrong lemma (as the one below)
lemma vanishesRelativeToOrder_zero {Ψ : Trivialization F TotalSpace.proj} :
    vanishesRelativeToOrder (fun x ↦ (0 : V x)) k Ψ γ := by
  intro i hik
  have : Ψ.secToFun (fun x ↦ (0 : V x)) = 0 := sorry -- missing API lemma: secToFun_zero
  simp [this]

lemma vanishesToOrderAt_zero : vanishesToOrderAt I F (fun x ↦ (0 : V x)) k x₀ := by
  intro Ψ γ hΨ hx₀ hγ₀ hγ
  exact vanishesRelativeToOrder_zero

-- the sections vanishing to order k form a submodule
variable (V k x₀) in
def foo : Submodule 𝕜 (ContMDiffSection I F n V) where
  carrier := { s | vanishesToOrderAt (I := I) F s k x₀}
  add_mem' hs ht Ψ γ := by
    intro hΨ hx₀ hγ₀ hγ'
    unfold vanishesRelativeToOrder
    intro i' hik'
    specialize hs Ψ γ hΨ hx₀ hγ₀ hγ' i' hik'
    specialize ht Ψ γ hΨ hx₀ hγ₀ hγ' i' hik'
    -- secToFun is linear on an individual fiber (missing lemma)
    -- iteratedDeriv is linear
    -- exercise!
    sorry
  zero_mem' := by
    simp only [mem_setOf_eq, ContMDiffSection.coe_zero]
    exact vanishesToOrderAt_zero _
  smul_mem' := sorry -- exercise!

theorem foo_mono {n k l} (hkl : k ≤ l) : foo (F := F) I V n l x₀ ≤ foo I V n k x₀ := by
  intro s hs
  exact vanishesToOrderAt_mono hs hkl

variable (V F k x₀) in
/-- The module of `k`-jets of sections of `V` at `x₀` -/
def kjets := (ContMDiffSection I F n V) ⧸ (foo I V n k x₀)
deriving AddCommGroup, Module 𝕜

variable (F V k x₀) in
/-- The canonical linear map from `(k + 1)`-jets to `k`-jets. -/
def kjetsMono : kjets I F V n (k + 1) x₀ →ₗ[𝕜] kjets I F V n k x₀ :=
  have hk : k ≤ k + 1 := Nat.le_add_right k 1
  Submodule.factor (foo_mono I hk)

-- xxx: also from l to k? also continuous, when we put a topology?

/-- The canonical linear map from `(k + 1)`-jets to `k`-jets is surjective. -/
theorem kjetsMono_surjective : Function.Surjective (kjetsMono I F V n k x₀) :=
  have hk : k ≤ k + 1 := Nat.le_add_right k 1
  Submodule.factor_surjective (foo_mono I hk)

-- lemma: kjets does not

-- lemma: dimension of the space of k-jets, 1 + r + (r.choose 2) or so
-- perhaps easiest using local trivialisations?

-- given a trivialisation, canonical map identifying k-jets with a suitable direct sum of spaces

-- short exact sequence involving kjets

-- s and t are k,x-equivalence iff their differences vanishes to order k at x
