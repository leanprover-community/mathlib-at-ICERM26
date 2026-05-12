module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

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
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  -- future? ContMDiffVectorBundle also?

-- let s, t be sections of V
variable {f : B → 𝕜} {a : 𝕜} {s t : Π x : B, V x} {u : Set B} {k : ℕ} {x₀ : B}


-- given local trivialisation Ψ,
variable {Ψ : Trivialization F (TotalSpace.proj : TotalSpace F V → B)} [MemTrivializationAtlas Ψ]


-- s vanishes to order k at x relative to Ψ if ...
variable (Ψ s k) in
def vanishesRelativeToOrder (γ : 𝕜 → B) : Prop :=
  ∀ i ≤ k, iteratedDeriv i (secToFun Ψ s ∘ γ) 0 = (0 : F)

/- `vanishesRelativeToOrder` is independent of the choice of trivialisation -/
lemma vanishesRelativeToOrder_change_triv
  {Ψ Ψ' : Trivialization F (TotalSpace.proj : TotalSpace F V → B)}
  [MemTrivializationAtlas Ψ] [MemTrivializationAtlas Ψ'] {γ : 𝕜 → B} :
  vanishesRelativeToOrder s k Ψ γ ↔ vanishesRelativeToOrder s k Ψ' γ := sorry


-- only depends on the value of γ near 0

-- is monotone in k

-- natural map from k-jets to k-1-jets

variable (F s k x₀) in
/-- `s` vanishes to order `k` at `x₀` -/
def vanishesToOrderAt : Prop :=
  ∀ (Ψ : Trivialization F (TotalSpace.proj : TotalSpace F V → B)),
  ∀ (γ : 𝕜 → B), --∀ i ≤ k,
  MemTrivializationAtlas Ψ → x₀ ∈ Ψ.baseSet → γ 0 = x₀ → CMDiffAt k γ 0 →
  vanishesRelativeToOrder s k Ψ γ

-- vanishesToOrderAt only depends on the value in a neighbourhood

-- is monotone in k

variable (I)

-- Note. This particular definition doesn't work in the holomorphic category,
-- would need to switch to a germ-based definition.

-- the sections vanishing to order k form a submodule
variable (V k x₀) in
def foo : Submodule 𝕜 (ContMDiffSection I F k V) where
  carrier := { s | vanishesToOrderAt (I := I) F s k x₀}
  add_mem' hs ht Ψ γ := by
    intro hΨ hx₀ hγ₀ hγ'
    unfold vanishesRelativeToOrder
    intro i' hik'
    specialize hs Ψ γ hΨ hx₀ hγ₀ hγ' i' hik'
    specialize ht Ψ γ hΨ hx₀ hγ₀ hγ' i' hik'
    -- secToFun is linear on an individual fiber(missing lemma)
    -- iteratedDeriv is linear
    -- exercise!
    sorry
  zero_mem' := sorry -- exercise!
  smul_mem' := sorry -- exercise!

variable (V k x₀) in
/-- The module of `k`-jets of sections of `V` at `x₀` -/
def kjets := (ContMDiffSection I F k V) ⧸ (foo I V k x₀)

-- lemma: kjets does not

-- lemma: dimension of the space of k-jets, 1 + r + (r.choose 2) or so
-- perhaps easiest using local trivialisations?

-- given a trivialisation, canonical map identifying k-jets with a suitable direct sum of spaces

-- short exact sequence involving kjets

-- s and t are k,x-equivalence iff their differences vanishes to order k at x
