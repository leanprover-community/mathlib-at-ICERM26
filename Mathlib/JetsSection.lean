import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

import Mathlib.SecToFun

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
variable {f : B → 𝕜} {a : 𝕜} {s t : Π x : B, V x} {u : Set B} {k : ℕ} [hkn : Fact (k ≤ n)] {x₀ : B}


-- given local trivialisation Ψ,
variable {Ψ : Trivialization F (TotalSpace.proj : TotalSpace F V → B)} [MemTrivializationAtlas Ψ]


-- s vanishes to order k at x relative to Ψ if ...
variable (Ψ s k) in
def vanishesRelativeToOrder (γ : 𝕜 → B) : Prop :=
  ∀ i ≤ k, iteratedDeriv i (secToFun Ψ s ∘ γ) 0 = (0 : F)

variable {γ γ' : 𝕜 → B}

private lemma vanishesRelativeToOrder_zero_iff' (γ : 𝕜 → B) : vanishesRelativeToOrder s 0 Ψ γ ↔ Ψ.secToFun s (γ 0) = 0 := by
  simp [vanishesRelativeToOrder]

variable (Ψ) in
/-- A section `s` vanishes to order zero relative to `Ψ` and `γ` iff `s (γ 0) = 0`. -/
--@[simp]
lemma vanishesRelativeToOrder_zero_iff {γ : 𝕜 → B} (hγ : γ 0 ∈ Ψ.baseSet) :
    vanishesRelativeToOrder s 0 Ψ γ ↔ s (γ 0) = 0 := by
  rw [vanishesRelativeToOrder_zero_iff']
  refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
  · -- goal: s (γ 0) = 0
    sorry
  · -- missing API for secToFun, if this is even true??
    --rw [Ψ.secToFun_apply_of_eq]
    --unfold secToFun
    --rw [← mk_proj_snd Ψ ?_] does the wrong direction
    --· simp
    --simp (disch := assumption)
    --grind
    --simp (disch := sorry)
    --dsimp
    --simp [Ψ.secToFun]
    sorry

omit [∀ (x : B), IsTopologicalAddGroup (V x)]
  [∀ (x : B), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
theorem coordChange_secToFun {ψ ψ' : Trivialization F (TotalSpace.proj : TotalSpace F V → B)}
    [MemTrivializationAtlas ψ'] [MemTrivializationAtlas ψ] (b : B) (hb : b ∈ ψ.baseSet) [VectorBundle 𝕜 F V]:
    coordChange ψ ψ' b (secToFun ψ s b) = secToFun ψ' s b := by
  grind [secToFun, coordChange_apply_snd]

omit [∀ (x : B), IsTopologicalAddGroup (V x)]
  [∀ (x : B), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
theorem secToFun_zero {ψ : Trivialization F (TotalSpace.proj : TotalSpace F V → B)}
    [MemTrivializationAtlas ψ] [VectorBundle 𝕜 F V] (b : B) (hb : b ∈ ψ.baseSet) :
    secToFun ψ (fun x => (0 : V x)) b = 0 := by
  simp [secToFun, ((VectorBundle.trivialization_linear' ψ).linear (R := 𝕜) b hb).map_zero]

/- `vanishesRelativeToOrder` is independent of the choice of trivialisation -/
lemma vanishesRelativeToOrder_change_triv
    {Ψ Ψ' : Trivialization F (TotalSpace.proj : TotalSpace F V → B)}
    [MemTrivializationAtlas Ψ] [MemTrivializationAtlas Ψ'] {γ : 𝕜 → B} :
    vanishesRelativeToOrder s k Ψ γ ↔ vanishesRelativeToOrder s k Ψ' γ := by
  suffices ∀ (Ψ Ψ' : Trivialization F (TotalSpace.proj : TotalSpace F V → B))
    [MemTrivializationAtlas Ψ] [MemTrivializationAtlas Ψ'] {γ : 𝕜 → B},
    vanishesRelativeToOrder s k Ψ γ → vanishesRelativeToOrder s k Ψ' γ by
    refine ⟨fun h ↦ this Ψ Ψ' h, fun h ↦ this Ψ' Ψ h⟩
  intro ψ ψ' _ _ γ h i hi
  set postCoordChange := fun b ↦ coordChange ψ ψ' b (secToFun ψ s b)
  have (t) (ht : t ∈ γ⁻¹' ψ.baseSet) : postCoordChange (γ t) = secToFun ψ' s (γ t) := by
    grind [coordChange_secToFun]
  -- This follows from a general theorem
  sorry

-- unused
-- /- `vanishesRelativeToOrder` only depends on the curve `γ` near `0` -/
-- -- TODO bad name!
-- lemma vanishesRelativeToOrder_congr_of_eventuallyEq_γ (heq : γ =ᶠ[𝓝 0] γ') :
--   vanishesRelativeToOrder s k Ψ γ ↔ vanishesRelativeToOrder s k Ψ γ' := sorry

-- -- XXX: is this actually true? the lemma below certainly is
-- /- `vanishesRelativeToOrder` only depends on the section `s` near `x₀` -/
-- lemma vanishesRelativeToOrder_congr_of_eventuallyEq (heq : (T% s) =ᶠ[𝓝 x₀] (T% t)) :
--   vanishesRelativeToOrder s k Ψ γ ↔ vanishesRelativeToOrder t k Ψ γ := sorry

/- `vanishesRelativeToOrder` is monotone in the order of vanishing -/
lemma vanishesRelativeToOrder_mono {l : ℕ} (hs : vanishesRelativeToOrder s k Ψ γ) (hkl : l ≤ k) :
   vanishesRelativeToOrder t l Ψ γ := sorry

variable (I F s k x₀) in
/-- `s` vanishes to order `k` at `x₀` -/
def vanishesToOrderAt : Prop :=
  ∀ (Ψ : Trivialization F (TotalSpace.proj : TotalSpace F V → B)), ∀ (γ : 𝕜 → B),
  MemTrivializationAtlas Ψ → x₀ ∈ Ψ.baseSet → γ 0 = x₀ → CMDiffAt n γ 0 →
  vanishesRelativeToOrder s k Ψ γ

/-- A section `s` vanishes to order zero at `x₀` iff `s x₀ = 0`. -/
@[simp]
lemma vanishesToOrderAt_zero_iff : vanishesToOrderAt I F n s 0 x₀ ↔ s x₀ = 0 := by
  refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
  · let t := trivializationAt F V x₀
    let γ : 𝕜 → B := fun a ↦ x₀
    have hγ₀ : γ 0 = x₀ := by simp [γ]
    have hx₀ : x₀ ∈ t.baseSet := by
      simpa [γ] using FiberBundle.mem_baseSet_trivializationAt' x₀
    rw [← hγ₀, ← vanishesRelativeToOrder_zero_iff t hx₀]
    exact hs t γ (by infer_instance) hx₀ (by simp [γ]) contMDiffAt_const
  · intro Ψ γ hΨ hx₀ hγ₀ hγ
    rw [vanishesRelativeToOrder_zero_iff Ψ (by rwa [hγ₀]), hγ₀, hs]

section Deriv

omit hkn in
lemma iteratedDeriv_congr_of_isOpen
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f₁ f₂ : 𝕜 → F} {s : Set 𝕜} (hs : IsOpen s) {x : 𝕜} (hxs : x ∈ s)
    (h : ∀ x ∈ s, f₁ x = f₂ x) (n : ℕ) :
    iteratedDeriv n f₁ x = iteratedDeriv n f₂ x := by
  rw [← iteratedDerivWithin_of_isOpen hs hxs, ← iteratedDerivWithin_of_isOpen hs hxs]
  exact iteratedDerivWithin_congr h hxs

omit hkn in
lemma iteratedDeriv_congr_of_eventually
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f₁ f₂ : 𝕜 → F} {s : Set 𝕜} {x : 𝕜} (hs : s ∈ 𝓝 x) (h : ∀ x ∈ s, f₁ x = f₂ x) (n : ℕ) :
    iteratedDeriv n f₁ x = iteratedDeriv n f₂ x := by -- not quite the right statement yet!
  obtain ⟨s', hss', hs', hxs'⟩ := mem_nhds_iff.mp hs
  apply iteratedDeriv_congr_of_isOpen hs' hxs' (by grind)

end Deriv

variable {n} in
omit [(x : B) → AddCommGroup (V x)] hkn in
/- `vanishesToOrderAt` only depends on the section `s` near `x₀` -/
lemma vanishesToOrderAt.congr_of_eventually (hs : vanishesToOrderAt I F n s k x₀)
    {u : Set B} (hu : u ∈ 𝓝 x₀) (heq : ∀ x ∈ u, s x = t x) :
    vanishesToOrderAt I F n t k x₀ := by
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

variable {n} in
omit [(x : B) → AddCommGroup (V x)] hkn in
/- `vanishesToOrderAt` only depends on the section `s` near `x₀` -/
lemma vanishesToOrderAt_congr_iff_eventuallyEq
    {u : Set B} (hu : u ∈ 𝓝 x₀) (heq : ∀ x ∈ u, s x = t x) :
    vanishesToOrderAt I F n s k x₀ ↔ vanishesToOrderAt I F n t k x₀ :=
  ⟨fun hs ↦ hs.congr_of_eventually hu heq, fun ht ↦ ht.congr_of_eventually hu (by grind)⟩

variable {n} in
omit [(x : B) → AddCommGroup (V x)] hkn in
/- `vanishesToOrderAt` is monotone in the order of vanishing -/
lemma vanishesToOrderAt_mono {l : ℕ} (hs : vanishesToOrderAt I F n s k x₀) (hkl : l ≤ k) :
    vanishesToOrderAt I F n s l x₀ := by
  intro Ψ γ hΨ hx₀Ψ hγx₀ hγ i hi
  exact hs Ψ γ hΨ hx₀Ψ hγx₀ hγ i (hi.trans hkl)

variable (I)

-- Note. This particular definition doesn't work in the holomorphic category,
-- would need to switch to a germ-based definition.

-- TODO: this seems to be the wrong lemma (as the one below)
omit hkn in
lemma vanishesRelativeToOrder_zero {Ψ : Trivialization F TotalSpace.proj} :
    vanishesRelativeToOrder (fun x ↦ (0 : V x)) k Ψ γ := by
  intro i hik
  have : Ψ.secToFun (fun x ↦ (0 : V x)) = 0 := sorry -- missing API lemma: secToFun_zero
  simp [this]

omit hkn in
variable {n} in
lemma vanishesToOrderAt_zero : vanishesToOrderAt I F n (fun x ↦ (0 : V x)) k x₀ := by
  intro Ψ γ hΨ hx₀ hγ₀ hγ
  exact vanishesRelativeToOrder_zero

-- the sections vanishing to order k form a submodule
variable (V k x₀) in
def foo : Submodule 𝕜 (ContMDiffSection I F n V) where
  carrier := { s | vanishesToOrderAt (I := I) F n s k x₀}
  add_mem' {a b} ha hb Ψ γ := by
    intro hΨ hx₀ hγ₀ hγ'
    unfold vanishesRelativeToOrder
    intro i hik
    specialize ha Ψ γ hΨ hx₀ hγ₀ hγ' i hik
    specialize hb Ψ γ hΨ hx₀ hγ₀ hγ' i hik
    have hik' : (i : WithTop ℕ∞) ≤ k := Nat.cast_le.mpr hik
    -- exercise!
    convert iteratedDeriv_add (n := i) (f := Ψ.secToFun a ∘ γ) (g := Ψ.secToFun b ∘ γ) (x := 0) ?_ ?_
    · -- secToFun is linear on an individual fiber (missing lemma)
      sorry
    · simp [ha, hb]
    · have H : CMDiffAt n (Ψ.secToFun a) (γ 0) := sorry -- missing lemma
      exact ((H.comp 0 hγ').of_le (m := i) (hik'.trans hkn.elim)).contDiffAt
    · have H : CMDiffAt n (Ψ.secToFun b) (γ 0) := sorry -- missing lemma
      exact ((H.comp 0 hγ').of_le (m := i) (hik'.trans hkn.elim)).contDiffAt
  zero_mem' := by
    simp only [mem_setOf_eq, ContMDiffSection.coe_zero]
    exact vanishesToOrderAt_zero _
  smul_mem' := sorry -- exercise!

theorem foo_mono {k l : ℕ} [hln : Fact (l ≤ n)] (hkl : k ≤ l) (x₀) :
    foo (F := F) I V n l x₀ ≤ foo I V n k (hkn := ⟨(Nat.cast_le.mpr hkl).trans hln.elim⟩) x₀ := by
  intro s hs
  exact vanishesToOrderAt_mono hs hkl

variable (V F k x₀) in
/-- The module of `k`-jets of sections of `V` at `x₀` -/
def kjets := (ContMDiffSection I F n V) ⧸ (foo I V n k x₀)
deriving AddCommGroup, Module 𝕜

variable (F V k x₀) in
/-- The canonical linear map from `(k + 1)`-jets to `k`-jets. -/
def kjetsMono [hkn : Fact (k + 1 ≤ n)] (x₀ : B) :
    kjets I F V n (k + 1) (hkn := ⟨Eq.trans_le (Nat.cast_add k 1) hkn.elim⟩) x₀ →ₗ[𝕜]
      kjets I F V n k (hkn :=
        -- should we let `grind` handle this silently?
        ⟨((Nat.cast_le.mpr (Nat.le_add_right k 1)).trans_eq (Nat.cast_add k 1)).trans hkn.elim⟩)
        x₀ :=
  have hk : k ≤ k + 1 := Nat.le_add_right k 1
  Submodule.factor (foo_mono I n (hln := ⟨Eq.trans_le (Nat.cast_add k 1) hkn.elim⟩) hk x₀)

-- xxx: also from l to k? also continuous, when we put a topology?

omit hkn in
/-- The canonical linear map from `(k + 1)`-jets to `k`-jets is surjective. -/
theorem kjetsMono_surjective [hkn : Fact (k + 1 ≤ n)] (x₀ : B) :
    Function.Surjective (kjetsMono I F V n k x₀) :=
  have hk : k ≤ k + 1 := Nat.le_add_right k 1
  Submodule.factor_surjective <|
    foo_mono I n (hln := ⟨Eq.trans_le (Nat.cast_add k 1) hkn.elim⟩) hk x₀

-- lemma: kjets does not

-- lemma: dimension of the space of k-jets, 1 + r + (r.choose 2) or so
-- perhaps easiest using local trivialisations?

-- given a trivialisation, canonical map identifying k-jets with a suitable direct sum of spaces

-- short exact sequence involving kjets

-- s and t are k,x-equivalence iff their differences vanishes to order k at x
