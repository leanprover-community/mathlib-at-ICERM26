/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.Basic


/-! # Riemann–Stieltjes integration by parts

In this file we establish how integration by parts API for the Riemann–Stieltjes integral
`∫⟨B⟩ x in a..b, f x ∂g` defined in `Analysis.BoxIntegral.Stieltjes.Defs`.

-/

@[expose] public section

open scoped BigOperators
open BoxIntegral


/-! ## Helper lemmas

These should be upstreamed to Mathlib eventually.
-/

@[simp]
theorem BoundedVariationOn.subsingleton {α : Type*} [LinearOrder α] {E : Type*}
    [PseudoEMetricSpace E] (f : α → E) {s : Set α} (hs : s.Subsingleton) :
  BoundedVariationOn f s := by
    simp [BoundedVariationOn, hs]

theorem MonotoneOn.boundedVariationOn {a b : ℝ} {f : ℝ → ℝ}
    (hf : MonotoneOn f (.Icc a b)) :
    BoundedVariationOn f (.Icc a b) := by
  rcases lt_trichotomy a b with (hab | rfl | hab)
  · convert hf.locallyBoundedVariationOn a b _ _ <;> grind
  · simp
  simp [hab]

theorem BoundedVariationOn.neg {α : Type*} [LinearOrder α] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) :
    BoundedVariationOn (- f ·) s := by
  have : LipschitzOnWith 1 (-· : E → E) .univ := by intro _ _ _ _; simp
  exact LipschitzOnWith.comp_boundedVariationOn this (by aesop) hf

theorem BoundedVariationOn.neg_iff {α : Type*} [LinearOrder α] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : α → E) (s : Set α) :
    BoundedVariationOn f s ↔ BoundedVariationOn (- f ·) s :=
  ⟨fun hf ↦ hf.neg, fun hf ↦ by simpa using hf.neg⟩

theorem AntitoneOn.boundedVariationOn {a b : ℝ} {f : ℝ → ℝ}
    (hf : AntitoneOn f (.Icc a b)) :
    BoundedVariationOn f (.Icc a b) := by
  have : AntitoneOn (-· : ℝ → ℝ) .univ  := by intro _ _ _ _; aesop
  convert ((this.comp hf _).boundedVariationOn).neg using 1 <;> aesop


namespace BoxIntegral.TaggedDivision

/-! ## Partitions -/
namespace DualPartition

def x (π : TaggedDivision) : Fin (π.N + 2) → ℝ :=
  Fin.cons (π.x 0) (Fin.snoc π.tag (π.x (Fin.last π.N)))

@[simp]
theorem x_first (π : TaggedDivision) : x π 0 = π.x 0 := by
  simp [x]

@[simp]
theorem x_last (π : TaggedDivision) : x π (Fin.last (π.N + 1)) = π.x (Fin.last π.N) := by
  simp [x]

end DualPartition

def DualPartition (π : TaggedDivision) : TaggedDivision where
  N := π.N + 1
  tag := π.x
  x := DualPartition.x π

@[simp]
theorem DualPartition_first (π : TaggedDivision) : π.DualPartition.x 0 = π.x 0 := by
  exact DualPartition.x_first π

@[simp]
theorem DualPartition_last (π : TaggedDivision) :
    π.DualPartition.x (Fin.last π.DualPartition.N) = π.x (Fin.last π.N) := by
  exact DualPartition.x_last π

def RiemannStieltjesSum (π : TaggedDivision) (f g : ℝ → ℝ) : ℝ :=
  ∑ i : Fin π.N, f (π.tag i) * (g (π.x i.succ) - g (π.x i.castSucc))

end BoxIntegral.TaggedDivision


namespace BoxIntegral.TaggedDivision.RiemannStieltjesSum

@[simp]
theorem eq_zero_of_N_eq_zero (π : TaggedDivision) (hπ : π.N = 0) (f g : ℝ → ℝ) :
    π.RiemannStieltjesSum f g = 0 := by
  rcases π with ⟨⟨N, x⟩, tag⟩
  dsimp at hπ ⊢
  subst N
  simp [TaggedDivision.RiemannStieltjesSum]

theorem eq_dropLast_add
    (π : TaggedDivision) (hN : 0 < π.N) (f g : ℝ → ℝ) :
      π.RiemannStieltjesSum f g =
      π.dropLast.RiemannStieltjesSum f g +
      f (π.tag ⟨π.N - 1, by lia⟩) *
        (g (π.x (Fin.last π.N)) - g (π.x ⟨π.N - 1, by lia⟩)) := by
  rcases π with ⟨⟨N, x⟩, tag⟩
  dsimp [RiemannStieltjesSum, dropLast] at hN ⊢
  cases N with
  | zero => lia
  | succ n =>
      rw [Fin.sum_univ_castSucc]
      congr

theorem snoc (π : TaggedDivision) (c t : ℝ) (f g : ℝ → ℝ) :
    (π.snoc c t).RiemannStieltjesSum  f g =
      π.RiemannStieltjesSum  f g + f t * (g c - g (π.x (Fin.last π.N))) := by
  rcases π with ⟨⟨N, x⟩, tag⟩
  dsimp [RiemannStieltjesSum, TaggedDivision.snoc, BoxIntegral.OrderedDivision.snoc]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hs : i.castSucc.succ = i.succ.castSucc := by ext; simp
    have hxs : @Fin.snoc (N + 1) (fun _ => ℝ) x c i.castSucc.succ = x i.succ := by
      rw [hs, Fin.snoc_castSucc]
    rw [hxs]
    simp [Fin.snoc_castSucc]
  · simp [Fin.snoc_last, Fin.snoc_castSucc]

theorem removeDuplicates
    (π : TaggedDivision) (f g : ℝ → ℝ) :
    π.removeDuplicates.RiemannStieltjesSum f g =
      π.RiemannStieltjesSum f g := by
  revert f g
  induction π using TaggedDivision.recOnDropLast with
  | zero π h0 =>
    intro f g
    rw [TaggedDivision.removeDuplicates.of_N_eq_zero π h0]
  | step π hN ih =>
    intro f g
    have h0 : ¬π.N = 0 := by lia
    let y := π.x ⟨π.N - 1, by lia⟩
    let z := π.x (Fin.last π.N)
    let t := π.tag ⟨π.N - 1, by lia⟩
    let σ := π.dropLast.removeDuplicates
    have hσ_last : σ.x (Fin.last σ.N) = y := by
      dsimp [σ]
      rw [TaggedDivision.removeDuplicates.last π.dropLast]
      exact π.dropLast_last
    have hrec :
        σ.RiemannStieltjesSum f g =
          π.dropLast.RiemannStieltjesSum f g := by
      dsimp [σ]
      exact ih f g
    have hdrop := eq_dropLast_add π hN f g
    by_cases h : y = z
    · rw [TaggedDivision.removeDuplicates.of_last_eq π hN (by simpa [y, z] using h)]
      rw [hrec, hdrop]
      simp [y, z, h]
    · rw [TaggedDivision.removeDuplicates.of_last_ne π hN (by simpa [y, z] using h)]
      rw [snoc σ z t f g, hrec, hdrop]
      simp [hσ_last, y, z, t]

theorem by_parts (π : TaggedDivision) (f g : ℝ → ℝ) :
    π.RiemannStieltjesSum f g =
      (π.DualPartition).RiemannStieltjesSum g f := by sorry

end BoxIntegral.TaggedDivision.RiemannStieltjesSum
namespace mynamespace

/-! ## One-dimensional interval partitions

API for one-dimensional partitions and tagged partitions
-/

open BoxIntegral

noncomputable def toPartition {N : ℕ} {a b : ℝ}
    (x : Fin (N + 1) → ℝ) (hx : StrictMono x)
    (ha : (x 0) = a) (hb : x (Fin.last N) = b) : Prepartition (Ioc a b) where
      boxes := (Finset.univ : Finset (Fin N)).map
        ⟨fun i ↦ Ioc (x i.castSucc) (x i.succ), by
          intro i j hij
          apply Fin.castSucc_injective
          exact hx.injective <| by
            have h := congrFun (congrArg Box.lower hij) 0
            simpa [Ioc.lower (hx i.castSucc_lt_succ),
              Ioc.lower (hx j.castSucc_lt_succ)] using h⟩
      le_of_mem' := by
        intro J hJ
        rw [Finset.mem_map] at hJ
        obtain ⟨i, _, rfl⟩ := hJ
        have hi := hx i.castSucc_lt_succ
        have h0 : a ≤ x i.castSucc := ha ▸ hx.monotone i.castSucc.zero_le
        have hN : x i.succ ≤ b := hb ▸ hx.monotone i.succ.le_last
        exact (Ioc_le_Ioc_iff (h0.trans_lt (hi.trans_le hN)) hi).mpr ⟨h0, hN⟩
      --TODO(bmgeorgiev): Golf the disjointness proof.
      pairwiseDisjoint := by
        intro _ hJ _ hK hne
        rw [Finset.mem_coe, Finset.mem_map] at hJ hK
        obtain ⟨i, _, rfl⟩ := hJ
        obtain ⟨j, _, rfl⟩ := hK
        simp only [Function.Embedding.coeFn_mk, Function.onFun, Box.disjoint_iff₁,
          Ioc.lower₁ (hx i.castSucc_lt_succ), Ioc.upper₁ (hx i.castSucc_lt_succ),
          Ioc.lower₁ (hx j.castSucc_lt_succ), Ioc.upper₁ (hx j.castSucc_lt_succ)]
        rcases lt_trichotomy i j with hij | rfl | hji
        · exact Or.inl (hx.monotone (Fin.succ_le_castSucc_iff.mpr hij))
        · exact absurd rfl hne
        · exact Or.inr (hx.monotone (Fin.succ_le_castSucc_iff.mpr hji))


noncomputable def toTaggedPartition {N : ℕ} {a b : ℝ}
    (x : Fin (N + 1) → ℝ) (hx : StrictMono x)
    (y : Fin N → ℝ) (hy : ∀ i : Fin N,  (x i.castSucc ≤ y i) ∧ (y i ≤ x i.succ))
    (ha : (x 0) = a) (hb : x (Fin.last N) = b) :
    TaggedPrepartition (Ioc a b) :=
    {toPartition x hx ha hb with
      tag := by
        classical
        exact fun J _ ↦
          if h : ∃ i : Fin N, Ioc (x i.castSucc) (x i.succ) = J then y h.choose else a
      tag_mem_Icc := by sorry
    }


theorem toPartition_isPartition {N : ℕ} {a b : ℝ} (hab : a < b)
    (x : Fin (N + 1) → ℝ) (hx : StrictMono x)
    (ha : (x 0) = a) (hb : x (Fin.last N) = b) :
    (toPartition x hx ha hb).IsPartition := by
  sorry


theorem fromPartition
    {a b : ℝ} (hab : a < b)
    (π : Prepartition (Ioc a b))
    (hπ : π.IsPartition) :
    letI N := Finset.card π.boxes
    ∃ (x : Fin (N + 1) → ℝ) (hx : StrictMono x) (ha : (x 0) = a) (hb : x (Fin.last N) = b),
     π = toPartition x hx ha hb := by
  sorry

theorem fromTaggedPartition
    {a b : ℝ} (hab : a < b)
    (π : TaggedPrepartition (Ioc a b))
    (hπ : π.IsPartition) :
    ∃ (N : ℕ) (x : Fin (N + 1) → ℝ) (hx : StrictMono x)
      (ha : (x 0) = a) (hb : x (Fin.last N) = b)
      (y : Fin N → ℝ) (hy : ∀ i : Fin N, (x i.castSucc ≤ y i) ∧ (y i ≤ x i.succ)),
      π.toPrepartition = toPartition x hx ha hb ∧
        ∀ i : Fin N, y i = π.tag (Ioc (x i.castSucc) (x i.succ)) 0 := by
  sorry

open TaggedPrepartition
variable {E : Type} {F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem taggedSum_eq_integralSum {N : ℕ} {a b : ℝ} (hab : a < b)
    (x : Fin (N + 1) → ℝ) (hx : StrictMono x)
    (y : Fin N → ℝ) (hy : ∀ i : Fin N,  (x i.castSucc ≤ y i) ∧ (y i ≤ x i.succ))
    (ha : (x 0) = a) (hb : x (Fin.last N) = b)
    (vol : (Fin 1) →ᵇᵃ E →L[ℝ] F)
    (f :  ℝ → E):
    integralSum (fun x => (f (x 1))) vol (toTaggedPartition x hx y hy ha hb) =
      Finset.sum (Finset.univ)
        (fun i: Fin N ↦ (vol (Ioc (x i.succ) (x i.castSucc))) (f (y i))) := by
  sorry

end mynamespace

namespace BoxIntegral

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {a b : ℝ} {B : E →L[ℝ] F →L[ℝ] G} {f : ℝ → E} {g : ℝ → F} {L : G} {c : E}

/-- Theorem A.2 of Montgomery Vaughan: if ∫ₐᵇ f dg exists, then ∫ₐᵇ g df exists and
∫ₐᵇ g df = g(b) * f(b) - g(a) * f(a) - ∫ₐᵇ f dg. -/
theorem HasStieltjesIntegral.by_parts (hL : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral a b B.flip g f (B (f b) (g b) - B (f a) (g a) - L) := by sorry

theorem StieltjesIntegrable.by_parts (h : StieltjesIntegrable a b B f g) :
    StieltjesIntegrable a b B.flip g f := ⟨_, h.hasStieltjesIntegral.by_parts⟩

theorem StieltjesIntegrable.symm_right
  : StieltjesIntegrable a b B f g ↔ StieltjesIntegrable a b B.flip g f := ⟨by_parts, by_parts⟩

theorem stieltjesIntegral.by_parts (h : StieltjesIntegrable a b B f g) :
    ∫⟨B.flip⟩ x in a..b, g x ∂f = B (f b) (g b) - B (f a) (g a) - ∫⟨B⟩ x in a..b, f x ∂g := by
  rw [h.hasStieltjesIntegral.by_parts.stieltjesIntegral_eq,
    h.hasStieltjesIntegral.stieltjesIntegral_eq]

theorem HasStieltjesIntegral.of_const :
    HasStieltjesIntegral a b B (fun _ ↦ c) g (B c (g b) - B c (g a)) := by
  convert by_parts (B := B.flip) (f := g) (g := fun _ ↦ c) (L := 0) (by simp [const_right]) using 1
  simp

@[simp]
theorem StieltjesIntegrable.of_const : StieltjesIntegrable a b B (fun _ ↦ c) g :=
  HasStieltjesIntegral.of_const.stieltjesIntegrable

@[simp]
theorem stieltjesIntegral.of_const : ∫⟨B⟩ _ in a..b, c ∂g = B c (g b) - B c (g a) :=
  HasStieltjesIntegral.of_const.stieltjesIntegral_eq

theorem BoundedVariationOn.riemannIntegrable [CompleteSpace E] (hab : a ≤ b)
    (hf : BoundedVariationOn f (.Icc a b)) : RiemannIntegrable a b f := by
  rcases eq_or_lt_of_le hab with (rfl | hab)
  · simp
  unfold RiemannIntegrable
  rw [StieltjesIntegrable.symm_right]
  rw [← Set.uIcc_of_lt hab] at hf
  exact .of_continuousOn_of_boundedVariationOn (by fun_prop) hf

theorem MonotoneOn.riemannIntegrable {f : ℝ → ℝ} (hab : a ≤ b) (hf : MonotoneOn f (.Icc a b)) :
    RiemannIntegrable a b f := hf.boundedVariationOn.riemannIntegrable hab

theorem AntitoneOn.riemannIntegrable {f : ℝ → ℝ} (hab : a ≤ b) (hf : AntitoneOn f (.Icc a b)) :
    RiemannIntegrable a b f := hf.boundedVariationOn.riemannIntegrable hab

end BoxIntegral
