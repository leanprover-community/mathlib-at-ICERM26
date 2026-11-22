/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.Basic
public import Mathlib.Analysis.BoxIntegral.Stieltjes.RiemannStieltjesSum


/-! # Riemann–Stieltjes integration by parts

In this file we establish how integration by parts API for the Riemann–Stieltjes integral
`∫⟨B⟩ x in a..b, f x ∂g` defined in `Analysis.BoxIntegral.Stieltjes.Defs`.

## AI usage

The proof of `HasStieltjesIntegral.by_parts` (Theorem A.2 of Montgomery–Vaughan) was rewritten by
Claude (Anthropic) in November 2026, replacing an earlier LLM-generated proof. It compiles, but
has not been reviewed by a human.
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

namespace BoxIntegral

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {a b : ℝ} {B : E →L[ℝ] F →L[ℝ] G} {f : ℝ → E} {g : ℝ → F} {L : G} {c : E}

/-- Theorem A.2 of Montgomery Vaughan: if ∫ₐᵇ f dg exists, then ∫ₐᵇ g df exists and
∫ₐᵇ g df = g(b) * f(b) - g(a) * f(a) - ∫ₐᵇ f dg. -/
theorem HasStieltjesIntegral.by_parts (hL : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral a b B.flip g f (B (f b) (g b) - B (f a) (g a) - L) := by
  wlog hle : a ≤ b generalizing a b L with hsymm
  · rw [HasStieltjesIntegral.symm_iff]
    convert hsymm hL.symm (by order) using 1
    abel
  obtain rfl | hab := hle.eq_or_lt
  · simp_all
  rw [hasStieltjesIntegral_iff_lim_sum hab] at hL ⊢
  intro ε hε
  obtain ⟨δ, hδ, hL⟩ := hL ε hε
  refine ⟨δ / 2, by positivity, fun π hπ_hen hπ_part hπ_mesh ↦ ?_⟩
  -- As in Montgomery–Vaughan: the sum for `∫ g df` over `π` is the boundary term minus the sum
  -- for `∫ f dg` over the dual partition, whose mesh is at most twice that of `π`.
  rw [π.dual_sum_by_parts hab hπ_hen hπ_part, dist_sub_left]
  refine hL _ (π.dual_isHenstock hab hπ_hen hπ_part) (π.dual_isPartition hab hπ_hen hπ_part) ?_
  calc (π.dual hab hπ_hen hπ_part).mesh_size ≤ 2 * π.mesh_size :=
        π.dual_mesh_size_le_two_mul hab hπ_hen hπ_part
    _ ≤ 2 * (δ / 2) := by gcongr
    _ = δ := by field_simp


theorem StieltjesIntegrable.by_parts (h : StieltjesIntegrable a b B f g) :
    StieltjesIntegrable a b B.flip g f := ⟨_, h.hasStieltjesIntegral.by_parts⟩

theorem StieltjesIntegrable.symm_right
  : StieltjesIntegrable a b B f g ↔ StieltjesIntegrable a b B.flip g f := ⟨by_parts, by_parts⟩

theorem stieltjesIntegral.by_parts (h : StieltjesIntegrable a b B f g) :
    ∫⟨B.flip⟩ x in a..b, g x ∂f = B (f b) (g b) - B (f a) (g a) - ∫⟨B⟩ x in a..b, f x ∂g := by
  rw [h.hasStieltjesIntegral.by_parts.stieltjesIntegral_eq,
    h.hasStieltjesIntegral.stieltjesIntegral_eq]

/-- ## Some applications of integration by parts -/
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

theorem HasRiemannIntegral.of_const : HasRiemannIntegral a b (fun _ ↦ c) ((b - a) • c) := by
  unfold HasRiemannIntegral; convert HasStieltjesIntegral.of_const using 1
  simp; module

@[simp]
theorem RiemannIntegrable.of_const : RiemannIntegrable a b (fun _ ↦ c) :=
  HasRiemannIntegral.of_const.riemannIntegrable

@[simp]
theorem riemannIntegral.of_const : riemannIntegral a b (fun _ ↦ c) = (b - a) • c :=
  HasRiemannIntegral.of_const.riemannIntegral_eq

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
