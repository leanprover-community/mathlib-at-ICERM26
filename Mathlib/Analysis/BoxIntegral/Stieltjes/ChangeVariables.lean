/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.Basic

/-! # Change of variables for the Riemann–Stieltjes integral

In this file we establish how the Riemann–Stieltjes integral
`∫⟨B⟩ x in a..b, f x ∂g` defined in `Analysis.BoxIntegral.Stieltjes.Defs`, behaves with respect to
monotone changes of variable.

-/

@[expose] public section

open BoxIntegral Fin ContinuousLinearMap TaggedPrepartition Metric
open Prepartition hiding mem_mk
open Finset hiding Ioc mem_mk

namespace BoxIntegral

section Change

/-! ## Change of variables -/

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {φ : ℝ → ℝ} {f : ℝ → E} {g : ℝ → F} {L : G} {a b : ℝ} {B : E →L[ℝ] F →L[ℝ] G}

/-- The Riemann-Stieltjes integral is unchanged after composing with a strictly monotone
continuous function. -/
theorem HasStieltjesIntegral.of_comp_strictMono_continuous (hab : a ≤ b)
    (hmono : StrictMonoOn φ (Set.Icc a b))
    (hcont : ContinuousOn φ (Set.Icc a b))
    (h : HasStieltjesIntegral (φ a) (φ b) B f g L) :
    HasStieltjesIntegral a b B (f ∘ φ) (g ∘ φ) L := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp_all
  have ha_mem : a ∈ Set.Icc a b := by simp [hab.le]
  have hb_mem : b ∈ Set.Icc a b := by simp [hab.le]
  have hsurj := hcont.surjOn_Icc ha_mem hb_mem
  have hφab := hmono ha_mem hb_mem hab
  have hmono' := hmono.monotoneOn
  simp only [hφab, hasStieltjesIntegral_iff_lim_sum, gt_iff_lt, mesh_size₁, Finset.sup_le_iff,
    mem_boxes, mem_toPrepartition, isValue, map_sub,
    hab, Function.comp_apply] at h ⊢
  peel h with ε hε h
  obtain ⟨δ', hδ', h⟩ := h
  obtain ⟨δ, hδ, hδf⟩ := hcont.metric_uniform δ' hδ'
  refine ⟨NNReal.mk (δ/2) (by linarith), (show 0 < δ/2 by positivity),
    fun π hhen hpart hmesh ↦ ?_⟩
  have h1 {J : Box (Fin 1)} (hJ : J ∈ π) := J.mem_of_le hab (π.le_of_mem' _ hJ)
  have h2 {J : Box (Fin 1)} (hJ : J ∈ π) : φ J.lower₁ < φ J.upper₁ :=
    hmono (h1 hJ).1 (h1 hJ).2 J.lower_lt_upper₁
  have hinj : Set.InjOn (Ioc.comp φ) ↑π.boxes :=
    Ioc.comp_injOn_of_strictMonoOn hab (fun J hJ ↦ π.le_of_mem' J hJ) hmono
  classical
  set σ : Box (Fin 1) → Box (Fin 1) := Function.invFunOn (Ioc.comp φ) ↑π.boxes with hσ_def
  have hσ : ∀ J ∈ π.boxes, σ (Ioc.comp φ J) = J :=
    fun J hJ ↦ hinj.leftInvOn_invFunOn hJ
  let π' : TaggedPrepartition (Ioc (φ a) (φ b)) := {
    boxes := π.boxes.image (Ioc.comp φ)
    le_of_mem' J' hJ' := by
      simp only [mem_image, mem_boxes, mem_toPrepartition] at hJ'
      obtain ⟨J, hJπ, rfl⟩ := hJ'
      rw [J.eq_Ioc]
      simp only [Box.lower_lt_upper₁, Ioc.comp_apply, Ioc_le_Ioc_iff hφab (h2 hJπ)]
      and_intros <;> apply hmono' <;> grind
    pairwiseDisjoint I' hI' J' hJ' hdisj := by
      simp only [coe_image, Set.mem_image, SetLike.mem_coe, mem_boxes,
        mem_toPrepartition, Function.onFun] at hI' hJ' ⊢
      obtain ⟨I, hIπ, rfl⟩ := hI'
      obtain ⟨J, hJπ, rfl⟩ := hJ'
      have h : I ≠ J := by grind
      replace h := π.pairwiseDisjoint hIπ hJπ h
      simp only [Function.onFun, Box.disjoint_iff₁, Ioc.comp, h2 hIπ, Ioc.upper₁, h2 hJπ,
        Ioc.lower₁] at h ⊢
      apply Or.imp _ _ h <;> apply hmono' <;> grind
    tag J' := fun _ ↦ φ (π.tag (σ J') 0)
    tag_mem_Icc J' := by
      have := π.tag_mem_Icc (σ J')
      simp only [Box.Icc_def, Set.mem_Icc, Pi.le_def, hab, Ioc.lower, forall_fin_one,
        isValue, Ioc.upper, hφab, forall_const] at this ⊢
      refine ⟨hmono' ha_mem (by simp [this]) this.1, hmono' (by simp [this]) hb_mem this.2⟩
  }
  convert h π' (fun J' hJ' ↦ ?_) (fun x' hx' ↦ ?_) (fun J' hJ' ↦ ?_) using 2
  · symm
    rw [show π'.boxes = π.boxes.image (Ioc.comp φ) from rfl, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun J hJ ↦ ?_
    simp [π', hσ J hJ]; simp [Ioc.comp, h2 hJ]
  · simp only [isValue, mem_mk, Prepartition.mem_mk, mem_image, mem_boxes, mem_toPrepartition,
    Box.Icc₁_eq, Box.Icc₁_def, Set.mem_Icc, Set.mem_setOf_eq, π'] at hJ' ⊢
    obtain ⟨J, hJπ, rfl⟩ := hJ'
    specialize h1 hJπ
    simp only [hσ J hJπ]; simp only [Ioc.comp, h2 hJπ, Ioc.lower₁, isValue, Ioc.upper₁]
    have h3 := π.tag_mem_Icc J
    have h4 := hhen J hJπ
    simp only [Box.Icc₁_eq, Box.Icc₁_def, hab, Ioc.lower₁, Ioc.upper₁, isValue, Set.mem_Icc,
      Set.mem_setOf_eq] at h3 h4
    exact ⟨hmono' h1.1 (by simp [h3]) h4.1, hmono' (by simp [h3]) h1.2 h4.2⟩
  · simp only [Box.mem₁, Box.toSet₁_def, hφab, Ioc.lower₁, Ioc.upper₁, isValue, Set.mem_Ioc,
    mem_toPrepartition] at hx' ⊢
    have := hsurj (show x' 0 ∈ Set.Icc (φ a) (φ b) by grind)
    simp only [isValue, Set.mem_image, Set.mem_Icc] at this
    obtain ⟨x, hx, hxx'⟩ := this
    simp only [isValue, ← hxx', mem_mk, Prepartition.mem_mk,
      mem_image, mem_boxes, mem_toPrepartition,
      exists_exists_and_eq_and, π'] at hx' ⊢
    have : a < x := by grind
    obtain ⟨J, hJπ, hxJ⟩ := hpart (fun _ ↦ x) (by simp [hab, this, hx])
    use J, hJπ
    simp only [Box.mem₁, Box.toSet₁_def, Set.mem_Ioc, Ioc.comp, h2 hJπ, Ioc.lower₁,
      Ioc.upper₁] at hxJ ⊢
    specialize h1 hJπ
    exact ⟨hmono h1.1 (by simp [hx]) hxJ.1, hmono' (by simp [hx]) h1.2 hxJ.2⟩
  simp only [isValue, mem_mk, Prepartition.mem_mk, mem_image, mem_boxes,
    mem_toPrepartition, π'] at hJ'
  obtain ⟨J, hJπ, rfl⟩ := hJ'
  specialize h1 hJπ
  specialize h2 hJπ
  have := J.lower_lt_upper₁
  simp only [Ioc.comp, h2, Ioc.upper₁, Ioc.lower₁]
  suffices dist (φ J.lower₁) (φ J.upper₁) < δ' by
    change φ J.upper₁ - φ J.lower₁ ≤ δ'
    simp [Real.dist_eq] at this ⊢; grind
  apply hδf _ h1.1 _ h1.2
  specialize hmesh J hJπ
  simp [← NNReal.coe_le_coe] at hmesh ⊢; grind

theorem StieltjesIntegrable.of_comp_strictMono_continuous (hab : a ≤ b)
    (hmono : StrictMonoOn φ (.Icc a b))
    (hcont : ContinuousOn φ (.Icc a b))
    (h : StieltjesIntegrable (φ a) (φ b) B f g) :
    StieltjesIntegrable a b B (f ∘ φ) (g ∘ φ) :=
  (h.hasStieltjesIntegral.of_comp_strictMono_continuous hab hmono hcont).stieltjesIntegrable

theorem stieltjesIntegral_of_comp_strictMono_continuous (hab : a ≤ b)
    (hmono : StrictMonoOn φ (.Icc a b))
    (hcont : ContinuousOn φ (.Icc a b))
    (h : StieltjesIntegrable (φ a) (φ b) B f g) :
    ∫⟨B⟩ x in a..b, f (φ x) ∂(g ∘ φ) = ∫⟨B⟩ x in φ a..φ b, f x ∂g :=
  (h.hasStieltjesIntegral.of_comp_strictMono_continuous hab hmono hcont).stieltjesIntegral_eq

end Change

end BoxIntegral
