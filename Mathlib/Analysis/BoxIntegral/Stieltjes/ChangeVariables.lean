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
`∫⟨B⟩ x in a..b, f x ∂g` defined in `Analysis.BoxIntegral.Stieltjes.Defs` behaves under
changes of variable — composition with strictly monotone, strictly antitone, or reflection
maps.

## Main theorems

### Strictly monotone change of variables

* `BoxIntegral.HasStieltjesIntegral.of_comp_strictMono_continuous`: if `φ` is strictly
  monotone and continuous on `[a, b]`, then `HasStieltjesIntegral (φ a) (φ b) B f g L`
  implies `HasStieltjesIntegral a b B (f ∘ φ) (g ∘ φ) L`. The corresponding integrability
  statement (`StieltjesIntegrable.of_comp_strictMono_continuous`) and integral-value
  statement (`stieltjesIntegral_of_comp_strictMono_continuous`) follow.

### Reflection

* `BoxIntegral.HasStieltjesIntegral.of_reflect`: reflection across the origin sends
  `HasStieltjesIntegral a b B f g L` to
  `HasStieltjesIntegral (-b) (-a) B (f ∘ Neg.neg) (g ∘ Neg.neg) (-L)`. With analogous
  integrability and integral-value corollaries (`StieltjesIntegrable.of_reflect`,
  `stieltjesIntegral_of_reflect`).

### Strictly antitone change of variables

* `BoxIntegral.HasStieltjesIntegral.of_comp_strictAnti_continuous`: if `φ` is strictly
  antitone and continuous on `[a, b]`, then `HasStieltjesIntegral (φ a) (φ b) B f g L`
  implies `HasStieltjesIntegral a b B (f ∘ φ) (g ∘ φ) L` — the same conclusion as in
  the monotone case (no sign change on `L`, since the antitone-induced orientation flip
  cancels the implicit endpoint swap). Derived from the monotone version composed with
  the reflection lemma. Integrability and integral-value corollaries follow.

### Reflection for the Riemann integral

* `BoxIntegral.HasRiemannIntegral.of_reflect`: specialization to the Riemann integral,
  `∫_{-b}^{-a} f(-x) dx = ∫_a^b f(x) dx` (no sign flip — the `id` integrator absorbs the
  reflection's sign change via the `neg_right` API). With `RiemannIntegrable.of_reflect`
  and `riemannIntegral_of_reflect`.

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
    (hmono : StrictMonoOn φ (.Icc a b))
    (hcont : ContinuousOn φ (.Icc a b))
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
  simp only [Ioc.comp, h2, Ioc.len]
  suffices dist (φ J.lower₁) (φ J.upper₁) < δ' by
    change φ J.upper₁ - φ J.lower₁ ≤ δ'
    simp [Real.dist_eq] at this ⊢; grind
  apply hδf _ h1.1 _ h1.2
  specialize hmesh J hJπ
  simp [← NNReal.coe_le_coe, Box.len] at hmesh ⊢; grind

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

private noncomputable def Box.reflect (J : Box (Fin 1)) : Box (Fin 1) :=
  Ioc (-J.upper₁) (-J.lower₁)

private lemma Box.lower_lt_upper_reflect₁ (J : Box (Fin 1)) : (-J.upper₁) < (-J.lower₁) := by
  simp only [neg_lt_neg_iff, Box.lower_lt_upper₁]

private noncomputable def Box.reflect_len (J : Box (Fin 1)) : J.reflect.len = J.len := by
  simp [Box.len, Box.reflect, J.lower_lt_upper_reflect₁]; abel

open Topology

theorem HasStieltjesIntegral.of_reflect
    (h : HasStieltjesIntegral a b B f g L) :
    HasStieltjesIntegral (-b) (-a) B (f ∘ Neg.neg) (g ∘ Neg.neg) (-L) := by
  wlog hab : a ≤ b
  · rw [HasStieltjesIntegral.symm_iff] at h ⊢
    simpa using this h (by order)
  obtain rfl | hab := hab.eq_or_lt
  · simp_all
  have hab' : -b < -a := by grind
  simp only [hab, hasStieltjesIntegral_iff_lim_sum, gt_iff_lt, mesh_size_le_iff₁, mem_boxes,
    mem_toPrepartition, isValue, hab', Function.comp_apply] at h ⊢
  peel h with ε hε δ hδ h
  intro π hhen hpart hmesh
  classical
  let π' : TaggedPrepartition (Ioc a b) := {
    boxes := π.boxes.image Box.reflect
    le_of_mem' J' hJ' := by
      simp only [mem_image, mem_boxes, mem_toPrepartition] at hJ'
      obtain ⟨J, hJπ, rfl⟩ := hJ'
      replace hJπ := π.le_of_mem hJπ
      simp [Box.reflect, hab, Box.le_Ioc_iff, J.lower_lt_upper_reflect₁] at hJπ ⊢
      grind
    pairwiseDisjoint I' hI' J' hJ' hdisj := by
      simp only [coe_image, Set.mem_image, SetLike.mem_coe, mem_boxes,
        mem_toPrepartition, Function.onFun] at hI' hJ' ⊢
      obtain ⟨I, hIπ, rfl⟩ := hI'
      obtain ⟨J, hJπ, rfl⟩ := hJ'
      have h : I ≠ J := by grind
      replace h := π.pairwiseDisjoint hIπ hJπ h
      simp [Box.disjoint_iff₁, Box.reflect, I.lower_lt_upper_reflect₁,
        J.lower_lt_upper_reflect₁] at h ⊢
      tauto
    tag J' := fun _ ↦ -π.tag (Box.reflect J') 0
    tag_mem_Icc J' := by
      have := π.tag_mem_Icc (Box.reflect J')
      simp [Box.reflect, hab] at this ⊢
      grind
  }
  rw [← dist_neg_neg, ← Finset.sum_neg_distrib, neg_neg]
  convert h π' (fun J' hJ' ↦ ?_) (fun x' hx' ↦ ?_) (fun J' hJ' ↦ ?_) using 2
  · convert Finset.sum_bijective Box.reflect (Function.Involutive.bijective (fun J ↦ ?_))
      (fun J ↦ ?_) (fun J hJ ↦ ?_)
    · simp [Box.reflect, J.lower_lt_upper_reflect₁, ← Box.eq_Ioc]
    · simp only [mem_boxes, mem_toPrepartition, Box.reflect, mem_image, π']
      refine ⟨ by grind, fun ⟨J', hJ', heq⟩ ↦ ?_ ⟩
      have : J = J' := by
        simp [Box.congr₁, J.lower_lt_upper_reflect₁, J'.lower_lt_upper_reflect₁] at heq ⊢
        tauto
      simp_all
    simp [Box.reflect, π', J.lower_lt_upper_reflect₁, ←Box.eq_Ioc]
  · simp only [isValue, mem_mk, Prepartition.mem_mk, mem_image, mem_boxes, mem_toPrepartition,
    π'] at hJ'
    obtain ⟨ J, hJπ, rfl⟩ := hJ'
    have := hhen J hJπ
    simp [Box.reflect, J.lower_lt_upper_reflect₁, π', ← Box.eq_Ioc] at this ⊢
    tauto
  · let x := - x' 0
    have hx : -b ≤ x ∧ x < -a := by simpa [x, hab, and_comm] using hx'
    have hmem (y : ℝ) : ∃ J ∈ π.boxes, y ∈ Set.Ioc (-b) (-a) → y ∈ J.toSet₁ := by
      let y' := if y ∈ Set.Ioc (-b) (-a) then y else -a
      obtain ⟨J, hJπ, _⟩ := hpart (fun _ ↦ y') (by simp [hab', y']; grind)
      exact ⟨J, hJπ, by aesop⟩
    choose J hJ hmem using hmem
    have h1 : ∀ᶠ y in 𝓝[>] x, y ∈ Set.Ioc (-b) (-a) := by
      filter_upwards [Ioo_mem_nhdsGT hx.2] with y hy using ⟨hx.1.trans_lt hy.1, hy.2.le⟩
    obtain ⟨I, _, hI'⟩ : ∃ I ∈ π.boxes, ∃ᶠ y in 𝓝[>] x, J y = I := by
      rw [← Filter.frequently_exists_finset]
      simpa using (.of_forall hJ : ∀ᶠ y in 𝓝[>] x, J y ∈ π.boxes).frequently
    have h2 : ∃ᶠ y in 𝓝[>] x, y ∈ I.toSet₁ :=
      (hI'.and_eventually (h1.mono hmem)).mono fun _ ⟨h_eq, hy⟩ ↦ h_eq ▸ hy
    refine ⟨I.reflect, by aesop, ?_⟩
    simp only [Box.toSet₁_def, Set.mem_Ioc] at h2
    suffices I.lower₁ ≤ x ∧ x < I.upper₁ by
      simp [x, Box.reflect, I.lower_lt_upper_reflect₁] at this ⊢; grind
    refine ⟨not_lt.mp fun hlt ↦ ?_, ?_⟩
    · obtain ⟨y, _⟩ := (h2.and_eventually
        ((eventually_lt_nhds hlt).filter_mono nhdsWithin_le_nhds)).exists
      linarith
    · obtain ⟨y, ⟨_, hyu⟩, hyx⟩ :=
        (h2.and_eventually (self_mem_nhdsWithin (s := Set.Ioi x))).exists
      exact hyx.trans_le hyu
  simp only [isValue, mem_mk, Prepartition.mem_mk, mem_image, mem_boxes, mem_toPrepartition,
    π'] at hJ'
  obtain ⟨ J, hJπ, rfl⟩ := hJ'
  specialize hmesh J hJπ
  simpa [Box.reflect_len] using hmesh

theorem StieltjesIntegrable.of_reflect (h : StieltjesIntegrable a b B f g) :
    StieltjesIntegrable (-b) (-a) B (f ∘ Neg.neg) (g ∘ Neg.neg) :=
  h.hasStieltjesIntegral.of_reflect.stieltjesIntegrable

theorem stieltjesIntegral_of_reflect (h : StieltjesIntegrable a b B f g) :
    ∫⟨B⟩ x in (-b)..(-a), f (-x) ∂(g ∘ Neg.neg) = -∫⟨B⟩ x in a..b, f x ∂g :=
  h.hasStieltjesIntegral.of_reflect.stieltjesIntegral_eq

/-- The Riemann-Stieltjes integral is unchanged after composing with a strictly antitone
continuous function. -/
theorem HasStieltjesIntegral.of_comp_strictAnti_continuous (hab : a ≤ b)
    (hanti : StrictAntiOn φ (.Icc a b)) (hcont : ContinuousOn φ (.Icc a b))
    (h : HasStieltjesIntegral (φ a) (φ b) B f g L) :
    HasStieltjesIntegral a b B (f ∘ φ) (g ∘ φ) L := by
  have hMaps : Set.MapsTo Neg.neg (.Icc (-b) (-a)) (.Icc a b) := fun _ _ ↦ by grind
  have h' : HasStieltjesIntegral ((φ ∘ Neg.neg) (-b)) ((φ ∘ Neg.neg) (-a)) B f g (-L) := by
    simpa using h.symm
  simpa [Function.comp_def] using
    (HasStieltjesIntegral.of_comp_strictMono_continuous (neg_le_neg hab)
    (hanti.comp (fun _ _ _ _ h ↦ neg_lt_neg h) hMaps)
    (hcont.comp continuous_neg.continuousOn hMaps) h').of_reflect

theorem StieltjesIntegrable.of_comp_strictAnti_continuous (hab : a ≤ b)
    (hanti : StrictAntiOn φ (.Icc a b)) (hcont : ContinuousOn φ (.Icc a b))
    (h : StieltjesIntegrable (φ a) (φ b) B f g) :
    StieltjesIntegrable a b B (f ∘ φ) (g ∘ φ) :=
  (h.hasStieltjesIntegral.of_comp_strictAnti_continuous hab hanti hcont).stieltjesIntegrable

theorem stieltjesIntegral_of_comp_strictAnti_continuous (hab : a ≤ b)
    (hanti : StrictAntiOn φ (.Icc a b)) (hcont : ContinuousOn φ (.Icc a b))
    (h : StieltjesIntegrable (φ a) (φ b) B f g) :
    ∫⟨B⟩ x in a..b, f (φ x) ∂(g ∘ φ) = ∫⟨B⟩ x in φ a..φ b, f x ∂g :=
  (h.hasStieltjesIntegral.of_comp_strictAnti_continuous hab hanti hcont).stieltjesIntegral_eq

/-- Reflection for the Riemann integral: `∫_{-b}^{-a} f(-x) dx = ∫_a^b f(x) dx`. -/
theorem HasRiemannIntegral.of_reflect {M : E} (h : HasRiemannIntegral a b f M) :
    HasRiemannIntegral (-b) (-a) (f ∘ Neg.neg) M := by
  simpa [show (-Neg.neg : ℝ → ℝ) = id by ext; simp]
    using (HasStieltjesIntegral.of_reflect h).neg_right

theorem RiemannIntegrable.of_reflect (h : RiemannIntegrable a b f) :
    RiemannIntegrable (-b) (-a) (f ∘ Neg.neg) :=
  h.hasRiemannIntegral.of_reflect.riemannIntegrable

theorem riemannIntegral_of_reflect (h : RiemannIntegrable a b f) :
    riemannIntegral (-b) (-a) (f ∘ Neg.neg) = riemannIntegral a b f :=
  h.hasRiemannIntegral.of_reflect.riemannIntegral_eq

end Change

end BoxIntegral
