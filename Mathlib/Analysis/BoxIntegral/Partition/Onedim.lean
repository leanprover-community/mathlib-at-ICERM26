/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Box.Ioc
public import Mathlib.Analysis.BoxIntegral.Partition.Additive
public import Mathlib.Analysis.BoxIntegral.Partition.Tagged

/-! # One-dimensional partitions

This file defines some basic API for one-dimensional partitions.
-/

@[expose] public section

namespace BoxIntegral

open Prepartition Finset

/-! ## One-dimensional mesh size -/

/-- In one dimension, the mesh size simplifies to the longest length of an interval
in the partition. -/
theorem mesh_size₁ {I : Box (Fin 1)} (π : Prepartition I) : π.mesh_size
    = π.boxes.sup (fun B ↦ NNReal.mk B.len (by linarith [B.len_pos]))
    := by simp [mesh_size]; congr

@[simp]
theorem mesh_size_le_iff₁ {I : Box (Fin 1)} (π : Prepartition I) (ε : NNReal) :
    π.mesh_size ≤ ε ↔ ∀ B ∈ π.boxes, B.len ≤ ε := by
  simp [mesh_size_le_iff, Box.len, Box.lower₁, Box.upper₁]

/-- In one dimension, the length of `splitLower J 0 c` (when nonempty) is bounded by the length
of `J`. -/
theorem Box.splitLower_unbot_len_le {J : Box (Fin 1)} {c : ℝ}
    (h : J.splitLower 0 c ≠ ⊥) :
    ((J.splitLower 0 c).unbot h).len ≤ J.len := by
  change ((J.splitLower 0 c).unbot h).upper 0 - ((J.splitLower 0 c).unbot h).lower 0 ≤
    J.upper 0 - J.lower 0
  rw [Box.splitLower_unbot_upper_apply_self, congrArg (· 0) (Box.splitLower_unbot_lower h)]
  exact sub_le_sub_right (min_le_right _ _) _

/-! ### Cutting a one-dimensional prepartition at an interior point

Given a prepartition of `Ioc a b` and `c ∈ (a, b]`, `Prepartition.splitLowerAt` takes the
lower (≤ c) half of each box, yielding a prepartition of `Ioc a c`. The companion theorems
state that this preserves the partition property and does not increase the mesh size. -/

open scoped Classical in
/-- Cut a prepartition of `Ioc a b` at `c ∈ (a, b]`: take the lower (≤ c) half of each box. -/
noncomputable def Prepartition.splitLowerAt {a b : ℝ}
    (π : Prepartition (BoxIntegral.Ioc a b)) (c : ℝ) (hac : a < c) (hcb : c ≤ b) :
    Prepartition (BoxIntegral.Ioc a c) :=
  have hab : a < b := hac.trans_le hcb
  Prepartition.ofWithBot (π.boxes.image (fun J => J.splitLower 0 c))
    (by
      intro K hK
      simp only [Finset.mem_image] at hK
      obtain ⟨J, hJ_in, rfl⟩ := hK
      rw [← Box.withBotCoe_subset_iff, Box.coe_splitLower, Box.coe_coe]
      rintro x ⟨hxJ, hxc⟩
      have hJ_le := (Box.le_Ioc_iff hab J).mp (π.le_of_mem' J hJ_in)
      rw [Box.mem_coe, Box.mem₁, Box.toSet₁_def, Set.mem_Ioc] at hxJ
      rw [Box.mem_coe, mem_Ioc hac, Set.mem_Ioc]
      exact ⟨lt_of_le_of_lt hJ_le.1 hxJ.1, hxc⟩)
    (by
      intro K1 hK1 K2 hK2 hne
      simp only [Finset.coe_image, Set.mem_image] at hK1 hK2
      obtain ⟨J1, hJ1_in, rfl⟩ := hK1
      obtain ⟨J2, hJ2_in, rfl⟩ := hK2
      rw [← Box.disjoint_withBotCoe, Box.coe_splitLower, Box.coe_splitLower]
      exact (π.disjoint_coe_of_mem hJ1_in hJ2_in (fun h => hne (by rw [h]))).mono
        Set.inter_subset_left Set.inter_subset_left)

theorem Prepartition.mem_splitLowerAt_iff {a b : ℝ}
    {π : Prepartition (BoxIntegral.Ioc a b)} {c : ℝ} {hac : a < c} {hcb : c ≤ b}
    {K : Box (Fin 1)} :
    K ∈ π.splitLowerAt c hac hcb ↔ ∃ J ∈ π.boxes, ↑K = Box.splitLower J 0 c := by
  classical
  unfold splitLowerAt
  rw [Prepartition.mem_ofWithBot, Finset.mem_image]
  exact ⟨fun ⟨J, hJ, hKJ⟩ => ⟨J, hJ, hKJ.symm⟩, fun ⟨J, hJ, hKJ⟩ => ⟨J, hJ, hKJ.symm⟩⟩

open scoped Classical in
/-- A sum over the boxes of `π.splitLowerAt c` reindexes to a sum over the original boxes of `π`,
where each box `J` contributes via its lower half `splitLower J 0 c` (or `0` when that half is
empty). This is the bookkeeping behind comparing a Riemann sum on the cut prepartition to one on
the original. -/
theorem Prepartition.sum_splitLowerAt_boxes {a b : ℝ}
    (π : Prepartition (BoxIntegral.Ioc a b)) {c : ℝ} (hac : a < c) (hcb : c ≤ b)
    {M : Type*} [AddCommMonoid M] (ψ : Box (Fin 1) → M) :
    ∑ K ∈ (π.splitLowerAt c hac hcb).boxes, ψ K =
      ∑ J ∈ π.boxes,
        if h : Box.splitLower J 0 c ≠ ⊥ then ψ ((Box.splitLower J 0 c).unbot h) else 0 := by
  symm
  rw [← Finset.sum_filter_of_ne (p := fun J => Box.splitLower J 0 c ≠ ⊥)
    (fun J _ hψ heq => hψ (dif_neg (not_not_intro heq)))]
  refine Finset.sum_bij
    (fun J hJ => (Box.splitLower J 0 c).unbot (Finset.mem_filter.mp hJ).2) ?_ ?_ ?_ ?_
  · intro J hJ
    exact Prepartition.mem_splitLowerAt_iff.mpr
      ⟨J, (Finset.mem_filter.mp hJ).1, WithBot.coe_unbot _ _⟩
  · intro J1 hJ1 J2 hJ2 hi_eq
    rw [Finset.mem_filter] at hJ1 hJ2
    refine Prepartition.splitLower_injOn hJ1.1 hJ2.1 hJ1.2 ?_
    rw [← WithBot.coe_unbot (Box.splitLower J1 0 c) hJ1.2,
        ← WithBot.coe_unbot (Box.splitLower J2 0 c) hJ2.2]
    exact congrArg (fun x : Box (Fin 1) => (x : WithBot (Box (Fin 1)))) hi_eq
  · intro K hK
    obtain ⟨J, hJ_in, hsp⟩ := Prepartition.mem_splitLowerAt_iff.mp hK
    have hJ_ne : Box.splitLower J 0 c ≠ ⊥ := by rw [← hsp]; exact WithBot.coe_ne_bot
    exact ⟨J, Finset.mem_filter.mpr ⟨hJ_in, hJ_ne⟩,
      WithBot.coe_injective (by rw [WithBot.coe_unbot, hsp])⟩
  · intro J hJ
    rw [dif_pos (Finset.mem_filter.mp hJ).2]

open scoped Classical in
/-- The tagged-prepartition version of `Prepartition.sum_splitLowerAt_boxes`. -/
theorem TaggedPrepartition.sum_splitLowerAt_boxes {a b : ℝ}
    (π : TaggedPrepartition (BoxIntegral.Ioc a b)) {c : ℝ} (hac : a < c) (hcb : c ≤ b)
    {M : Type*} [AddCommMonoid M] (ψ : Box (Fin 1) → M) :
    ∑ K ∈ (π.splitLowerAt c hac hcb).boxes, ψ K =
      ∑ J ∈ π.boxes,
        if h : Box.splitLower J 0 c ≠ ⊥ then ψ ((Box.splitLower J 0 c).unbot h) else 0 :=
  π.toPrepartition.sum_splitLowerAt_boxes hac hcb ψ

theorem Prepartition.splitLowerAt_isPartition {a b : ℝ}
    (π : Prepartition (BoxIntegral.Ioc a b)) {c : ℝ} (hac : a < c) (hcb : c ≤ b)
    (hπ : π.IsPartition) : (π.splitLowerAt c hac hcb).IsPartition := by
  have hab : a < b := hac.trans_le hcb
  intro x hx
  rw [mem_Ioc hac, Set.mem_Ioc] at hx
  obtain ⟨J, hJ_in, hxJ⟩ := hπ x (by
    rw [mem_Ioc hab, Set.mem_Ioc]; exact ⟨hx.1, hx.2.trans hcb⟩)
  have h_ne : Box.splitLower J 0 c ≠ ⊥ := by
    rw [ne_eq, Box.splitLower_eq_bot, not_le]
    rw [Box.mem_def] at hxJ
    exact lt_of_lt_of_le (hxJ 0).1 hx.2
  refine ⟨(Box.splitLower J 0 c).unbot h_ne, ?_, ?_⟩
  · rw [mem_splitLowerAt_iff]
    exact ⟨J, hJ_in, (WithBot.coe_unbot _ h_ne)⟩
  · rw [← Box.mem_coe, ← Box.coe_coe, WithBot.coe_unbot, Box.coe_splitLower]
    exact ⟨hxJ, hx.2⟩

theorem Prepartition.splitLowerAt_mesh_le {a b : ℝ}
    (π : Prepartition (BoxIntegral.Ioc a b)) {c : ℝ} (hac : a < c) (hcb : c ≤ b) :
    (π.splitLowerAt c hac hcb).mesh_size ≤ π.mesh_size := by
  rw [mesh_size_le_iff₁]
  intro K hK
  obtain ⟨J, hJ_in, hsp⟩ := Prepartition.mem_splitLowerAt_iff.mp hK
  have h_ne : Box.splitLower J 0 c ≠ ⊥ := by rw [← hsp]; exact WithBot.coe_ne_bot
  have hKeq : K = (Box.splitLower J 0 c).unbot h_ne := by
    apply WithBot.coe_injective; rw [hsp, WithBot.coe_unbot]
  have hKlen : K.len ≤ J.len := hKeq ▸ Box.splitLower_unbot_len_le h_ne
  have hJ_len : J.len ≤ (π.mesh_size : ℝ) :=
    (mesh_size_le_iff₁ π _).mp le_rfl J hJ_in
  linarith

open scoped Classical in
/-- Cut a tagged prepartition of `Ioc a b` at `c ∈ (a, b]`: take the lower half of each box,
inheriting the tag (clipped to `c`). -/
noncomputable def TaggedPrepartition.splitLowerAt {a b : ℝ}
    (π : TaggedPrepartition (BoxIntegral.Ioc a b)) (c : ℝ) (hac : a < c) (hcb : c ≤ b) :
    TaggedPrepartition (BoxIntegral.Ioc a c) where
  toPrepartition := π.toPrepartition.splitLowerAt c hac hcb
  tag K :=
    if hK : ∃ J ∈ π.boxes, ↑K = Box.splitLower J 0 c then
      fun _ => min (π.tag (Classical.choose hK) 0) c
    else fun _ => c
  tag_mem_Icc := by
    have hab : a < b := hac.trans_le hcb
    intro K
    rw [Box.mem_Icc₁, Box.Icc₁_def, Ioc.lower₁ hac, Ioc.upper₁ hac]
    show _ ∈ Set.Icc a c
    by_cases hK : ∃ J ∈ π.boxes, ↑K = Box.splitLower J 0 c
    · simp only [dif_pos hK]
      have htag_ge : a ≤ π.tag (Classical.choose hK) 0 := by
        have := π.tag_mem_Icc (Classical.choose hK)
        rw [Box.mem_Icc₁, Box.Icc₁_def, Ioc.lower₁ hab, Ioc.upper₁ hab] at this
        exact this.1
      exact ⟨le_min htag_ge hac.le, min_le_right _ _⟩
    · simp only [dif_neg hK]; exact ⟨hac.le, le_refl _⟩

theorem TaggedPrepartition.splitLowerAt_tag_apply {a b : ℝ}
    (π : TaggedPrepartition (BoxIntegral.Ioc a b)) {c : ℝ} (hac : a < c) (hcb : c ≤ b)
    {J : Box (Fin 1)} (hJ : J ∈ π.boxes) (h_ne : Box.splitLower J 0 c ≠ ⊥) :
    (π.splitLowerAt c hac hcb).tag ((Box.splitLower J 0 c).unbot h_ne) 0 =
      min (π.tag J 0) c := by
  classical
  set K := (Box.splitLower J 0 c).unbot h_ne with hK_def
  have h_witness : ∃ J' ∈ π.boxes, ↑K = Box.splitLower J' 0 c :=
    ⟨J, hJ, WithBot.coe_unbot _ _⟩
  have h_spec := Classical.choose_spec h_witness
  have h_ne' : Box.splitLower (Classical.choose h_witness) 0 c ≠ ⊥ := by
    rw [← h_spec.2]; exact WithBot.coe_ne_bot
  have hJ'_eq : Classical.choose h_witness = J :=
    Prepartition.splitLower_injOn h_spec.1 hJ h_ne'
      (by rw [← h_spec.2, ← WithBot.coe_unbot (Box.splitLower J 0 c) h_ne])
  change (if hK : ∃ J' ∈ π.boxes, ↑K = Box.splitLower J' 0 c then
          (fun _ : Fin 1 => min (π.tag (Classical.choose hK) 0) c)
        else fun _ : Fin 1 => c) 0 = min (π.tag J 0) c
  rw [dif_pos h_witness, hJ'_eq]

theorem TaggedPrepartition.mem_splitLowerAt_iff {a b : ℝ}
    {π : TaggedPrepartition (BoxIntegral.Ioc a b)} {c : ℝ} {hac : a < c} {hcb : c ≤ b}
    {K : Box (Fin 1)} :
    K ∈ π.splitLowerAt c hac hcb ↔ ∃ J ∈ π.boxes, ↑K = Box.splitLower J 0 c :=
  @Prepartition.mem_splitLowerAt_iff _ _ π.toPrepartition c hac hcb K

theorem TaggedPrepartition.splitLowerAt_mesh_le {a b : ℝ}
    (π : TaggedPrepartition (BoxIntegral.Ioc a b)) {c : ℝ} (hac : a < c) (hcb : c ≤ b) :
    (π.splitLowerAt c hac hcb).mesh_size ≤ π.mesh_size :=
  Prepartition.splitLowerAt_mesh_le π.toPrepartition hac hcb

theorem TaggedPrepartition.splitLowerAt_isPartition {a b : ℝ}
    (π : TaggedPrepartition (BoxIntegral.Ioc a b)) {c : ℝ} (hac : a < c) (hcb : c ≤ b)
    (hπ : π.IsPartition) : (π.splitLowerAt c hac hcb).IsPartition :=
  Prepartition.splitLowerAt_isPartition π.toPrepartition hac hcb hπ

theorem TaggedPrepartition.splitLowerAt_isHenstock {a b : ℝ}
    (π : TaggedPrepartition (BoxIntegral.Ioc a b)) {c : ℝ} (hac : a < c) (hcb : c ≤ b)
    (hH : π.IsHenstock) : (π.splitLowerAt c hac hcb).IsHenstock := by
  intro K hK_in
  have hK_prep : K ∈ π.toPrepartition.splitLowerAt c hac hcb := hK_in
  obtain ⟨J, hJ_in, hsp⟩ := Prepartition.mem_splitLowerAt_iff.mp hK_prep
  have h_ne : Box.splitLower J 0 c ≠ ⊥ := by rw [← hsp]; exact WithBot.coe_ne_bot
  have hKeq : K = (Box.splitLower J 0 c).unbot h_ne :=
    WithBot.coe_injective (by rw [hsp, WithBot.coe_unbot])
  have htag := hH J hJ_in
  rw [Box.Icc_def] at htag
  have htag_lo : J.lower 0 ≤ π.tag J 0 := htag.1 0
  have htag_hi : π.tag J 0 ≤ J.upper 0 := htag.2 0
  have hJ_lt : J.lower 0 < c := by
    simpa [ne_eq, Box.splitLower_eq_bot, not_le] using h_ne
  rw [Box.mem_Icc₁, Box.Icc₁_def, hKeq]
  show _ ∈ Set.Icc _ _
  rw [TaggedPrepartition.splitLowerAt_tag_apply π hac hcb hJ_in h_ne]
  rw [show ((Box.splitLower J 0 c).unbot h_ne).lower₁ = J.lower 0 from
        congrArg (· 0) (Box.splitLower_unbot_lower h_ne),
      show ((Box.splitLower J 0 c).unbot h_ne).upper₁ = min c (J.upper 0) from
        Box.splitLower_unbot_upper_apply_self h_ne]
  exact ⟨le_min htag_lo hJ_lt.le,
    le_min (min_le_right _ _) ((min_le_left _ _).trans htag_hi)⟩

/-- For a tagged prepartition of `Ioc a b`, at most one box either straddles `c` or sits at
`c` with its left endpoint and tag both equal to `c` (these are the boxes whose contribution
to a one-dimensional Riemann sum is affected by cutting at `c`). -/
theorem TaggedPrepartition.near_c_at_most_one {a b : ℝ}
    (π : TaggedPrepartition (BoxIntegral.Ioc a b)) (c : ℝ) :
    (π.boxes.filter (fun J => (J.lower 0 < c ∧ c < J.upper 0) ∨
                              (π.tag J 0 = c ∧ J.lower 0 = c))).card ≤ 1 := by
  rw [Finset.card_le_one]
  intros J1 hJ1 J2 hJ2
  rw [Finset.mem_filter] at hJ1 hJ2
  by_contra hne
  have hd := (Box.disjoint_iff₁ (J := J1) (J' := J2)).mp
    (π.disjoint_coe_of_mem hJ1.1 hJ2.1 hne)
  have unpack : ∀ {J}, (J.lower 0 < c ∧ c < J.upper 0) ∨
      (π.tag J 0 = c ∧ J.lower 0 = c) → J.lower 0 ≤ c ∧ c < J.upper 0 :=
    fun {J} h => h.elim (fun ⟨l, u⟩ => ⟨l.le, u⟩)
      (fun ⟨_, le⟩ => ⟨le.le, le ▸ J.lower_lt_upper 0⟩)
  obtain ⟨hJ1_lo, hJ1_up⟩ := unpack hJ1.2
  obtain ⟨hJ2_lo, hJ2_up⟩ := unpack hJ2.2
  rcases hd with h | h
  · linarith [show J1.upper 0 ≤ c from h.trans hJ2_lo]
  · linarith [show J2.upper 0 ≤ c from h.trans hJ1_lo]

namespace Prepartition

/-! ## Evenly spaced partitions
-/

/-- We use a bundled `Even` class to represent an evenly spaced partition of an interval
`Ioc a b` into `N` equally spaced subintervals, arranged in a grid.
-/
class Even where
  a : ℝ
  b : ℝ
  N : ℤ
  hab : a < b
  hN : 0 < N

namespace Even

variable (e : Even) (x : ℝ) (n : ℤ)

theorem b_sub_a_pos : 0 < e.b - e.a := by linarith [e.hab]

/-- We use `δ` to denote the spacing of the grid. -/
noncomputable def δ : ℝ := (e.b - e.a) / e.N

theorem delta_pos : 0 < e.δ := div_pos e.b_sub_a_pos (mod_cast e.hN)

/-- The grid points of the partition. -/
noncomputable def grid : ℤ → ℝ := (e.a + · * e.δ)

@[simp]
theorem grid_zero : e.grid 0 = e.a := by simp [grid]

@[simp]
theorem grid_N : e.grid (e.N) = e.b := by have := e.hN; simp [grid, δ]; field_simp; abel

theorem grid_succ_eq : e.grid (n + 1) = e.grid n + e.δ := by simp [grid]; ring

theorem grid_succ_gt : e.grid (n + 1) > e.grid n := by
  linarith [e.grid_succ_eq n, e.delta_pos]

theorem grid_strictMono : StrictMono e.grid :=
  fun _ _ h ↦ by simp [grid, add_lt_add_iff_left, mul_lt_mul_iff_left₀ e.delta_pos, h]

theorem grid_mono : Monotone e.grid := e.grid_strictMono.monotone

@[simp]
theorem a_le_grid_iff : e.a ≤ e.grid n ↔ 0 ≤ n := by simp [← grid_zero, e.grid_strictMono.le_iff_le]

@[simp]
theorem a_lt_grid_iff : e.a < e.grid n ↔ 0 < n := by simp [← grid_zero, e.grid_strictMono.lt_iff_lt]

@[simp]
theorem grid_le_b_iff : e.grid n ≤ e.b ↔ n ≤ e.N := by simp [← grid_N, e.grid_strictMono.le_iff_le]

@[simp]
theorem grid_lt_b_iff : e.grid n < e.b ↔ n < e.N := by simp [← grid_N, e.grid_strictMono.lt_iff_lt]

theorem grid_mem_Ioc_iff : e.grid n ∈ Set.Ioc e.a e.b ↔ n ∈ Set.Ioc 0 e.N := by simp

theorem grid_mem_Ioo_iff : e.grid n ∈ Set.Ioo e.a e.b ↔ n ∈ Set.Ioo 0 e.N := by simp

theorem grid_mem_Ico_iff : e.grid n ∈ Set.Ico e.a e.b ↔ n ∈ Set.Ico 0 e.N := by simp

theorem grid_mem_Icc_iff : e.grid n ∈ Set.Icc e.a e.b ↔ n ∈ Set.Icc 0 e.N := by simp

/-- The index set for the partition. -/
noncomputable def indices := Finset.Ico 0 e.N

instance indices_nonempty : Nonempty e.indices := ⟨ 0, by simp [indices, hN] ⟩

theorem Ioc_subset_Ioc {n : ℤ} (hn : n ∈ e.indices) :
  Set.Ioc (e.grid n) (e.grid (n + 1)) ⊆ .Ioc e.a e.b := by
  simp [indices] at hn; gcongr <;> { simp ; grind }

theorem Ioo_subset_Ioo {n : ℤ} (hn : n ∈ e.indices) :
  Set.Ioo (e.grid n) (e.grid (n + 1)) ⊆ .Ioo e.a e.b := by
  simp [indices] at hn; gcongr <;> { simp ; grind }

theorem Ico_subset_Ico {n : ℤ} (hn : n ∈ e.indices) :
  Set.Ico (e.grid n) (e.grid (n + 1)) ⊆ .Ico e.a e.b := by
  simp [indices] at hn; gcongr <;> { simp ; grind }

theorem Icc_subset_Icc {n : ℤ} (hn : n ∈ e.indices) :
  Set.Icc (e.grid n) (e.grid (n + 1)) ⊆ .Icc e.a e.b := by
  simp [indices] at hn; gcongr <;> { simp ; grind }

/-- The box representing the entire interval. -/
noncomputable def box := Ioc e.a e.b

@[simp]
theorem box_lower₁ : e.box.lower₁ = e.a := by simp [box, hab]

@[simp]
theorem box_upper₁ : e.box.upper₁ = e.b := by simp [box, hab]

@[simp]
theorem box_len : e.box.len = e.b - e.a := by simp [box, hab]

/-- The grid boxes comprising the partition. -/
noncomputable def gridbox : ℤ → Box (Fin 1) := fun n ↦ Ioc (e.grid n) (e.grid (n + 1))

@[simp]
theorem gridbox_upper : (e.gridbox n).upper₁ = e.grid (n + 1) := by
  simp [gridbox, grid_succ_gt]

@[simp]
theorem gridbox_lower : (e.gridbox n).lower₁ = e.grid n := by
  simp [gridbox, grid_succ_gt]

@[simp]
theorem gridbox_len : (e.gridbox n).len = e.δ := by simp [Box.len, grid_succ_eq]

theorem gridbox_Icc₁ : (e.gridbox n).Icc₁ = Set.Icc (e.grid n) (e.grid (n + 1)) := by simp

theorem gridbox_toSet₁ : (e.gridbox n).toSet₁ = Set.Ioc (e.grid n) (e.grid (n + 1)) :=
  by simp

theorem gridbox_le_box {n : ℤ} (hn : n ∈ e.indices) : e.gridbox n ≤ e.box := by
  simpa [gridbox, box, Ioc_le_Ioc_iff, e.hab, e.grid_succ_gt n, indices] using hn

noncomputable def index : ℝ → ℤ := fun x ↦ ⌈(x - e.a) / e.δ⌉ - 1

theorem grid_lt_iff : e.grid n < x ↔ n ≤ e.index x := by
  have := e.delta_pos
  simp [index, grid, Int.le_sub_one_iff, Int.lt_ceil]; field_simp; grind

theorem grid_index_lt : e.grid (e.index x) < x := by simp [grid_lt_iff]

theorem le_grid_iff : x ≤ e.grid n ↔ e.index x < n := by
  have := e.delta_pos
  simp [index, grid, Int.sub_one_lt_iff, Int.ceil_le]; field_simp; grind

theorem le_grid_succ_index : x ≤ e.grid (e.index x + 1) := by simp [le_grid_iff]

theorem mem_gridbox_iff₁ : x ∈ (e.gridbox n).toSet₁ ↔ e.index x = n := by
  simp [grid_lt_iff, le_grid_iff]; omega

theorem mem_gridbox_iff (x : Fin 1 → ℝ) (n : ℤ) : x ∈ e.gridbox n ↔ e.index (x 0) = n := by
  simp [grid_lt_iff, le_grid_iff]; omega

theorem mem_box_iff : x ∈ e.box.toSet₁ ↔ e.index x ∈ e.indices := by
  simp [indices, ←grid_zero, ←grid_N, grid_lt_iff, le_grid_iff]

open Classical in
noncomputable def toPrepartition : Prepartition e.box :=
  {
    boxes := (e.indices).image e.gridbox
    le_of_mem' J hJ := by
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hJ
      exact e.gridbox_le_box hj
    pairwiseDisjoint I hI J hJ hdisj := by
      simp only [coe_image, Set.mem_image] at hI hJ
      obtain ⟨i, hi, rfl⟩ := hI
      obtain ⟨j, hj, rfl⟩ := hJ
      simp [Box.disjoint_iff₁, e.grid_strictMono.le_iff_le]
      lia
  }

@[simp]
theorem mem_toPrepartition_iff (J : Box (Fin 1)) :
    J ∈ e.toPrepartition ↔ ∃ n ∈ e.indices, e.gridbox n = J := by simp [toPrepartition]

theorem toPrepartition_isPartition : (e.toPrepartition).IsPartition := by
  intro x hx
  simp [box, hab] at hx
  refine ⟨ e.gridbox (e.index (x 0)), ?_, by simp [grid_index_lt, le_grid_succ_index] ⟩
  simp only [Fin.isValue, mem_toPrepartition_iff, indices]
  use e.index (x 0)
  simp [← grid_lt_iff, ← le_grid_iff, hx]

theorem len_of_subbox {J : Box (Fin 1)} (hJ : J ∈ e.toPrepartition) : J.len = e.δ := by
  simp only [toPrepartition, mem_mk, mem_image] at hJ
  obtain ⟨n, hn, rfl⟩ := hJ
  simp


/-- Can delete once #40745 lands in mathlib -/
@[simp]
theorem forall_in_set_const {p : Prop} {α : Type*} (S : Set α) [Nonempty S] : (∀ x ∈ S, p) ↔ p :=
  by aesop

/-- Can delete once #40745 lands in mathlib -/
@[simp]
theorem forall_in_finset_const {p : Prop} {α : Type*} (S : Finset α) [Nonempty S] :
  (∀ x ∈ S, p) ↔ p := forall_in_set_const _

theorem mesh_size_toPrepartition : (e.toPrepartition).mesh_size = e.δ.toNNReal
  := by
  apply eq_of_forall_ge_iff
  simp [-mesh_size_le_iff, toPrepartition, Real.toNNReal_le_iff_le_coe]

end Even

end Prepartition

end BoxIntegral
