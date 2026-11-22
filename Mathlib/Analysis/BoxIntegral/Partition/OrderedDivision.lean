/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Box.Ioc
public import Mathlib.Analysis.BoxIntegral.Partition.Basic
public import Mathlib.Analysis.BoxIntegral.Partition.Onedim
public import Mathlib.Data.Finset.Sort

/-! # Ordered divisions of intervals

This file defines ordered one-dimensional divisions and their canonical prepartitions of
`BoxIntegral.Ioc a b`.

It also defines tagged divisions and duplicate-removal for tagged divisions, and the two
translations used in the proof of Riemann–Stieltjes integration by parts:

* `TaggedDivision.toTaggedPrepartition`: a tagged division of `[a, b]` with valid tags (possibly
  with repeated division points) gives a Henstock tagged partition of `Ioc a b`, made of its
  nondegenerate subintervals.
* `TaggedPrepartition.toTaggedDivision`: a tagged partition of `Ioc a b` gives the tagged division
  whose division points are the endpoints of its boxes, in increasing order.

## AI usage

The following were written by Claude (Anthropic) in November 2026, replacing `sorry`s: the
proofs of `OrderedDivision.fromPartition_map` and `TaggedDivision.removeDuplicates.first`; the
definitions `TaggedDivision.toTaggedPrepartition` (via `TaggedDivision.posIdx` and
`TaggedDivision.toPrepartition`) and `TaggedPrepartition.toTaggedDivision`, with all the lemmas
about them; and the lemmas in the `boundaries` section. They compile, but have not been reviewed
by a human. Note that `toTaggedPrepartition` drops degenerate subintervals directly, so the
integration-by-parts argument no longer uses `TaggedDivision.removeDuplicates`.
-/

@[expose] public section

namespace BoxIntegral

/-! ## Ordered divisions -/

/-- Raw finite data for an ordered division of an interval. Correctness properties are added
separately. -/
structure OrderedDivision where
  /-- The number of subintervals. There are `N + 1` division points. -/
  N : ℕ
  /-- The division points. -/
  x : Fin (N + 1) → ℝ

namespace OrderedDivision

/-- The division points are strictly increasing. -/
def StrictMono (π : OrderedDivision) : Prop :=
  _root_.StrictMono π.x

/-- Add one point to the right of an ordered division. -/
def snoc (π : OrderedDivision) (c : ℝ) : OrderedDivision where
  N := π.N + 1
  x := Fin.snoc π.x c

/-- The `i`th subinterval of an ordered division, as a one-dimensional box. -/
noncomputable def box (π : OrderedDivision) (i : Fin π.N) : Box (Fin 1) :=
  Ioc (π.x i.castSucc) (π.x i.succ)

theorem box_injective {π : OrderedDivision} (hπ : π.StrictMono) :
    Function.Injective π.box := by
  intro i j hij
  apply Fin.castSucc_injective
  exact hπ.injective <| by
    have h := congrFun (congrArg Box.lower hij) 0
    simpa [box, Ioc.lower (hπ i.castSucc_lt_succ),
      Ioc.lower (hπ j.castSucc_lt_succ)] using h

noncomputable def boxMap {π : OrderedDivision} (hπ : π.StrictMono) : Finset (Box (Fin 1)) :=
  (Finset.univ : Finset (Fin π.N)).map ⟨π.box, π.box_injective hπ⟩

/-- The prepartition of `Ioc a b` associated to an ordered division with endpoints `a` and `b`. -/
noncomputable def toPrepartition {a b : ℝ}
    {π : OrderedDivision} (hπ : π.StrictMono)
    (ha : π.x 0 = a) (hb : π.x (Fin.last π.N) = b) :
    Prepartition (Ioc a b) where
  boxes := π.boxMap hπ
  le_of_mem' := by
    intro J hJ
    unfold boxMap at hJ
    rw [Finset.mem_map] at hJ
    rcases hJ with ⟨i, _, rfl⟩
    have hsub_left : π.x 0 ≤ π.x i.castSucc := hπ.monotone (Fin.zero_le _)
    have hsub_right : π.x i.succ ≤ π.x (Fin.last π.N) := hπ.monotone (Fin.le_last _)
    have hab : a < b := by
      rw [← ha, ← hb]
      exact hsub_left.trans_lt ((hπ i.castSucc_lt_succ).trans_le hsub_right)
    rw [Box.le_iff_bounds]
    constructor
    · intro k
      have hk : k = 0 := Subsingleton.elim k 0
      subst k
      simpa [box, Ioc.lower (hπ i.castSucc_lt_succ), Ioc.lower hab, ha] using hsub_left
    · intro k
      have hk : k = 0 := Subsingleton.elim k 0
      subst k
      simpa [box, Ioc.upper (hπ i.castSucc_lt_succ), Ioc.upper hab, hb] using hsub_right
  pairwiseDisjoint := by
    intro J hJ K hK hne
    simp only [Finset.mem_coe] at hJ hK
    unfold boxMap at *
    rw [Finset.mem_map] at hJ hK
    rcases hJ with ⟨i, _, rfl⟩
    rcases hK with ⟨j, _, rfl⟩
    rw [Function.onFun]
    refine Set.disjoint_left.2 ?_
    intro y hyi hyj
    by_cases hij : i = j
    · subst j
      exact hne rfl
    · rcases lt_or_gt_of_ne hij with hij | hji
      · have hle : i.succ ≤ j.castSucc := by
          simpa [Fin.succ_le_castSucc_iff] using hij
        have hyi' := (mem_Ioc (hπ i.castSucc_lt_succ) y).1 hyi
        have hyj' := (mem_Ioc (hπ j.castSucc_lt_succ) y).1 hyj
        exact not_lt_of_ge (hyi'.2.trans (hπ.monotone hle)) hyj'.1
      · have hle : j.succ ≤ i.castSucc := by
          simpa [Fin.succ_le_castSucc_iff] using hji
        have hyi' := (mem_Ioc (hπ i.castSucc_lt_succ) y).1 hyi
        have hyj' := (mem_Ioc (hπ j.castSucc_lt_succ) y).1 hyj
        exact not_lt_of_ge (hyj'.2.trans (hπ.monotone hle)) hyi'.1

theorem toPrepartition_isPartition {a b : ℝ}
    (π : OrderedDivision) (hπ : π.StrictMono) (hN : 0 < π.N)
    (ha : π.x 0 = a) (hb : π.x (Fin.last π.N) = b) :
    (π.toPrepartition hπ ha hb).IsPartition := by
  classical
  intro y hy
  have hab : a < b := by
    rw [← ha, ← hb]
    exact hπ (by simpa [Fin.lt_def] using hN)
  obtain ⟨hya, hyb⟩ := (mem_Ioc hab y).1 hy
  -- `M` is the (nonempty) set of indices `k` with `y 0 ≤ π.x k`; take its minimum.
  let M : Finset (Fin (π.N + 1)) := Finset.univ.filter fun k ↦ y 0 ≤ π.x k
  have hM_ne : M.Nonempty :=
    ⟨Fin.last π.N, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb ▸ hyb⟩⟩
  set m := M.min' hM_ne
  have hm_le : y 0 ≤ π.x m := (Finset.mem_filter.mp (M.min'_mem hM_ne)).2
  have hm_pos : 0 < (m : ℕ) := by
    rcases Nat.eq_zero_or_pos (m : ℕ) with h | h
    · refine absurd (?_ : y 0 ≤ a) (not_le.mpr hya)
      simpa [show m = 0 from Fin.ext h, ha] using hm_le
    · exact h
  let i : Fin π.N := ⟨(m : ℕ) - 1, by have := m.2; omega⟩
  have h_succ : i.succ = m := Fin.ext (by change (m : ℕ) - 1 + 1 = (m : ℕ); omega)
  refine ⟨π.box i, ?_, ?_⟩
  · change π.box i ∈ (π.toPrepartition hπ ha hb).boxes
    simp [toPrepartition, boxMap]
  · refine (mem_Ioc (hπ i.castSucc_lt_succ) y).2 ⟨?_, h_succ ▸ hm_le⟩
    by_contra hge
    have hle : m ≤ i.castSucc :=
      M.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩)
    exact absurd hle (not_le.mpr (by change (m : ℕ) - 1 < (m : ℕ); omega))

noncomputable def boundaries (a b : ℝ)
    (π : Prepartition (Ioc a b)) : Finset ℝ :=
  π.boxes.image (fun J ↦ J.lower 0) ∪ π.boxes.image (fun J ↦ J.upper 0)

/-- Build an `OrderedDivision` from a nonempty finset of reals: the division points are the
elements of `S` enumerated in increasing order. -/
noncomputable def ofFinset (S : Finset ℝ) (hS : S.Nonempty) : OrderedDivision where
  N := S.card - 1
  x := S.orderEmbOfFin (Nat.sub_add_cancel (Finset.card_pos.mpr hS)).symm

/-- Build an `OrderedDivision` from a prepartition. The result is meaningful when
`boundaries a b π` is nonempty (e.g. when `π` is a partition of a nondegenerate interval);
otherwise we return the trivial single-point division. -/
noncomputable def fromPartition {a b : ℝ} (π : Prepartition (Ioc a b)) :
    OrderedDivision :=
  open Classical in
  if hS : (boundaries a b π).Nonempty then ofFinset _ hS
  else { N := 0, x := fun _ ↦ a }

theorem fromPartition_of_nonempty {a b : ℝ} {π : Prepartition (Ioc a b)}
    (hS : (boundaries a b π).Nonempty) :
    fromPartition π = ofFinset (boundaries a b π) hS := by
  simp [fromPartition, hS]

theorem fromPartition_strictMono {a b : ℝ} (π : Prepartition (Ioc a b)) :
    (fromPartition π).StrictMono := by
  unfold fromPartition
  split_ifs with hS
  · exact ((boundaries a b π).orderEmbOfFin _).strictMono
  · intro i j hij
    have hi : (i : ℕ) < 1 := i.isLt
    have hj : (j : ℕ) < 1 := j.isLt
    have : (i : ℕ) < (j : ℕ) := hij
    omega

/-- Membership of a constant point in a one-dimensional box. -/
theorem _root_.BoxIntegral.Box.const_mem₁ {J : Box (Fin 1)} {s : ℝ} :
    (fun _ : Fin 1 ↦ s) ∈ J ↔ J.lower 0 < s ∧ s ≤ J.upper 0 := by
  rw [Box.mem_def, Fin.forall_fin_one]
  exact Iff.rfl

section boundaries

/-! ### Boundary points of a one-dimensional prepartition -/

variable {a b : ℝ} {π : Prepartition (Ioc a b)}

theorem mem_boundaries {s : ℝ} :
    s ∈ boundaries a b π ↔ ∃ J ∈ π, J.lower 0 = s ∨ J.upper 0 = s := by
  simp only [boundaries, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨J, hJ, h⟩ | ⟨J, hJ, h⟩)
    exacts [⟨J, hJ, .inl h⟩, ⟨J, hJ, .inr h⟩]
  · rintro ⟨J, hJ, h | h⟩
    exacts [.inl ⟨J, hJ, h⟩, .inr ⟨J, hJ, h⟩]

theorem boundaries_bounds {s : ℝ} (hs : s ∈ boundaries a b π) :
    (Ioc a b).lower 0 ≤ s ∧ s ≤ (Ioc a b).upper 0 := by
  obtain ⟨J, hJ, h⟩ := mem_boundaries.1 hs
  have hle := Box.le_iff_bounds.1 (π.le_of_mem hJ)
  have h1 : (Ioc a b).lower 0 ≤ J.lower 0 := hle.1 0
  have h2 : J.upper 0 ≤ (Ioc a b).upper 0 := hle.2 0
  have h3 := J.lower_lt_upper 0
  rcases h with rfl | rfl
  · exact ⟨h1, by linarith⟩
  · exact ⟨by linarith, h2⟩

/-- No boundary point of a prepartition lies in the interior of one of its boxes. -/
theorem not_mem_interior_of_mem_boundaries {s : ℝ} (hs : s ∈ boundaries a b π)
    {J : Box (Fin 1)} (hJ : J ∈ π) : ¬ (J.lower 0 < s ∧ s < J.upper 0) := by
  rintro ⟨hl, hu⟩
  have hKlu : ∀ K : Box (Fin 1), K.lower 0 < K.upper 0 := fun K ↦ K.lower_lt_upper 0
  obtain ⟨K, hK, h | h⟩ := mem_boundaries.1 hs
  · -- `s` is the left endpoint of `K`: points just to the right of `s` lie in `J` and in `K`.
    have hJ' : (fun _ : Fin 1 ↦ min (J.upper 0) (K.upper 0)) ∈ J :=
      Box.const_mem₁.2 ⟨lt_min (by linarith) (by linarith [hKlu K]), min_le_left _ _⟩
    have hK' : (fun _ : Fin 1 ↦ min (J.upper 0) (K.upper 0)) ∈ K :=
      Box.const_mem₁.2 ⟨lt_min (by linarith) (hKlu K), min_le_right _ _⟩
    obtain rfl := π.eq_of_mem_of_mem hJ hK hJ' hK'
    linarith
  · -- `s` is the right endpoint of `K`, so it lies in both `J` and `K`.
    have hJ' : (fun _ : Fin 1 ↦ s) ∈ J := Box.const_mem₁.2 ⟨hl, hu.le⟩
    have hK' : (fun _ : Fin 1 ↦ s) ∈ K := Box.const_mem₁.2 ⟨by linarith [hKlu K], h.ge⟩
    obtain rfl := π.eq_of_mem_of_mem hJ hK hJ' hK'
    linarith

theorem boundaries_nonempty (hπ : π.IsPartition) : (boundaries a b π).Nonempty := by
  obtain ⟨J, hJ⟩ := hπ.nonempty_boxes
  exact ⟨J.lower 0, mem_boundaries.2 ⟨J, hJ, .inl rfl⟩⟩

theorem fromPartition_mem (hS : (boundaries a b π).Nonempty)
    (k : Fin ((fromPartition π).N + 1)) : (fromPartition π).x k ∈ boundaries a b π := by
  revert k
  rw [fromPartition_of_nonempty hS]
  exact fun k ↦ Finset.orderEmbOfFin_mem _ _ k

theorem exists_fromPartition_eq (hS : (boundaries a b π).Nonempty) {s : ℝ}
    (hs : s ∈ boundaries a b π) : ∃ k, (fromPartition π).x k = s := by
  rw [fromPartition_of_nonempty hS]
  have : s ∈ Set.range ((boundaries a b π).orderEmbOfFin
      (Nat.sub_add_cancel (Finset.card_pos.mpr hS)).symm) := by
    rw [Finset.range_orderEmbOfFin]
    exact hs
  exact this

theorem fromPartition_first (hab : a < b) (hπ : π.IsPartition) :
    (fromPartition π).x 0 = a := by
  have hS := boundaries_nonempty hπ
  have hmono := fromPartition_strictMono π
  have h0 := boundaries_bounds (fromPartition_mem hS 0)
  rw [Ioc.lower hab, Ioc.upper hab] at h0
  refine le_antisymm (not_lt.1 fun hlt ↦ ?_) h0.1
  obtain ⟨J, hJ, hxJ⟩ := hπ _ ((mem_Ioc hab (fun _ ↦ (fromPartition π).x 0)).2 ⟨hlt, h0.2⟩)
  rw [Box.const_mem₁] at hxJ
  obtain ⟨k, hk⟩ := exists_fromPartition_eq hS (mem_boundaries.2 ⟨J, hJ, .inl rfl⟩)
  have := hmono.monotone (Fin.zero_le k)
  linarith [hxJ.1]

theorem fromPartition_last (hab : a < b) (hπ : π.IsPartition) :
    (fromPartition π).x (Fin.last (fromPartition π).N) = b := by
  have hS := boundaries_nonempty hπ
  have hmono := fromPartition_strictMono π
  have hN := boundaries_bounds (fromPartition_mem hS (Fin.last (fromPartition π).N))
  rw [Ioc.lower hab, Ioc.upper hab] at hN
  refine le_antisymm hN.2 (not_lt.1 fun hlt ↦ ?_)
  obtain ⟨J, hJ, hxJ⟩ := hπ _ ((mem_Ioc hab (fun _ ↦ b)).2 ⟨hab, le_rfl⟩)
  rw [Box.const_mem₁] at hxJ
  obtain ⟨k, hk⟩ := exists_fromPartition_eq hS (mem_boundaries.2 ⟨J, hJ, .inr rfl⟩)
  have := hmono.monotone (Fin.le_last k)
  linarith [hxJ.2]

/-- Every interval between consecutive boundary points of a partition is one of its boxes. -/
theorem box_fromPartition_mem (hπ : π.IsPartition) (i : Fin (fromPartition π).N) :
    (fromPartition π).box i ∈ π := by
  have hS := boundaries_nonempty hπ
  have hmono : _root_.StrictMono (fromPartition π).x := fromPartition_strictMono π
  have hmem := fromPartition_mem hS
  have hlt : (fromPartition π).x i.castSucc < (fromPartition π).x i.succ :=
    hmono Fin.castSucc_lt_succ
  -- The right endpoint of the `i`th interval lies in some box `J` of `π`.
  have hp : (fun _ : Fin 1 ↦ (fromPartition π).x i.succ) ∈ Ioc a b := by
    rw [Box.const_mem₁]
    exact ⟨(boundaries_bounds (hmem i.castSucc)).1.trans_lt hlt,
      (boundaries_bounds (hmem i.succ)).2⟩
  obtain ⟨J, hJ, hpJ⟩ := hπ _ hp
  rw [Box.const_mem₁] at hpJ
  -- Since no boundary point lies inside `J`, the endpoints of `J` are those of the interval.
  have hlow : J.lower 0 = (fromPartition π).x i.castSucc := by
    obtain ⟨k, hk⟩ := exists_fromPartition_eq hS (mem_boundaries.2 ⟨J, hJ, .inl rfl⟩)
    have hk_lt : (fromPartition π).x k < (fromPartition π).x i.succ := hk ▸ hpJ.1
    have h1 : J.lower 0 ≤ (fromPartition π).x i.castSucc :=
      hk ▸ hmono.monotone (Fin.le_castSucc_iff.2 (hmono.lt_iff_lt.1 hk_lt))
    refine le_antisymm h1 (not_lt.1 fun h ↦ ?_)
    exact not_mem_interior_of_mem_boundaries (hmem i.castSucc) hJ ⟨h, hlt.trans_le hpJ.2⟩
  have hup : J.upper 0 = (fromPartition π).x i.succ := by
    refine le_antisymm (not_lt.1 fun h ↦ ?_) hpJ.2
    exact not_mem_interior_of_mem_boundaries (hmem i.succ) hJ ⟨hpJ.1, h⟩
  have hJ_eq : J = (fromPartition π).box i := by
    rw [Box.congr₁]
    simp only [box, Ioc.lower₁ hlt, Ioc.upper₁ hlt]
    exact ⟨hlow, hup⟩
  exact hJ_eq ▸ hJ

theorem fromPartition_map (hπ : π.IsPartition) :
    boxMap (fromPartition_strictMono π) = π.boxes := by
  have hS := boundaries_nonempty hπ
  have hmono : _root_.StrictMono (fromPartition π).x := fromPartition_strictMono π
  refine Finset.Subset.antisymm (fun J hJ ↦ ?_) (fun J hJ ↦ ?_)
  · obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hJ
    exact box_fromPartition_mem hπ i
  · -- The right endpoint of `J` is a division point other than the first one.
    obtain ⟨m, hm⟩ := exists_fromPartition_eq hS (mem_boundaries.2 ⟨J, hJ, .inr rfl⟩)
    have hm0 : m ≠ 0 := by
      rintro rfl
      obtain ⟨k, hk⟩ := exists_fromPartition_eq hS (mem_boundaries.2 ⟨J, hJ, .inl rfl⟩)
      have := hmono.monotone (Fin.zero_le k)
      linarith [J.lower_lt_upper 0]
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hm0
    have hlt : (fromPartition π).x i.castSucc < (fromPartition π).x i.succ :=
      hmono Fin.castSucc_lt_succ
    -- `J` and the `i`th interval share the point `J.upper`, so they coincide.
    have hJ' : (fun _ : Fin 1 ↦ J.upper 0) ∈ J := Box.const_mem₁.2 ⟨J.lower_lt_upper 0, le_rfl⟩
    have hi' : (fun _ : Fin 1 ↦ J.upper 0) ∈ (fromPartition π).box i := by
      rw [Box.const_mem₁]
      simp only [box, Ioc.lower hlt, Ioc.upper hlt]
      exact ⟨hm ▸ hlt, hm.ge⟩
    have := π.eq_of_mem_of_mem hJ (box_fromPartition_mem hπ i) hJ' hi'
    exact Finset.mem_map.2 ⟨i, Finset.mem_univ _, this.symm⟩

end boundaries

end OrderedDivision

/-! ## Helper lemmas for snoc -/

/-- If we add a new value to the right of a monotone `Fin`-indexed function, preserving the
last-value inequality, the resulting `Fin.snoc` is monotone. -/
theorem monotone_fin_snoc {n : ℕ} {f : Fin (n + 1) → ℝ} {x : ℝ}
    (hf : Monotone f) (hx : f (Fin.last n) ≤ x) : Monotone (Fin.snoc f x) := by
  intro i j hij
  cases j using Fin.lastCases with
  | last =>
      rw [Fin.snoc_last]
      cases i using Fin.lastCases with
      | last => simp
      | cast i =>
          rw [Fin.snoc_castSucc]
          exact (hf i.le_last).trans hx
  | cast j =>
      cases i using Fin.lastCases with
      | last =>
          exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
      | cast i =>
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hf hij

/-- If we add a new value to the right of a strictly monotone `Fin`-indexed function, preserving
the strict last-value inequality, the resulting `Fin.snoc` is strictly monotone. -/
theorem strictMono_fin_snoc {n : ℕ} {f : Fin (n + 1) → ℝ} {x : ℝ}
    (hf : StrictMono f) (hx : f (Fin.last n) < x) : StrictMono (Fin.snoc f x) := by
  intro i j hij
  cases j using Fin.lastCases with
  | last =>
      rw [Fin.snoc_last]
      cases i using Fin.lastCases with
      | last => exact False.elim (not_lt_of_ge le_rfl hij)
      | cast i =>
          rw [Fin.snoc_castSucc]
          exact lt_of_le_of_lt (hf.monotone i.le_last) hx
  | cast j =>
      cases i using Fin.lastCases with
      | last =>
          exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
      | cast i =>
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hf hij

/-! ## Tagged divisions -/

/-- A tagged division is an ordered division together with one tag in each subinterval. The
validity of the tags is kept as a separate predicate. -/
structure TaggedDivision extends OrderedDivision where
  /-- The tag in the corresponding subinterval. -/
  tag : Fin N → ℝ

namespace OrderedDivision

/-- Tag each interval of an ordered division by its left endpoint. -/
def toLeftTagged (π : OrderedDivision) : TaggedDivision where
  toOrderedDivision := π
  tag := fun i ↦ π.x i.castSucc

end OrderedDivision

namespace TaggedDivision

/-- The division points are monotone. -/
def Monotone (π : TaggedDivision) : Prop :=
  _root_.Monotone π.x

/-- Each tag lies in its corresponding closed subinterval of consecutive division points. -/
def ValidTags (π : TaggedDivision) : Prop :=
  ∀ i, π.x i.castSucc ≤ π.tag i ∧ π.tag i ≤ π.x i.succ

theorem validTags_monotone (π : TaggedDivision) (hπ : π.ValidTags) : π.Monotone :=
  Fin.monotone_iff_le_succ.2 fun i ↦ (hπ i).1.trans (hπ i).2

theorem validTags_last (π : TaggedDivision) (hπ : π.ValidTags)
    (hN : 0 < π.N := by omega) :
    π.x ⟨π.N - 1, by omega⟩ ≤ π.tag ⟨π.N - 1, by omega⟩ ∧
      π.tag ⟨π.N - 1, by omega⟩ ≤ π.x (Fin.last π.N) := by
  have htag := hπ ⟨π.N - 1, by omega⟩
  constructor
  · simpa using htag.1
  · have hs : (⟨π.N - 1, by omega⟩ : Fin π.N).succ = Fin.last π.N := by
      ext
      simp
      omega
    simpa [hs] using htag.2

/-- The division points are strictly increasing. -/
def StrictMono (π : TaggedDivision) : Prop :=
  _root_.StrictMono π.x

/-- Add a new division point and a tag for the newly-created final subinterval. -/
def snoc (π : TaggedDivision) (c t : ℝ) : TaggedDivision where
  toOrderedDivision := π.toOrderedDivision.snoc c
  tag := Fin.snoc π.tag t

/-- Remove the final interval of a nonempty tagged division. -/
def dropLast (π : TaggedDivision) (hN : 0 < π.N := by omega) : TaggedDivision :=
  by
    rcases π with ⟨⟨N, x⟩, tag⟩
    dsimp at hN ⊢
    cases N with
    | zero => omega
    | succ n =>
        exact
          { N := n
            x := fun i ↦ x i.castSucc
            tag := fun i ↦ tag i.castSucc }

@[simp]
theorem dropLast_N (π : TaggedDivision) (hN : 0 < π.N := by omega) :
    π.dropLast.N = π.N - 1 := by
  rcases π with ⟨⟨N, x⟩, tag⟩
  dsimp [dropLast] at hN ⊢
  cases N with
  | zero => omega
  | succ n => simp

theorem dropLast_last (π : TaggedDivision) (hN : 0 < π.N := by omega) :
    π.dropLast.x (Fin.last π.dropLast.N) =
      π.x ⟨π.N - 1, by omega⟩ := by
  rcases π with ⟨⟨N, x⟩, tag⟩
  dsimp [dropLast] at hN ⊢
  cases N with
  | zero => omega
  | succ n => exact congrArg x (by ext; simp)

theorem dropLast_monotone (π : TaggedDivision) (hπ : π.Monotone)
    (hN : 0 < π.N := by omega) :
    π.dropLast.Monotone := by
  rcases π with ⟨⟨N, x⟩, tag⟩
  dsimp [Monotone, dropLast] at hπ hN ⊢
  cases N with
  | zero => omega
  | succ n => intro i j hij; exact hπ hij

theorem dropLast_validTags (π : TaggedDivision) (hπ : π.ValidTags)
    (hN : 0 < π.N := by omega) :
    π.dropLast.ValidTags := by
  rcases π with ⟨⟨N, x⟩, tag⟩
  dsimp [ValidTags, dropLast] at hπ hN ⊢
  cases N with
  | zero => omega
  | succ n => intro i; simpa using hπ i.castSucc

/-- Recursion over tagged divisions by repeatedly dropping the final interval. -/
noncomputable def recOnDropLast {motive : TaggedDivision → Sort _} (π : TaggedDivision)
    (zero : ∀ π, π.N = 0 → motive π)
    (step : ∀ π (hN : 0 < π.N), motive (π.dropLast (hN := hN)) → motive π) :
    motive π :=
  if h0 : π.N = 0 then
    zero π h0
  else
    have hN : 0 < π.N := Nat.pos_of_ne_zero h0
    step π hN (recOnDropLast (π.dropLast (hN := hN)) zero step)
termination_by π.N
decreasing_by rw [dropLast_N π]; omega

theorem snoc_monotone (π : TaggedDivision) (hπ : π.Monotone) {c t : ℝ}
    (hc : π.x (Fin.last π.N) ≤ c) : (π.snoc c t).Monotone :=
  monotone_fin_snoc hπ hc

theorem snoc_validTags (π : TaggedDivision) (hπ_tag : π.ValidTags)
    {c t : ℝ} (ht : π.x (Fin.last π.N) ≤ t ∧ t ≤ c) : (π.snoc c t).ValidTags := by
  intro i
  cases i using Fin.lastCases with
  | last => simp [snoc, OrderedDivision.snoc, ht]
  | cast i => simpa [snoc, OrderedDivision.snoc, ← Fin.castSucc_succ] using hπ_tag i

theorem snoc_strict (π : TaggedDivision) (hπ : π.StrictMono) {c t : ℝ}
    (hc : π.x (Fin.last π.N) < c) : (π.snoc c t).StrictMono :=
  strictMono_fin_snoc hπ hc

/-! ### Removing duplicate division points -/

/-- Remove repeated consecutive division points from a tagged division. -/
noncomputable def removeDuplicates (π : TaggedDivision) : TaggedDivision :=
  π.recOnDropLast
    (zero := fun π _ ↦ π)
    (step := fun π _ σ ↦
      let y := π.x ⟨π.N - 1, by omega⟩
      let z := π.x (Fin.last π.N)
      if y = z then
        σ
      else
        σ.snoc z (π.tag ⟨π.N - 1, by omega⟩))

namespace removeDuplicates

theorem of_N_eq_zero (π : TaggedDivision) (hπ : π.N = 0) : π.removeDuplicates = π := by
  rw [TaggedDivision.removeDuplicates, TaggedDivision.recOnDropLast]
  simp [hπ]

theorem of_last_eq (π : TaggedDivision) (hN : 0 < π.N)
    (h : π.x ⟨π.N - 1, by omega⟩ = π.x (Fin.last π.N)) :
    π.removeDuplicates = π.dropLast.removeDuplicates := by
  rw [TaggedDivision.removeDuplicates, TaggedDivision.recOnDropLast]
  simp [Nat.ne_of_gt hN, h, TaggedDivision.removeDuplicates]

theorem of_last_ne (π : TaggedDivision) (hN : 0 < π.N)
    (h : ¬π.x ⟨π.N - 1, by omega⟩ = π.x (Fin.last π.N)) :
    π.removeDuplicates =
      π.dropLast.removeDuplicates.snoc (π.x (Fin.last π.N))
        (π.tag ⟨π.N - 1, by omega⟩) := by
  rw [TaggedDivision.removeDuplicates, TaggedDivision.recOnDropLast]
  simp [Nat.ne_of_gt hN, h, TaggedDivision.removeDuplicates]

theorem last (π : TaggedDivision) :
    π.removeDuplicates.x (Fin.last π.removeDuplicates.N) = π.x (Fin.last π.N) := by
  induction π using TaggedDivision.recOnDropLast with
  | zero π h0 =>
    rw [of_N_eq_zero π h0]
  | step π hN ih =>
    have h0 : ¬π.N = 0 := by omega
    let y := π.x ⟨π.N - 1, by omega⟩
    let z := π.x (Fin.last π.N)
    let σ := π.dropLast.removeDuplicates
    have hσ : σ.x (Fin.last σ.N) = y := by
      dsimp [σ]
      rw [ih]
      exact π.dropLast_last
    by_cases h : y = z
    · rw [of_last_eq π hN (by simpa [y, z] using h)]
      exact hσ.trans h
    · rw [of_last_ne π hN (by simpa [y, z] using h)]
      simp [snoc, OrderedDivision.snoc]

theorem first (π : TaggedDivision) :
    π.removeDuplicates.x 0 = π.x 0 := by
  induction π using TaggedDivision.recOnDropLast with
  | zero π h0 =>
    rw [of_N_eq_zero π h0]
  | step π hN ih =>
    have h0 : π.dropLast.x 0 = π.x 0 := by
      rcases π with ⟨⟨N, x⟩, tag⟩
      dsimp at hN
      cases N with
      | zero => omega
      | succ n => rfl
    by_cases h : π.x ⟨π.N - 1, by omega⟩ = π.x (Fin.last π.N)
    · rw [of_last_eq π hN h, ih, h0]
    · rw [of_last_ne π hN h]
      change Fin.snoc (α := fun _ ↦ ℝ) (π.dropLast hN).removeDuplicates.x (π.x (Fin.last π.N))
        (Fin.castSucc 0) = π.x 0
      rw [Fin.snoc_castSucc, ih, h0]

theorem strict (π : TaggedDivision) (hπ : π.Monotone) :
    π.removeDuplicates.StrictMono := by
  revert hπ
  induction π using TaggedDivision.recOnDropLast with
  | zero π h0 =>
    intro hπ
    rw [of_N_eq_zero π h0]
    dsimp [StrictMono]
    intro i j hij
    have hij' : i = j := by ext; omega
    subst j
    exact False.elim (not_lt_of_ge le_rfl hij)
  | step π hN ih =>
    intro hπ
    have h0 : ¬π.N = 0 := by omega
    let y := π.x ⟨π.N - 1, by omega⟩
    let z := π.x (Fin.last π.N)
    let σ := π.dropLast.removeDuplicates
    have hσ_last : σ.x (Fin.last σ.N) = y := by
      dsimp [σ]
      rw [last π.dropLast]
      exact π.dropLast_last
    have hσ : σ.StrictMono := by
      dsimp [σ]
      exact ih (π.dropLast_monotone hπ)
    by_cases h : y = z
    · rw [of_last_eq π hN (by simpa [y, z] using h)]
      exact hσ
    · have hle : y ≤ z := by
        simpa [y, z] using hπ (Fin.le_last (⟨π.N - 1, by omega⟩ : Fin (π.N + 1)))
      have hlt : y < z := lt_of_le_of_ne hle h
      have hc : σ.x (Fin.last σ.N) < z := by simpa [hσ_last] using hlt
      rw [of_last_ne π hN (by simpa [y, z] using h)]
      exact σ.snoc_strict hσ hc

theorem validTags (π : TaggedDivision) (hπ_tag : π.ValidTags) :
    π.removeDuplicates.ValidTags := by
  revert hπ_tag
  induction π using TaggedDivision.recOnDropLast with
  | zero π h0 =>
    intro hπ_tag
    rw [of_N_eq_zero π h0]
    exact hπ_tag
  | step π hN ih =>
    intro hπ_tag
    have h0 : ¬π.N = 0 := by omega
    let y := π.x ⟨π.N - 1, by omega⟩
    let z := π.x (Fin.last π.N)
    let σ := π.dropLast.removeDuplicates
    have hσ_last : σ.x (Fin.last σ.N) = y := by
      dsimp [σ]
      rw [last π.dropLast]
      exact π.dropLast_last
    have hπ'_tag : π.dropLast.ValidTags := π.dropLast_validTags hπ_tag
    have hσ_tag : σ.ValidTags := by
      dsimp [σ]
      exact ih hπ'_tag
    by_cases h : y = z
    · rw [of_last_eq π hN (by simpa [y, z] using h)]
      exact hσ_tag
    · have ht : σ.x (Fin.last σ.N) ≤ π.tag ⟨π.N - 1, by omega⟩ ∧
          π.tag ⟨π.N - 1, by omega⟩ ≤ z := by
        have htag := π.validTags_last hπ_tag
        constructor
        · simpa [hσ_last, y] using htag.1
        · simpa [z] using htag.2
      rw [of_last_ne π hN (by simpa [y, z] using h)]
      exact σ.snoc_validTags hσ_tag ht

end removeDuplicates

/-! ### The tagged prepartition associated to a tagged division

A tagged division may have repeated consecutive division points (this happens for the dual
division used in summation by parts). The associated tagged prepartition keeps the
nondegenerate subintervals only; the degenerate ones contribute nothing to Riemann–Stieltjes
sums or to the mesh size. -/

/-- The indices of the nondegenerate subintervals of a tagged division. -/
noncomputable def posIdx (π : TaggedDivision) : Finset (Fin π.N) :=
  Finset.univ.filter fun i ↦ π.x i.castSucc < π.x i.succ

theorem mem_posIdx {π : TaggedDivision} {i : Fin π.N} :
    i ∈ π.posIdx ↔ π.x i.castSucc < π.x i.succ := by
  simp [posIdx]

/-- For a monotone division, distinct nondegenerate subintervals are disjoint. -/
theorem disjoint_box {π : TaggedDivision} (hπ : π.Monotone) {i j : Fin π.N}
    (hi : i ∈ π.posIdx) (hj : j ∈ π.posIdx) (hij : i ≠ j) :
    Disjoint (π.box i : Set (Fin 1 → ℝ)) (π.box j) := by
  rw [mem_posIdx] at hi hj
  refine Set.disjoint_left.2 fun y hyi hyj ↦ ?_
  have hyi' := (mem_Ioc hi y).1 hyi
  have hyj' := (mem_Ioc hj y).1 hyj
  rcases lt_or_gt_of_ne hij with h | h
  · exact not_lt_of_ge (hyi'.2.trans (hπ (Fin.succ_le_castSucc_iff.2 h))) hyj'.1
  · exact not_lt_of_ge (hyj'.2.trans (hπ (Fin.succ_le_castSucc_iff.2 h))) hyi'.1

theorem box_injOn {π : TaggedDivision} (hπ : π.Monotone) :
    Set.InjOn π.box π.posIdx := by
  intro i hi j hj hij
  by_contra hne
  have hd := disjoint_box hπ hi hj hne
  rw [hij] at hd
  exact Set.disjoint_left.1 hd (π.box j).upper_mem (π.box j).upper_mem

open Classical in
/-- The prepartition of `Ioc a b` formed by the nondegenerate subintervals of a monotone
division of `[a, b]`. -/
noncomputable def toPrepartition {a b : ℝ} (π : TaggedDivision) (hπ : π.Monotone)
    (ha : π.x 0 = a) (hb : π.x (Fin.last π.N) = b) : Prepartition (Ioc a b) where
  boxes := π.posIdx.image π.box
  le_of_mem' J hJ := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hJ
    have hi' := mem_posIdx.1 hi
    have h0 : a ≤ π.x i.castSucc := by rw [← ha]; exact hπ (Fin.zero_le _)
    have hN : π.x i.succ ≤ b := by rw [← hb]; exact hπ (Fin.le_last _)
    exact (Ioc_le_Ioc_iff (h0.trans_lt (hi'.trans_le hN)) hi').2 ⟨h0, hN⟩
  pairwiseDisjoint J hJ K hK hne := by
    rw [Finset.mem_coe, Finset.mem_image] at hJ hK
    obtain ⟨i, hi, rfl⟩ := hJ
    obtain ⟨j, hj, rfl⟩ := hK
    exact disjoint_box hπ hi hj (by rintro rfl; exact hne rfl)

open Classical in
/-- The tagged prepartition of `Ioc a b` associated to a tagged division with valid tags and
endpoints `a` and `b`: its boxes are the nondegenerate subintervals, with the tags of the
division. -/
noncomputable def toTaggedPrepartition {a b : ℝ} (π : TaggedDivision) (hπ : π.ValidTags)
    (ha : π.x 0 = a) (hb : π.x (Fin.last π.N) = b) :
    TaggedPrepartition (Ioc a b) where
  toPrepartition := π.toPrepartition (π.validTags_monotone hπ) ha hb
  tag J := if h : ∃ i ∈ π.posIdx, π.box i = J then fun _ ↦ π.tag h.choose else (Ioc a b).lower
  tag_mem_Icc J := by
    split_ifs with h
    · have hi' := mem_posIdx.1 h.choose_spec.1
      have hmono := π.validTags_monotone hπ
      have h0 : a ≤ π.x h.choose.castSucc := by rw [← ha]; exact hmono (Fin.zero_le _)
      have hN : π.x h.choose.succ ≤ b := by rw [← hb]; exact hmono (Fin.le_last _)
      rw [Icc_of_Ioc (h0.trans_lt (hi'.trans_le hN))]
      exact ⟨h0.trans (hπ _).1, (hπ _).2.trans hN⟩
    · exact (Ioc a b).lower_mem_Icc

section toTaggedPrepartition

variable {a b : ℝ} (π : TaggedDivision) (hπ : π.ValidTags)
  (ha : π.x 0 = a) (hb : π.x (Fin.last π.N) = b)

open scoped Classical in
theorem toTaggedPrepartition_boxes :
    (π.toTaggedPrepartition hπ ha hb).boxes = π.posIdx.image π.box := rfl

open scoped Classical in
theorem mem_toTaggedPrepartition {J : Box (Fin 1)} :
    J ∈ π.toTaggedPrepartition hπ ha hb ↔ ∃ i ∈ π.posIdx, π.box i = J :=
  Finset.mem_image

theorem toTaggedPrepartition_tag {i : Fin π.N} (hi : i ∈ π.posIdx) :
    (π.toTaggedPrepartition hπ ha hb).tag (π.box i) = fun _ ↦ π.tag i := by
  have h : ∃ j ∈ π.posIdx, π.box j = π.box i := ⟨i, hi, rfl⟩
  have hc : h.choose = i :=
    box_injOn (π.validTags_monotone hπ) h.choose_spec.1 hi h.choose_spec.2
  simp only [toTaggedPrepartition, dif_pos h, hc]

/-- The tagged prepartition associated to a tagged division with valid tags is Henstock. -/
theorem toTaggedPrepartition_isHenstock :
    (π.toTaggedPrepartition hπ ha hb).IsHenstock := by
  intro J hJ
  obtain ⟨i, hi, rfl⟩ := (mem_toTaggedPrepartition π hπ ha hb).1 hJ
  have hi' := mem_posIdx.1 hi
  rw [toTaggedPrepartition_tag π hπ ha hb hi, Box.mem_Icc₁, Box.Icc₁_def]
  simp only [OrderedDivision.box, Ioc.lower₁ hi', Ioc.upper₁ hi']
  exact hπ i

/-- The tagged prepartition associated to a tagged division of `[a, b]` with valid tags is a
partition of `Ioc a b`. (For `a = b` this fails, as `Ioc a a` is a junk box.) -/
theorem toTaggedPrepartition_isPartition (hab : a < b) :
    (π.toTaggedPrepartition hπ ha hb).IsPartition := by
  classical
  intro y hy
  obtain ⟨hya, hyb⟩ := (mem_Ioc hab y).1 hy
  -- `m` is the first division point that is `≥ y 0`; it is not the first one.
  let M : Finset (Fin (π.N + 1)) := Finset.univ.filter fun k ↦ y 0 ≤ π.x k
  have hM_ne : M.Nonempty :=
    ⟨Fin.last π.N, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb ▸ hyb⟩⟩
  set m := M.min' hM_ne
  have hm_le : y 0 ≤ π.x m := (Finset.mem_filter.mp (M.min'_mem hM_ne)).2
  have hm_pos : 0 < (m : ℕ) := by
    rcases Nat.eq_zero_or_pos (m : ℕ) with h | h
    · refine absurd (?_ : y 0 ≤ a) (not_le.mpr hya)
      simpa [show m = 0 from Fin.ext h, ha] using hm_le
    · exact h
  let i : Fin π.N := ⟨(m : ℕ) - 1, by have := m.2; omega⟩
  have h_succ : i.succ = m := Fin.ext (by change (m : ℕ) - 1 + 1 = (m : ℕ); omega)
  have hm_le' : y 0 ≤ π.x i.succ := by rw [h_succ]; exact hm_le
  have h_lt : π.x i.castSucc < y 0 := by
    by_contra hge
    have hle : m ≤ i.castSucc :=
      M.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩)
    exact absurd hle (not_le.mpr (by change (m : ℕ) - 1 < (m : ℕ); omega))
  have hi : π.x i.castSucc < π.x i.succ := h_lt.trans_le hm_le'
  exact ⟨π.box i, (mem_toTaggedPrepartition π hπ ha hb).2 ⟨i, mem_posIdx.2 hi, rfl⟩,
    (mem_Ioc hi y).2 ⟨h_lt, hm_le'⟩⟩

/-- The mesh size of the prepartition associated to a tagged division with valid tags is the
largest gap between consecutive division points. -/
theorem toTaggedPrepartition_mesh_size :
    (π.toTaggedPrepartition hπ ha hb).mesh_size =
      (Finset.univ : Finset (Fin π.N)).sup
        (fun i ↦ NNReal.mk (π.x i.succ - π.x i.castSucc)
          (sub_nonneg.mpr ((hπ i).1.trans (hπ i).2))) := by
  classical
  rw [mesh_size₁, toTaggedPrepartition_boxes, Finset.sup_image]
  have hlen : ∀ i ∈ π.posIdx, (π.box i).len = π.x i.succ - π.x i.castSucc := fun i hi ↦
    Ioc.len (mem_posIdx.1 hi)
  refine le_antisymm (Finset.sup_le fun i hi ↦ ?_) (Finset.sup_le fun i _ ↦ ?_)
  · refine le_of_eq_of_le ?_ (Finset.le_sup (Finset.mem_univ i))
    exact NNReal.eq (hlen i hi)
  · by_cases hi : i ∈ π.posIdx
    · refine le_of_eq_of_le ?_ (Finset.le_sup hi)
      exact NNReal.eq (hlen i hi).symm
    · have h0 : π.x i.succ - π.x i.castSucc = 0 := by
        have := (hπ i).1.trans (hπ i).2
        rw [mem_posIdx, not_lt] at hi
        linarith
      exact le_of_eq_of_le (NNReal.eq (h0.trans NNReal.coe_zero.symm)) zero_le

end toTaggedPrepartition

end TaggedDivision

namespace TaggedPrepartition

variable {a b : ℝ}

/-- The tagged division obtained by ordering the boxes of a one-dimensional tagged
prepartition: the division points are the endpoints of its boxes, in increasing order. -/
noncomputable def toTaggedDivision (π : TaggedPrepartition (Ioc a b)) : TaggedDivision where
  toOrderedDivision := OrderedDivision.fromPartition π.toPrepartition
  tag i := π.tag ((OrderedDivision.fromPartition π.toPrepartition).box i) 0

/-- Ordering a Henstock tagged partition gives a tagged division with valid tags. -/
theorem toTaggedDivision_validTags {π : TaggedPrepartition (Ioc a b)}
    (hπ_hen : π.IsHenstock) (hπ_part : π.IsPartition) :
    π.toTaggedDivision.ValidTags := by
  intro (i : Fin (OrderedDivision.fromPartition π.toPrepartition).N)
  have hmono : _root_.StrictMono (OrderedDivision.fromPartition π.toPrepartition).x :=
    OrderedDivision.fromPartition_strictMono π.toPrepartition
  have hlt := hmono (Fin.castSucc_lt_succ (i := i))
  have htag := hπ_hen _ (OrderedDivision.box_fromPartition_mem hπ_part i)
  rw [Box.mem_Icc₁, Box.Icc₁_def] at htag
  simp only [OrderedDivision.box, Ioc.lower₁ hlt, Ioc.upper₁ hlt] at htag
  exact htag

/-- The ordered tagged division associated to a tagged partition starts at the left endpoint. -/
theorem toTaggedDivision_first (π : TaggedPrepartition (Ioc a b))
    (hab : a < b) (hπ_part : π.IsPartition) :
    π.toTaggedDivision.x 0 = a :=
  OrderedDivision.fromPartition_first hab hπ_part

/-- The ordered tagged division associated to a tagged partition ends at the right endpoint. -/
theorem toTaggedDivision_last (π : TaggedPrepartition (Ioc a b))
    (hab : a < b) (hπ_part : π.IsPartition) :
    π.toTaggedDivision.x (Fin.last π.toTaggedDivision.N) = b :=
  OrderedDivision.fromPartition_last hab hπ_part

/-- Ordering a Henstock tagged partition and then forgetting the ordering preserves mesh size. -/
theorem toTaggedDivision_toTaggedPrepartition_mesh_size
    (π : TaggedPrepartition (Ioc a b)) (hab : a < b)
    (hπ_hen : π.IsHenstock) (hπ_part : π.IsPartition) :
    (π.toTaggedDivision.toTaggedPrepartition
      (π.toTaggedDivision_validTags hπ_hen hπ_part)
      (π.toTaggedDivision_first hab hπ_part)
      (π.toTaggedDivision_last hab hπ_part)).mesh_size = π.mesh_size := by
  rw [TaggedDivision.toTaggedPrepartition_mesh_size, mesh_size₁,
    ← OrderedDivision.fromPartition_map (π := π.toPrepartition) hπ_part,
    OrderedDivision.boxMap, Finset.sup_map]
  refine Finset.sup_congr rfl fun i _ ↦ NNReal.eq ?_
  have hmono : _root_.StrictMono (OrderedDivision.fromPartition π.toPrepartition).x :=
    OrderedDivision.fromPartition_strictMono π.toPrepartition
  exact (Ioc.len (hmono (Fin.castSucc_lt_succ (i := i)))).symm

end TaggedPrepartition

end BoxIntegral
