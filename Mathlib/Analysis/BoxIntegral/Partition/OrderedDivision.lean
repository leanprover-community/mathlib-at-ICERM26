/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Box.Ioc
public import Mathlib.Analysis.BoxIntegral.Partition.Basic

/-! # Ordered divisions of intervals

This file defines ordered one-dimensional divisions and their canonical prepartitions of
`BoxIntegral.Ioc a b`.
-/

@[expose] public section

open scoped BigOperators

namespace BoxIntegral

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


theorem box_injective (π : OrderedDivision) (hπ : π.StrictMono) :
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
    (π : OrderedDivision) (hπ : π.StrictMono)
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
  have h0last : (0 : Fin (π.N + 1)) < Fin.last π.N := by
    rw [Fin.lt_def]
    simpa using hN
  have hab : a < b := by
    rw [← ha, ← hb]
    exact hπ h0last
  have hy' := (mem_Ioc hab y).1 hy
  let P : ℕ → Prop := fun k ↦ ∃ hk : k < π.N + 1, y 0 ≤ π.x ⟨k, hk⟩
  have hP : ∃ k, P k := by
    refine ⟨π.N, ?_, ?_⟩
    · omega
    · have hlast : (⟨π.N, by omega⟩ : Fin (π.N + 1)) = Fin.last π.N := by
        ext
        simp
      simpa [hb, hlast] using hy'.2
  let m := Nat.find hP
  have hmP : P m := Nat.find_spec hP
  rcases hmP with ⟨hm_lt, hm_le⟩
  have hm_pos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    have hidx : (⟨m, hm_lt⟩ : Fin (π.N + 1)) = 0 := by
      ext
      exact hm0
    have : y 0 ≤ a := by simpa [ha, hidx] using hm_le
    exact not_lt_of_ge this hy'.1
  let i : Fin π.N := ⟨m - 1, by omega⟩
  refine ⟨π.box i, ?_, ?_⟩
  · change π.box i ∈ (π.toPrepartition hπ ha hb).boxes
    unfold toPrepartition boxMap
    simp
  · rw [box]
    refine (mem_Ioc (hπ i.castSucc_lt_succ) y).2 ?_
    constructor
    · have hprev_not : ¬ y 0 ≤ π.x i.castSucc := by
        intro hprev
        have hlt : (i : ℕ) < m := by
          dsimp [i]
          omega
        exact Nat.find_min hP hlt ⟨i.2.trans (by omega), hprev⟩
      exact lt_of_not_ge hprev_not
    · have hs : i.succ = (⟨m, hm_lt⟩ : Fin (π.N + 1)) := by
        ext
        dsimp [i]
        omega
      simpa [hs] using hm_le

noncomputable def fromPartition {a b : ℝ}
    {π : Prepartition (Ioc a b)} (hπ : π.IsPartition) :
    OrderedDivision := by sorry

theorem fromPartition_strictMono {a b : ℝ}
    {π : Prepartition (Ioc a b)} (hπ : π.IsPartition) :
    (fromPartition hπ).StrictMono := by sorry

theorem fromPartition_map {a b : ℝ}
    {π : Prepartition (Ioc a b)} (hπ : π.IsPartition):
    boxMap (fromPartition_strictMono hπ)  = π.boxes := by sorry


end OrderedDivision

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

end TaggedDivision

end BoxIntegral
