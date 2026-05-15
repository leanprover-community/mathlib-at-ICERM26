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

/-- The prepartition of `Ioc a b` associated to an ordered division with endpoints `a` and `b`. -/
noncomputable def toPrepartition {a b : ℝ}
    (π : OrderedDivision) (hπ : π.StrictMono)
    (ha : π.x 0 = a) (hb : π.x (Fin.last π.N) = b) :
    Prepartition (Ioc a b) where
  boxes := (Finset.univ : Finset (Fin π.N)).map ⟨π.box, π.box_injective hπ⟩
  le_of_mem' := by
    intro J hJ
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
    dsimp [toPrepartition]
    rw [Finset.mem_map]
    exact ⟨i, Finset.mem_univ _, rfl⟩
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

end OrderedDivision

end BoxIntegral
