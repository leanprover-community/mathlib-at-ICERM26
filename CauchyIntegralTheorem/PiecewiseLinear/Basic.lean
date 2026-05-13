/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module

public import IntervalIntegral.Reparameterization
public import Topology.Union

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

namespace Path

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
public noncomputable abbrev piecewiseLinearInterpolation {N : ℕ} (hpos : 0 < N)
    (p : Fin (N + 1) → E) {x y : E} (h0 : p 0 = x) (hN : p (Fin.last N) = y) :
    Path x y :=
  let grid : Fin (N + 1) → I := equalGrid N
  let f : I → E := fun t =>
    if ht : t = 1 then y
    else
      let i : Fin N := ⟨Nat.floor ((N : ℝ) * (t : ℝ)), by
        have htlt : (t : ℝ) < 1 := by
          exact lt_of_le_of_ne t.2.2 (by
            intro h
            exact ht (Subtype.ext h))
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
        have hmul : (N : ℝ) * (t : ℝ) < (N : ℝ) := by
          simpa using mul_lt_mul_of_pos_left htlt hNpos
        exact (Nat.floor_lt (mul_nonneg (le_of_lt hNpos) t.2.1)).2 hmul⟩
      AffineMap.lineMap (p i.castSucc) (p i.succ) ((N : ℝ) * (t : ℝ) - i)
  {
  toFun := f
  continuous_toFun := by
    have hcont (i : Fin N) : ContinuousOn f (Icc (grid i.castSucc) (grid i.succ)) := by
      let g : I → E := fun t =>
        AffineMap.lineMap (p i.castSucc) (p i.succ) ((N : ℝ) * (t : ℝ) - i)
      have hg : Continuous g := by
        dsimp [g, AffineMap.lineMap]
        fun_prop
      have hright_val : f (grid i.succ) = p i.succ := by
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
        by_cases ht : grid i.succ = 1
        · have hisucc : i.succ = Fin.last N := by
            apply Fin.ext
            have hreal : ((i.val : ℝ) + 1) / (N : ℝ) = 1 := by
              simpa [grid, Nat.cast_add, Nat.cast_one] using congrArg Subtype.val ht
            have hreal' : (i.val : ℝ) + 1 = (N : ℝ) := by
              field_simp [ne_of_gt hNpos] at hreal
              linarith
            exact_mod_cast hreal'
          have htlast : grid (Fin.last N) = 1 := by simpa [hisucc] using ht
          simp [f, htlast, hN, hisucc]
        · have hmul : (N : ℝ) * (grid i.succ : ℝ) = (i.val + 1 : ℕ) := by
            simp [grid]
            field_simp [ne_of_gt hNpos]
          have hfloor : Nat.floor ((i.val : ℝ) + 1) = i.val + 1 := by
            rw [← Nat.cast_one, ← Nat.cast_add, Nat.floor_natCast]
          simp [f, ht, hmul, hfloor, AffineMap.lineMap_apply_zero]
          rfl
      have hright_formula : g (grid i.succ) = p i.succ := by
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
        have hparam : (N : ℝ) * (grid i.succ : ℝ) - (i : ℝ) = 1 := by
          simp [grid]
          field_simp [ne_of_gt hNpos]
          ring
        simp [g, hparam]
      refine hg.continuousOn.congr ?_
      intro t htcell
      by_cases hright : t = grid i.succ
      · simp [hright, hright_val, hright_formula]
      · have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
        have htlt_right : (t : ℝ) < (grid i.succ : ℝ) :=
          lt_of_le_of_ne htcell.2 (by
            intro h
            exact hright (Subtype.ext h))
        have htne1 : t ≠ 1 := by
          intro ht1
          apply hright
          apply Subtype.ext
          change (t : ℝ) = (grid i.succ : ℝ)
          rw [ht1]
          have hone_le : (1 : ℝ) ≤ (grid i.succ : ℝ) := by simpa [ht1] using htcell.2
          exact (le_antisymm (grid i.succ).2.2 hone_le).symm
        have hleft : (i.val : ℝ) ≤ (N : ℝ) * (t : ℝ) := by
          have hle : (grid i.castSucc : ℝ) ≤ (t : ℝ) := htcell.1
          have hle' : (i.val : ℝ) / (N : ℝ) ≤ (t : ℝ) := by simpa [grid] using hle
          exact (div_le_iff₀' hNpos).1 hle'
        have hright' : (N : ℝ) * (t : ℝ) < (i.val : ℝ) + 1 := by
          have hlt : (t : ℝ) < ((i.val : ℝ) + 1) / (N : ℝ) := by
            simpa [grid, Nat.cast_add, Nat.cast_one] using htlt_right
          exact (lt_div_iff₀' hNpos).1 hlt
        have hfloor : Nat.floor ((N : ℝ) * (t : ℝ)) = i.val := by
          exact Nat.floor_eq_on_Ico i.val ((N : ℝ) * (t : ℝ))
            ⟨hleft, by simpa using hright'⟩
        simp [f, g, htne1, hfloor]
        rfl

    have hcontUnion : ContinuousOn f
        (⋃ i ∈ (Finset.univ : Finset (Fin N)), Icc (grid i.castSucc) (grid i.succ)) := by
      exact ContinuousOn.finset_iUnion_of_isClosed (Finset.univ : Finset (Fin N))
        (fun i => Icc (grid i.castSucc) (grid i.succ))
        (fun i _ => hcont i)
        (fun i _ => isClosed_Icc)
    have hcover' : ∀ t : I, ∃ i : Fin N, grid i.castSucc ≤ t ∧ t ≤ grid i.succ := by
      intro t
      by_cases ht : t = 1
      · let i : Fin N := ⟨N - 1, by omega⟩
        use i
        constructor
        · rw [ht]
          exact unitInterval.le_one'
        · rw [ht]
          change (1 : ℝ) ≤ (grid i.succ : ℝ)
          have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
          have hnum : (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) := by
            exact_mod_cast Nat.sub_add_cancel hpos
          simp [grid, i, hnum]
          field_simp [ne_of_gt hNpos]
          norm_num
      · have htlt : (t : ℝ) < 1 := by
          exact lt_of_le_of_ne t.2.2 (by
            intro h
            exact ht (Subtype.ext h))
        use ⟨Nat.floor ((N : ℝ) * (t : ℝ)), ?_⟩
        simp [grid, equalGrid]
        constructor
        · have hfloor : (Nat.floor ((N : ℝ) * (t : ℝ)) : ℝ) ≤
              (N : ℝ) * (t : ℝ) := by
            apply Nat.floor_le
            apply mul_nonneg
            · exact Nat.cast_nonneg' N
            · exact t.2.1
          change ((Nat.floor ((N : ℝ) * (t : ℝ)) : ℝ) / (N : ℝ) ≤ (t : ℝ))
          apply (div_le_iff₀ (by exact_mod_cast hpos)).mpr
          simpa [mul_comm] using hfloor
        · have hfloor_lt :
              (N : ℝ) * (t : ℝ) <
                (Nat.floor ((N : ℝ) * (t : ℝ)) : ℝ) + 1 :=
            Nat.lt_floor_add_one ((N : ℝ) * (t : ℝ))
          change (t : ℝ) ≤
            ((Nat.floor ((N : ℝ) * (t : ℝ)) : ℝ) + 1) / (N : ℝ)
          apply le_of_lt
          rw [lt_div_iff₀ (by exact_mod_cast hpos)]
          simpa [mul_comm] using hfloor_lt
        · have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
          have hmul : (N : ℝ) * (t : ℝ) < (N : ℝ) := by
            simpa using mul_lt_mul_of_pos_left htlt hNpos
          exact (Nat.floor_lt (mul_nonneg (le_of_lt hNpos) t.2.1)).2 hmul
    have hcover :
        (⋃ i : Fin N, Icc (grid i.castSucc) (grid i.succ)) = Set.univ := by
      ext t
      constructor
      · intro _
        trivial
      · intro _
        rcases hcover' t with ⟨i, hi⟩
        exact mem_iUnion.2 ⟨i, hi⟩
    exact continuousOn_univ.mp (by simpa [hcover] using hcontUnion)
  source' := by
    simp [f]
    exact h0
  target' := by
    simp [f]
  }

theorem piecewiseLinearInterpolation_apply_of_mem_Icc {N : ℕ} (hpos : 0 < N)
    (p : Fin (N + 1) → E) {x y : E} (h0 : p 0 = x) (hN : p (Fin.last N) = y)
    (i : Fin N) {t : I}
    (ht : t ∈ Icc (equalGrid N i.castSucc) (equalGrid N i.succ)) :
    (piecewiseLinearInterpolation hpos p h0 hN) t =
      AffineMap.lineMap (p i.castSucc) (p i.succ) ((N : ℝ) * (t : ℝ) - i) := by
  let grid : Fin (N + 1) → I := equalGrid N
  let f : I → E := fun t =>
    if ht : t = 1 then y
    else
      let i : Fin N := ⟨Nat.floor ((N : ℝ) * (t : ℝ)), by
        have htlt : (t : ℝ) < 1 := by
          exact lt_of_le_of_ne t.2.2 (by
            intro h
            exact ht (Subtype.ext h))
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
        have hmul : (N : ℝ) * (t : ℝ) < (N : ℝ) := by
          simpa using mul_lt_mul_of_pos_left htlt hNpos
        exact (Nat.floor_lt (mul_nonneg (le_of_lt hNpos) t.2.1)).2 hmul⟩
      AffineMap.lineMap (p i.castSucc) (p i.succ) ((N : ℝ) * (t : ℝ) - i)
  change f t = AffineMap.lineMap (p i.castSucc) (p i.succ) ((N : ℝ) * (t : ℝ) - i)
  have htcell : t ∈ Icc (grid i.castSucc) (grid i.succ) := by
    simpa [grid] using ht
  by_cases hright : t = grid i.succ
  · have hright_val : f (grid i.succ) = p i.succ := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
      by_cases ht : grid i.succ = 1
      · have hisucc : i.succ = Fin.last N := by
          apply Fin.ext
          have hreal : ((i.val : ℝ) + 1) / (N : ℝ) = 1 := by
            simpa [grid, Nat.cast_add, Nat.cast_one] using congrArg Subtype.val ht
          have hreal' : (i.val : ℝ) + 1 = (N : ℝ) := by
            field_simp [ne_of_gt hNpos] at hreal
            linarith
          exact_mod_cast hreal'
        have htlast : grid (Fin.last N) = 1 := by simpa [hisucc] using ht
        simp [f, htlast, hN, hisucc]
      · have hmul : (N : ℝ) * (grid i.succ : ℝ) = (i.val + 1 : ℕ) := by
          simp [grid]
          field_simp [ne_of_gt hNpos]
        have hfloor : Nat.floor ((i.val : ℝ) + 1) = i.val + 1 := by
          rw [← Nat.cast_one, ← Nat.cast_add, Nat.floor_natCast]
        simp [f, ht, hmul, hfloor, AffineMap.lineMap_apply_zero]
        rfl
    have hright_formula :
        AffineMap.lineMap (p i.castSucc) (p i.succ)
            ((N : ℝ) * (grid i.succ : ℝ) - i) = p i.succ := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
      have hparam : (N : ℝ) * (grid i.succ : ℝ) - (i : ℝ) = 1 := by
        simp [grid]
        field_simp [ne_of_gt hNpos]
        ring
      simp [hparam]
    simp [hright, hright_val, hright_formula]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
    have htlt_right : (t : ℝ) < (grid i.succ : ℝ) :=
      lt_of_le_of_ne htcell.2 (by
        intro h
        exact hright (Subtype.ext h))
    have htne1 : t ≠ 1 := by
      intro ht1
      apply hright
      apply Subtype.ext
      change (t : ℝ) = (grid i.succ : ℝ)
      rw [ht1]
      have hone_le : (1 : ℝ) ≤ (grid i.succ : ℝ) := by simpa [ht1] using htcell.2
      exact (le_antisymm (grid i.succ).2.2 hone_le).symm
    have hleft : (i.val : ℝ) ≤ (N : ℝ) * (t : ℝ) := by
      have hle : (grid i.castSucc : ℝ) ≤ (t : ℝ) := htcell.1
      have hle' : (i.val : ℝ) / (N : ℝ) ≤ (t : ℝ) := by simpa [grid] using hle
      exact (div_le_iff₀' hNpos).1 hle'
    have hright' : (N : ℝ) * (t : ℝ) < (i.val : ℝ) + 1 := by
      have hlt : (t : ℝ) < ((i.val : ℝ) + 1) / (N : ℝ) := by
        simpa [grid, Nat.cast_add, Nat.cast_one] using htlt_right
      exact (lt_div_iff₀' hNpos).1 hlt
    have hfloor : Nat.floor ((N : ℝ) * (t : ℝ)) = i.val := by
      exact Nat.floor_eq_on_Ico i.val ((N : ℝ) * (t : ℝ))
        ⟨hleft, by simpa using hright'⟩
    simp [f, htne1, hfloor]
    rfl

theorem piecewiseLinearInterpolation_apply_equalGrid {N : ℕ} (hpos : 0 < N)
    (p : Fin (N + 1) → E) {x y : E} (h0 : p 0 = x) (hN : p (Fin.last N) = y)
    (i : Fin (N + 1)) :
    (piecewiseLinearInterpolation hpos p h0 hN) (equalGrid N i) = p i := by
  by_cases hi : i.val < N
  · let j : Fin N := ⟨i.val, hi⟩
    have hij : i = j.castSucc := by
      apply Fin.ext
      rfl
    have hmem : equalGrid N i ∈ Icc (equalGrid N j.castSucc) (equalGrid N j.succ) := by
      rw [hij]
      constructor
      · rfl
      · change (equalGrid N j.castSucc : ℝ) ≤ (equalGrid N j.succ : ℝ)
        simp [Nat.cast_add, Nat.cast_one]
        gcongr
        norm_num
    rw [piecewiseLinearInterpolation_apply_of_mem_Icc hpos p h0 hN j hmem]
    have hparam : (N : ℝ) * (equalGrid N i : ℝ) - (j : ℝ) = 0 := by
      rw [hij]
      simp
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
      field_simp [ne_of_gt hNpos]
      ring_nf
    rw [hparam, AffineMap.lineMap_apply_zero]
    simp only [hij]
  · have hiN : i = Fin.last N := by
      apply Fin.ext
      exact Nat.eq_of_lt_succ_of_not_lt i.isLt hi
    let j : Fin N := ⟨N - 1, by omega⟩
    have hsucc : j.succ = Fin.last N := by
      apply Fin.ext
      simp [j]
      omega
    have hmem : equalGrid N i ∈ Icc (equalGrid N j.castSucc) (equalGrid N j.succ) := by
      rw [hiN, ← hsucc]
      constructor
      · change (equalGrid N j.castSucc : ℝ) ≤ (equalGrid N j.succ : ℝ)
        simp [Nat.cast_add, Nat.cast_one]
        gcongr
        norm_num
      · rfl
    rw [piecewiseLinearInterpolation_apply_of_mem_Icc hpos p h0 hN j hmem]
    have hparam : (N : ℝ) * (equalGrid N i : ℝ) - (j : ℝ) = 1 := by
      rw [hiN]
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
      have hnum : (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hpos
      simp [j]
      field_simp [ne_of_gt hNpos]
      linarith
    rw [hparam, AffineMap.lineMap_apply_one]
    simp only [hsucc, hiN]

/-- Predicate saying that a path is piecewise linear in a real topological vector space.

This means that it is obtained by linearly interpolating through finitely many points. -/
public abbrev IsPiecewiseLinear {x y : E} (γ : Path x y) : Prop :=
  ∃ (N : ℕ) (hpos : 0 < N) (p : Fin (N + 1) → E) (h0 : p 0 = x)
    (hN : p (Fin.last N) = y), γ = piecewiseLinearInterpolation hpos p h0 hN

lemma piecewiseLinearInterpolation_isPiecewiseLinear {N : ℕ} (p : Fin (N + 1) → E)
    (hpos : 0 < N) {x y : E} (h0 : p 0 = x) (hN : p (Fin.last N) = y) :
    (piecewiseLinearInterpolation hpos p h0 hN).IsPiecewiseLinear := by
  exact ⟨N, hpos, p, h0, hN, rfl⟩


end Path

