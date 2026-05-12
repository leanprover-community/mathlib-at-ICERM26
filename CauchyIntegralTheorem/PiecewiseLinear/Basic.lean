/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module


public import CurveIntegral.PathReparam

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

namespace Path

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ContinuousOn.finset_iUnion_of_isClosed
    {α β ι : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (S : Finset ι) (s : ι → Set α)
    (hf : ∀ i ∈ S, ContinuousOn f (s i))
    (hs : ∀ i ∈ S, IsClosed (s i)) :
    ContinuousOn f (⋃ i ∈ S, s i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, continuousOn_empty]
  | insert a S ha ih =>
      have hfa : ContinuousOn f (s a) := hf a (by simp)
      have hsa : IsClosed (s a) := hs a (by simp)

      have hfS : ContinuousOn f (⋃ i ∈ S, s i) := by
        exact ih
          (fun i hi => hf i (by simp [hi]))
          (fun i hi => hs i (by simp [hi]))

      have hsS : IsClosed (⋃ i ∈ S, s i) := by
        exact isClosed_biUnion_finset fun i hi => hs i (by simp [hi])

      rw [Finset.set_biUnion_insert]
      exact hfa.union_of_isClosed hfS hsa hsS


/-- The path obtained by linearly interpolating through a finite list of points, using equal
subintervals of `[0, 1]`.

On the interval `[i / N, (i + 1) / N]`, this path is the straight segment from `p i` to
`p (i + 1)`. -/
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

theorem piecewiseLinearInterpolation_isPiecewiseLinear {N : ℕ} (p : Fin (N + 1) → E)
    (hpos : 0 < N) {x y : E} (h0 : p 0 = x) (hN : p (Fin.last N) = y) :
    (piecewiseLinearInterpolation hpos p h0 hN).IsPiecewiseLinear := by
  exact ⟨N, hpos, p, h0, hN, rfl⟩

/-- Every path in a real normed vector space can be uniformly approximated by piecewise linear
paths with the same endpoints. -/

theorem exists_isPiecewiseLinear_forall_dist_lt {x y : E} (γ : Path x y) :
    ∀ ε > 0, ∃ γ' : Path x y, γ'.IsPiecewiseLinear ∧ ∀ t : I, dist (γ t) (γ' t) < ε := by
  intro ε hε
  let ε' : ℝ := ε / 2
  have hε' : 0 < ε' := by positivity
  have hγuc : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  rcases Metric.uniformContinuous_iff.mp hγuc ε' hε' with ⟨δ, hδpos, hδ⟩

  rcases exists_nat_one_div_lt hδpos with ⟨n, hn⟩
  let N : ℕ := n + 1
  have hpos : 0 < N := Nat.succ_pos n
  have hstep : (1 : ℝ) / N < δ := by
    simpa [N, Nat.cast_add, Nat.cast_one] using hn

  let grid : Fin (N + 1) → I := fun i => ⟨i / N, by
    simp
    constructor
    · positivity
    · exact div_le_one_of_le₀ (by exact_mod_cast Nat.lt_succ_iff.mp i.isLt) (by positivity)⟩

  let pts : Fin (N + 1) → E := fun i => γ (grid i)

  have h0 : pts 0 = x := by
    simp [pts, grid]

  have hN : pts ⟨N, by omega⟩ = y := by
    simp [pts, grid]

  let γ' : Path x y := piecewiseLinearInterpolation hpos pts h0 (by simpa using hN)

  refine ⟨γ', ?_, ?_⟩
  · exact piecewiseLinearInterpolation_isPiecewiseLinear pts hpos h0 (by simpa using hN)
  · intro t
    have : ∃ i : Fin N, grid i.castSucc ≤ t ∧ t ≤ grid (i.succ) := by
      by_cases ht : t = 1
      · use Fin.last (N - 1)
        simp [grid]
        rw [ht]
        constructor
        · exact unitInterval.le_one'
        · apply le_of_eq
          grind
      · have ht : (t : ℝ) < 1 := by
          exact lt_of_le_of_ne t.2.2 (by
            intro h
            exact ht (Subtype.ext h))
        use ⟨Nat.floor ((N : ℝ) * (t : ℝ)), ?_⟩
        simp [grid]
        constructor
        · have hfloor : (Nat.floor ((N : ℝ) * (t : ℝ)) : ℝ) ≤ (N : ℝ) * (t : ℝ) := by
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
            simpa using mul_lt_mul_of_pos_left ht hNpos
          exact (Nat.floor_lt (mul_nonneg (le_of_lt hNpos) t.2.1)).2 hmul
    obtain ⟨i, hleft, hright⟩ := this
    have hdist_left : dist (grid i.castSucc) t < δ := by
      have hdist_le : dist (grid i.castSucc) t ≤ (1 : ℝ) / N := by
        rw [dist_comm, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
        · change (t : ℝ) - ((i : ℝ) / (N : ℝ)) ≤ (1 : ℝ) / (N : ℝ)
          have hright' : (t : ℝ) ≤ ((i : ℝ) + 1) / (N : ℝ) := by
            simpa [grid, Nat.cast_add, Nat.cast_one] using hright
          have hright'' : (t : ℝ) ≤ (i : ℝ) / (N : ℝ) + (1 : ℝ) / (N : ℝ) := by
            calc
              (t : ℝ) ≤ ((i : ℝ) + 1) / (N : ℝ) := hright'
              _ = (i : ℝ) / (N : ℝ) + (1 : ℝ) / (N : ℝ) := by ring
          linarith
        · exact sub_nonneg.mpr (by simpa [grid] using hleft)
      exact lt_of_le_of_lt hdist_le hstep
    have hdist_right : dist (grid i.castSucc) (grid i.succ) < δ := by
      have hdist_eq : dist (grid i.castSucc) (grid i.succ) = (1 : ℝ) / N := by
        rw [dist_comm, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
        · simp [grid, Nat.cast_add, Nat.cast_one, sub_eq_add_neg, add_div]
        · simp [grid, Nat.cast_add, Nat.cast_one]
          gcongr
          norm_num
      simpa [hdist_eq] using hstep

    have hγ_left : dist (γ t) (γ (grid i.castSucc)) < ε' := by
      exact Metric.mem_ball'.mp (hδ hdist_left)

    have hγ_right : dist (γ (grid i.castSucc)) (γ (grid i.succ)) < ε' := hδ hdist_right

    have hγγ' (i : Fin (N + 1)) : γ' (grid i) = γ (grid i) := by
      change (piecewiseLinearInterpolation hpos pts h0 (by simpa using hN)) (grid i) =
        γ (grid i)
      rw [piecewiseLinearInterpolation_apply_equalGrid]

    have hγ'_right : dist (γ' (grid i.castSucc)) (γ' t) < ε' := by
      have htmem : t ∈ Icc (equalGrid N i.castSucc) (equalGrid N i.succ) := by
        simpa [grid, equalGrid] using (show t ∈ Icc (grid i.castSucc) (grid i.succ) from
          ⟨hleft, hright⟩)
      have hγ't :
          γ' t =
            AffineMap.lineMap (pts i.castSucc) (pts i.succ) ((N : ℝ) * (t : ℝ) - i) := by
        change (piecewiseLinearInterpolation hpos pts h0 (by simpa using hN)) t =
          AffineMap.lineMap (pts i.castSucc) (pts i.succ) ((N : ℝ) * (t : ℝ) - i)
        exact piecewiseLinearInterpolation_apply_of_mem_Icc hpos pts h0 (by simpa using hN) i htmem
      have hγ'_left : γ' (grid i.castSucc) = pts i.castSucc := by
        rw [hγγ']
      have hpts_right : dist (pts i.castSucc) (pts i.succ) < ε' := by
        simpa [pts] using hγ_right
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
      have hc_nonneg : 0 ≤ (N : ℝ) * (t : ℝ) - (i : ℝ) := by
        have hleft' : ((i : ℝ) / (N : ℝ)) ≤ (t : ℝ) := by
          simpa [grid] using hleft
        have hleft'' : (i : ℝ) ≤ (N : ℝ) * (t : ℝ) :=
          (div_le_iff₀' hNpos).1 hleft'
        linarith
      have hc_le_one : (N : ℝ) * (t : ℝ) - (i : ℝ) ≤ 1 := by
        have hright' : (t : ℝ) ≤ ((i : ℝ) + 1) / (N : ℝ) := by
          simpa [grid, Nat.cast_add, Nat.cast_one] using hright
        have hright'' : (N : ℝ) * (t : ℝ) ≤ (i : ℝ) + 1 :=
          (le_div_iff₀' hNpos).1 hright'
        linarith
      have hnorm_le_one : ‖(N : ℝ) * (t : ℝ) - (i : ℝ)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
        exact hc_le_one
      rw [hγ'_left, hγ't, dist_left_lineMap]
      exact lt_of_le_of_lt
        (mul_le_of_le_one_left dist_nonneg hnorm_le_one) hpts_right

    calc
      dist (γ t) (γ' t) ≤ dist (γ t) (γ (grid i.castSucc)) + dist (γ (grid i.castSucc)) (γ' t) := by exact dist_triangle _ _ _
                      _ = dist (γ t) (γ (grid i.castSucc)) + dist (γ' (grid i.castSucc)) (γ' t) := by rw [dist_comm, hγγ']
                      _ < ε' + ε' := by refine add_lt_add_of_lt_of_lt hγ_left hγ'_right
                      _ = ε := by simp [ε']

theorem exists_isPiecewiseLinear_homotopy {x y : E} (γ γ' : Path x y) (H : Homotopy γ γ') :
  let hmap := ContinuousMap.curry H.toContinuousMap
  ∀ ε > 0, ∃ hmap' : Path (hmap 0) (hmap 1),
    hmap'.IsPiecewiseLinear ∧ ∀ t : I, dist (hmap t) (hmap' t) < ε := by
  intro hmap
  let hpath : Path (hmap 0) (hmap 1) :=
    { toFun := fun t => hmap t
      continuous_toFun := hmap.continuous
      source' := rfl
      target' := rfl }
  simpa using exists_isPiecewiseLinear_forall_dist_lt (γ := hpath)

end Path
