/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module


public import PiecewiseLinear.PiecewiseC1

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

namespace Path

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma exists_mem_subdivision
    {n : ℕ} (hn : 0 < n) {ts : Fin (n + 1) → ℝ}
    (hts0 : ts 0 = 0)
    (hts1 : ts ⟨n, Nat.lt_succ_self n⟩ = 1)
    (hts_mono : ∀ i : Fin n, ts i.castSucc < ts i.succ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ j : Fin n, x ∈ Icc (ts j.castSucc) (ts j.succ) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ hk : k ≤ n, x ≤ ts ⟨k, Nat.lt_succ_of_le hk⟩
  have hP : ∃ k, P k := ⟨n, by simpa [P, hts1] using hx.2⟩
  let k := Nat.find hP
  have hkP : P k := Nat.find_spec hP
  rcases hkP with ⟨hkn, hxk⟩
  by_cases hk0 : k = 0
  · let j0 : Fin n := ⟨0, hn⟩
    refine ⟨j0, ?_⟩
    have hx0 : x = 0 := le_antisymm (by simpa [k, hk0, hts0] using hxk) hx.1
    constructor
    · simp [j0, hx0, hts0]
    · have h01 := hts_mono j0
      have : ts (0 : Fin (n + 1)) < ts (Fin.succ j0) := by
        simpa using h01
      simpa [j0, hx0, hts0] using this.le
  · have hkpos : 0 < k := Nat.pos_iff_ne_zero.mpr hk0
    have hpred_lt_n : k - 1 < n := by omega
    let j : Fin n := ⟨k - 1, hpred_lt_n⟩
    refine ⟨j, ?_⟩
    have hnotPpred : ¬ P (k - 1) := Nat.find_min hP (Nat.sub_one_lt hk0)
    have hpred_le : ts j.castSucc ≤ x := by
      by_contra hlt
      exact hnotPpred ⟨Nat.le_of_lt hpred_lt_n, le_of_not_ge hlt⟩
    have hsucc_eq : j.succ = (⟨k, Nat.lt_succ_of_le hkn⟩ : Fin (n + 1)) := by
      ext
      simp [j]
      omega
    exact ⟨hpred_le, by simpa [hsucc_eq] using hxk⟩

/-- Recover an ordered subdivision from the finite-bad-set definition of piecewise-`C¹`. -/
theorem IsPiecewiseC1.exists_subdivision {x y : E} {γ : Path x y}
    (hγ : γ.IsPiecewiseC1) :
    ∃ n : ℕ, ∃ _ : 0 < n, ∃ ts : Fin (n + 1) → ℝ,
      ts 0 = 0 ∧
      ts ⟨n, by omega⟩ = 1 ∧
      (∀ i : Fin (n + 1), ts i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i : Fin n, ts i.castSucc < ts i.succ) ∧
      ∀ i : Fin n,
        ContDiffOn ℝ 1 (⇑γ.extend)
          (Set.Icc (ts i.castSucc) (ts i.succ)) := by
  classical
  rcases hγ with ⟨S, hS01, hγ_smooth⟩
  let breaks : Finset ℝ := insert 0 (insert 1 S)
  have hbreaks_mem : ∀ t ∈ breaks, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    simp only [breaks, Finset.mem_insert] at ht
    rcases ht with rfl | rfl | htS
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hS01 t htS
  have h0mem : (0 : ℝ) ∈ breaks := by simp [breaks]
  have h1mem : (1 : ℝ) ∈ breaks := by simp [breaks]
  have hnonempty : breaks.Nonempty := ⟨0, h0mem⟩
  have hmin : breaks.min' hnonempty = (0 : ℝ) := by
    apply le_antisymm
    · exact breaks.min'_le _ h0mem
    · exact (hbreaks_mem _ (breaks.min'_mem _)).1
  have hmax : breaks.max' hnonempty = (1 : ℝ) := by
    apply le_antisymm
    · exact (hbreaks_mem _ (breaks.max'_mem _)).2
    · exact breaks.le_max' _ h1mem
  have hpair_subset : ({0, 1} : Finset ℝ) ⊆ breaks := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact h0mem
    · exact h1mem
  have hcard_two : 2 ≤ breaks.card := by
    have hcard := Finset.card_le_card hpair_subset
    simpa using hcard
  let n : ℕ := breaks.card - 1
  have hn : 0 < n := by
    dsimp [n]
    omega
  have hcard : n + 1 = breaks.card := by
    dsimp [n]
    omega
  let idx : Fin (n + 1) → Fin breaks.card := fun i => Fin.cast hcard i
  let ts : Fin (n + 1) → ℝ := fun i => breaks.orderEmbOfFin rfl (idx i)
  refine ⟨n, hn, ts, ?_, ?_, ?_, ?_, ?_⟩
  · have hk_pos : 0 < breaks.card := by omega
    simpa [ts, idx, hmin] using
      (Finset.orderEmbOfFin_zero (s := breaks) rfl hk_pos)
  · have hk_pos : 0 < breaks.card := by omega
    have hlast :
        idx ⟨n, Nat.lt_succ_self n⟩ =
          ⟨breaks.card - 1, Nat.sub_lt hk_pos (Nat.succ_pos 0)⟩ := by
      ext
      simp [idx, n]
    change breaks.orderEmbOfFin rfl (idx ⟨n, Nat.lt_succ_self n⟩) = 1
    rw [hlast]
    simpa [hmax] using
      (Finset.orderEmbOfFin_last (s := breaks) rfl hk_pos)
  · intro i
    exact hbreaks_mem _ (Finset.orderEmbOfFin_mem breaks rfl (idx i))
  · intro i
    exact (breaks.orderEmbOfFin rfl).strictMono (by simp [idx])
  · intro i
    have hdisj : Disjoint (Ioo (ts i.castSucc) (ts i.succ)) (↑S : Set ℝ) := by
      rw [Set.disjoint_left]
      intro z hzI hzS
      have hzbreak : z ∈ breaks := by
        simp [breaks]
        exact Or.inr (Or.inr (by simpa using hzS))
      have hzrange : z ∈ Set.range (breaks.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hzbreak
      rcases hzrange with ⟨k, rfl⟩
      have hk_left : idx i.castSucc < k := by
        exact (breaks.orderEmbOfFin rfl).lt_iff_lt.mp (by simpa [ts] using hzI.1)
      have hk_right : k < idx i.succ := by
        exact (breaks.orderEmbOfFin rfl).lt_iff_lt.mp (by simpa [ts] using hzI.2)
      have hk_left_nat : (idx i.castSucc : ℕ) < k := hk_left
      have hk_right_nat : (k : ℕ) < idx i.succ := hk_right
      simp [idx] at hk_left_nat hk_right_nat
      omega
    exact hγ_smooth (ts i.castSucc) (ts i.succ)
      (hbreaks_mem _ (Finset.orderEmbOfFin_mem breaks rfl (idx i.castSucc)))
      (hbreaks_mem _ (Finset.orderEmbOfFin_mem breaks rfl (idx i.succ)))
      hdisj

/-- Build the finite-bad-set definition from an ordered subdivision. -/
theorem isPiecewiseC1_of_subdivision {x y : E} {γ : Path x y}
    {n : ℕ} (hn : 0 < n) (ts : Fin (n + 1) → ℝ)
    (hts0 : ts 0 = 0)
    (hts1 : ts ⟨n, Nat.lt_succ_self n⟩ = 1)
    (hts01 : ∀ i : Fin (n + 1), ts i ∈ Set.Icc (0 : ℝ) 1)
    (hts_mono : ∀ i : Fin n, ts i.castSucc < ts i.succ)
    (hγ_smooth : ∀ i : Fin n,
      ContDiffOn ℝ 1 (⇑γ.extend)
        (Set.Icc (ts i.castSucc) (ts i.succ))) :
    γ.IsPiecewiseC1 := by
  classical
  let S : Finset ℝ := Finset.univ.image ts
  refine ⟨S, ?_, ?_⟩
  · intro r hr
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hr
    rcases hr with ⟨i, rfl⟩
    exact hts01 i
  · intro a b ha hb hdisj
    by_cases hab : a ≤ b
    · by_cases hlt : a < b
      · let q : ℝ := (a + b) / 2
        have hq_mem : q ∈ Icc (0 : ℝ) 1 := by
          constructor
          · dsimp [q]
            nlinarith [ha.1, hb.1]
          · dsimp [q]
            nlinarith [ha.2, hb.2]
        have ha_lt_q : a < q := by
          dsimp [q]
          linarith
        have hq_lt_b : q < b := by
          dsimp [q]
          linarith
        rcases exists_mem_subdivision hn hts0 hts1 hts_mono hq_mem with ⟨j, hqj⟩
        have hleft_mem : ts j.castSucc ∈ (↑S : Set ℝ) := by
          simp [S]
        have hright_mem : ts j.succ ∈ (↑S : Set ℝ) := by
          simp [S]
        have hleft_le_a : ts j.castSucc ≤ a := by
          by_contra hnot
          have ha_lt_left : a < ts j.castSucc := lt_of_not_ge hnot
          have hleft_lt_b : ts j.castSucc < b := lt_of_le_of_lt hqj.1 hq_lt_b
          exact (Set.disjoint_left.mp hdisj) ⟨ha_lt_left, hleft_lt_b⟩ hleft_mem
        have hb_le_right : b ≤ ts j.succ := by
          by_contra hnot
          have hright_lt_b : ts j.succ < b := lt_of_not_ge hnot
          have ha_lt_right : a < ts j.succ := lt_of_lt_of_le ha_lt_q hqj.2
          exact (Set.disjoint_left.mp hdisj) ⟨ha_lt_right, hright_lt_b⟩ hright_mem
        exact (hγ_smooth j).mono fun r hr => ⟨hleft_le_a.trans hr.1, hr.2.trans hb_le_right⟩
      · have hba : b ≤ a := le_of_not_gt hlt
        have hab_eq : a = b := le_antisymm hab hba
        rcases exists_mem_subdivision hn hts0 hts1 hts_mono ha with ⟨j, haj⟩
        exact (hγ_smooth j).mono fun r hr => by
          have hr_eq : r = a := le_antisymm (by simpa [← hab_eq] using hr.2) hr.1
          rw [hr_eq]
          exact haj
    · have hba : b < a := lt_of_not_ge hab
      exact (hγ_smooth ⟨0, hn⟩).mono fun r hr => by
        exact False.elim (not_le_of_gt hba (hr.1.trans hr.2))

theorem IsPiecewiseLinear.isPiecewiseC1 {x y : E} {γ : Path x y}
    (hγ : γ.IsPiecewiseLinear) : γ.IsPiecewiseC1 := by
  rcases (show ∃ (N : ℕ) (hpos : 0 < N) (p : Fin (N + 1) → E) (h0 : p 0 = x)
    (hN : p (Fin.last N) = y), γ = piecewiseLinearInterpolation hpos p h0 hN from hγ) with
    ⟨N, hpos, p, h0, hN, rfl⟩
  refine isPiecewiseC1_of_subdivision (n := N) hpos (fun i => (i : ℝ) / N)
    ?_ ?_ ?_ ?_ ?_
  · simp
  · change (N : ℝ) / (N : ℝ) = 1
    exact div_self (by exact_mod_cast hpos.ne')
  · intro i
    constructor
    · positivity
    · exact div_le_one_of_le₀ (by exact_mod_cast Nat.lt_succ_iff.mp i.isLt) (by positivity)
  · intro i
    change ((i.castSucc : Fin (N + 1)) : ℝ) / (N : ℝ) <
      ((i.succ : Fin (N + 1)) : ℝ) / (N : ℝ)
    simp [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    gcongr
    norm_num
  · intro i
    let φ : ℝ → E := fun t =>
      AffineMap.lineMap (p i.castSucc) (p i.succ) ((N : ℝ) * t - i)
    have hφ : ContDiff ℝ 1 φ := by
      dsimp [φ, AffineMap.lineMap]
      fun_prop
    refine hφ.contDiffOn.congr ?_
    intro t ht
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      have hleft0 : (0 : ℝ) ≤ (fun j : Fin (N + 1) => (j : ℝ) / N) i.castSucc := by
        positivity
      have hright1 : (fun j : Fin (N + 1) => (j : ℝ) / N) i.succ ≤ 1 := by
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
        change ((i.succ : Fin (N + 1)) : ℝ) / (N : ℝ) ≤ 1
        rw [div_le_one₀ hNpos]
        exact_mod_cast Nat.succ_le_iff.mpr i.isLt
      exact ⟨hleft0.trans ht.1, ht.2.trans hright1⟩
    have htI : (⟨t, ht01⟩ : I) ∈
        Set.Icc (equalGrid N i.castSucc) (equalGrid N i.succ) := by
      constructor
      · simpa [equalGrid] using ht.1
      · simpa [equalGrid] using ht.2
    have happly :=
      piecewiseLinearInterpolation_apply_of_mem_Icc hpos p h0 hN i htI
    rw [Path.extend_apply _ ht01]
    exact happly

end Path
