/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

import PiecewiseC1.Basic

/-!
# Legacy exists_subpath_partition proof

This file archives the old ordered-subdivision proof that used to be commented out in
PiecewiseC1/Basic.lean. It is intentionally not imported by the library: the active proof of
Path.IsPiecewiseC1.subpath now uses the finite-bad-set definition directly.

The code below is kept as legacy reference and may need imports/helper lemmas refreshed before it is
used again.
-/

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

namespace Path

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private lemma exists_mem_subdivision
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
  · have hpred_lt_n : k - 1 < n := by omega
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

private lemma pullback_mem_Icc_of_mem_uIcc {a b c : ℝ} (hab : a ≠ b)
    (hc : c ∈ uIcc a b) : (c - a) / (b - a) ∈ Icc (0 : ℝ) 1 := by
  rcases le_total a b with hab_le | hba_le
  · have hab_lt : a < b := lt_of_le_of_ne hab_le hab
    have hc' : c ∈ Icc a b := by simpa [uIcc, hab_le] using hc
    constructor
    · exact div_nonneg (sub_nonneg.mpr hc'.1) (sub_nonneg.mpr hab_le)
    · exact div_le_one_of_le₀ (sub_le_sub_right hc'.2 a) (sub_nonneg.mpr hab_le)
  · have hba_lt : b < a := lt_of_le_of_ne hba_le hab.symm
    have hc' : c ∈ Icc b a := by simpa [uIcc, hba_le] using hc
    constructor
    · exact div_nonneg_of_nonpos (sub_nonpos.mpr hc'.2) (sub_nonpos.mpr hba_le)
    · rw [div_le_one_of_neg (sub_neg.mpr hba_lt)]
      linarith [hc'.1]

private lemma lt_pullback_of_affine_lt_of_lt {a b c r : ℝ} (hab : a < b)
    (h : (1 - r) * a + r * b < c) : r < (c - a) / (b - a) := by
  rw [lt_div_iff₀ (sub_pos.mpr hab)]
  linarith

private lemma pullback_lt_of_lt_affine_of_lt {a b c r : ℝ} (hab : a < b)
    (h : c < (1 - r) * a + r * b) : (c - a) / (b - a) < r := by
  rw [div_lt_iff₀ (sub_pos.mpr hab)]
  linarith

private lemma le_pullback_of_affine_le_of_lt {a b c r : ℝ} (hab : a < b)
    (h : (1 - r) * a + r * b ≤ c) : r ≤ (c - a) / (b - a) := by
  rw [le_div_iff₀ (sub_pos.mpr hab)]
  linarith

private lemma pullback_le_of_le_affine_of_lt {a b c r : ℝ} (hab : a < b)
    (h : c ≤ (1 - r) * a + r * b) : (c - a) / (b - a) ≤ r := by
  rw [div_le_iff₀ (sub_pos.mpr hab)]
  linarith

private lemma pullback_lt_of_affine_lt_of_gt {a b c r : ℝ} (hba : b < a)
    (h : (1 - r) * a + r * b < c) : (c - a) / (b - a) < r := by
  rw [div_lt_iff_of_neg (sub_neg.mpr hba)]
  linarith

private lemma lt_pullback_of_lt_affine_of_gt {a b c r : ℝ} (hba : b < a)
    (h : c < (1 - r) * a + r * b) : r < (c - a) / (b - a) := by
  rw [lt_div_iff_of_neg (sub_neg.mpr hba)]
  linarith

private lemma pullback_le_of_affine_le_of_gt {a b c r : ℝ} (hba : b < a)
    (h : (1 - r) * a + r * b ≤ c) : (c - a) / (b - a) ≤ r := by
  rw [div_le_iff_of_neg (sub_neg.mpr hba)]
  linarith

private lemma le_pullback_of_le_affine_of_gt {a b c r : ℝ} (hba : b < a)
    (h : c ≤ (1 - r) * a + r * b) : r ≤ (c - a) / (b - a) := by
  rw [le_div_iff_of_neg (sub_neg.mpr hba)]
  linarith

lemma exists_subpath_partition
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (γ : Path x y) (s t : I)
    (n : ℕ) (hn : 0 < n)
    (ts : Fin (n + 1) → ℝ)
    (hts0 : ts 0 = 0)
    (hts1 : ts ⟨n, Nat.lt_succ_self n⟩ = 1)
    (_hts01 : ∀ i : Fin (n + 1), 0 ≤ ts i ∧ ts i ≤ 1)
    (hts_mono : ∀ i : Fin n, ts i.castSucc < ts i.succ)
    (hγ_smooth :
      ∀ i : Fin n,
        ContDiffOn ℝ 1 (⇑γ.extend) (Icc (ts i.castSucc) (ts i.succ))) :
    ∃ m,
      0 < m ∧
        ∃ us : Fin (m + 1) → ℝ,
          us 0 = 0 ∧
            us ⟨m, Nat.lt_succ_self m⟩ = 1 ∧
              (∀ i : Fin (m + 1), 0 ≤ us i ∧ us i ≤ 1) ∧
                (∀ i : Fin m, us i.castSucc < us i.succ) ∧
                  ∀ i : Fin m,
                    ContDiffOn ℝ 1
                      (⇑(γ.subpath s t).extend)
                      (Icc (us i.castSucc) (us i.succ)) := by
  by_cases hst : s = t
  · refine ⟨1, by norm_num, fun i : Fin 2 => (i : ℝ), ?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · intro i
      fin_cases i <;> norm_num
    · intro i
      fin_cases i
      norm_num
    · intro i
      fin_cases i
      refine (contDiffOn_const (c := γ s)).congr ?_
      intro r hr
      have hr01 : r ∈ Icc (0 : ℝ) 1 := by simpa using hr
      rw [Path.extend_apply _ hr01]
      simp [Path.subpath, hst]
  classical
  let pullback : ℝ → ℝ := fun τ => (τ - (s : ℝ)) / ((t : ℝ) - (s : ℝ))
  let oldBreaks : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun i => ts i ∈ uIcc (s : ℝ) (t : ℝ)
  let breaks : Finset ℝ := insert 0 (insert 1 (oldBreaks.image fun i => pullback (ts i)))
  have hst_real : (s : ℝ) ≠ (t : ℝ) := by
    intro h
    exact hst (Subtype.ext h)
  have hbreaks_mem : ∀ u ∈ breaks, u ∈ Icc (0 : ℝ) 1 := by
    intro u hu
    simp only [breaks, Finset.mem_insert, Finset.mem_image] at hu
    rcases hu with rfl | rfl | ⟨i, hi, rfl⟩
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact pullback_mem_Icc_of_mem_uIcc hst_real (by
        simpa [oldBreaks] using (Finset.mem_filter.mp hi).2)
  have h0mem : (0 : ℝ) ∈ breaks := by simp [breaks]
  have h1mem : (1 : ℝ) ∈ breaks := by simp [breaks]
  have hbreaks_nonempty : breaks.Nonempty := ⟨0, h0mem⟩
  have hmin : breaks.min' hbreaks_nonempty = (0 : ℝ) := by
    apply le_antisymm
    · exact breaks.min'_le _ h0mem
    · exact (hbreaks_mem _ (breaks.min'_mem _)).1
  have hmax : breaks.max' hbreaks_nonempty = (1 : ℝ) := by
    apply le_antisymm
    · exact (hbreaks_mem _ (breaks.max'_mem _)).2
    · exact breaks.le_max' _ h1mem
  have hpair_subset : ({0, 1} : Finset ℝ) ⊆ breaks := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact h0mem
    · exact h1mem
  have hcard_two : 2 ≤ breaks.card := by
    have hcard := Finset.card_le_card hpair_subset
    simpa using hcard
  let m : ℕ := breaks.card - 1
  have hm_pos : 0 < m := by
    dsimp [m]
    omega
  have hm_succ : m + 1 = breaks.card := by
    dsimp [m]
    omega
  let idx : Fin (m + 1) → Fin breaks.card := fun i => Fin.cast hm_succ i
  let us : Fin (m + 1) → ℝ := fun i => breaks.orderEmbOfFin rfl (idx i)
  refine ⟨m, hm_pos, us, ?_, ?_, ?_, ?_, ?_⟩
  · have hk_pos : 0 < breaks.card := by omega
    simpa [us, idx, hmin] using
      (Finset.orderEmbOfFin_zero (s := breaks) rfl hk_pos)
  · have hk_pos : 0 < breaks.card := by omega
    have hlast :
        idx ⟨m, Nat.lt_succ_self m⟩ =
          ⟨breaks.card - 1, Nat.sub_lt hk_pos (Nat.succ_pos 0)⟩ := by
      ext
      simp [idx, m]
    change breaks.orderEmbOfFin rfl (idx ⟨m, Nat.lt_succ_self m⟩) = 1
    rw [hlast]
    simpa [hmax] using
      (Finset.orderEmbOfFin_last (s := breaks) rfl hk_pos)
  · intro i
    exact hbreaks_mem _ (Finset.orderEmbOfFin_mem breaks rfl (idx i))
  · intro i
    exact (breaks.orderEmbOfFin rfl).strictMono (by
      simp [idx])
  · intro i
    let ρ : ℝ → ℝ := fun r => (1 - r) * (s : ℝ) + r * (t : ℝ)
    rcases (show ∃ j : Fin n,
        MapsTo ρ (Icc (us i.castSucc) (us i.succ))
          (Icc (ts j.castSucc) (ts j.succ)) from by
      have hno_break : ∀ z ∈ breaks, us i.castSucc < z → z < us i.succ → False := by
        intro z hz hleft hright
        have hzrange : z ∈ Set.range (breaks.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hz
        rcases hzrange with ⟨k, rfl⟩
        have hk_left : idx i.castSucc < k := by
          exact (breaks.orderEmbOfFin rfl).lt_iff_lt.mp (by simpa [us] using hleft)
        have hk_right : k < idx i.succ := by
          exact (breaks.orderEmbOfFin rfl).lt_iff_lt.mp (by simpa [us] using hright)
        have hk_left_nat : (idx i.castSucc : ℕ) < k := hk_left
        have hk_right_nat : (k : ℕ) < idx i.succ := hk_right
        simp [idx] at hk_left_nat hk_right_nat
        omega
      let q : ℝ := (us i.castSucc + us i.succ) / 2
      have hstep : us i.castSucc < us i.succ := by
        exact (breaks.orderEmbOfFin rfl).strictMono (by simp [idx])
      have hq_mem : q ∈ Icc (us i.castSucc) (us i.succ) := by
        constructor <;> dsimp [q] <;> linarith
      have hq_left_lt : us i.castSucc < q := by
        dsimp [q]
        linarith
      have hq_lt_right : q < us i.succ := by
        dsimp [q]
        linarith
      have hleft01 : us i.castSucc ∈ Icc (0 : ℝ) 1 :=
        hbreaks_mem _ (Finset.orderEmbOfFin_mem breaks rfl (idx i.castSucc))
      have hright01 : us i.succ ∈ Icc (0 : ℝ) 1 :=
        hbreaks_mem _ (Finset.orderEmbOfFin_mem breaks rfl (idx i.succ))
      have hq01 : q ∈ Icc (0 : ℝ) 1 :=
        ⟨hleft01.1.trans hq_mem.1, hq_mem.2.trans hright01.2⟩
      have hρq01 : ρ q ∈ Icc (0 : ℝ) 1 := by
        dsimp [ρ]
        constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, hq01.1, hq01.2]
      rcases exists_mem_subdivision hn hts0 hts1 hts_mono hρq01 with ⟨j, hqj⟩
      refine ⟨j, ?_⟩
      intro r hr
      have hr01 : r ∈ Icc (0 : ℝ) 1 :=
        ⟨hleft01.1.trans hr.1, hr.2.trans hright01.2⟩
      have hρr01 : ρ r ∈ Icc (0 : ℝ) 1 := by
        dsimp [ρ]
        constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, hr01.1, hr01.2]
      have hρr_u : ρ r ∈ uIcc (s : ℝ) (t : ℝ) := by
        rcases le_total (s : ℝ) t with hst_le | hts_le
        · have : ρ r ∈ Icc (s : ℝ) t := by
            dsimp [ρ]
            constructor <;> nlinarith [hst_le, hr01.1, hr01.2]
          simpa [uIcc, hst_le] using this
        · have : ρ r ∈ Icc (t : ℝ) s := by
            dsimp [ρ]
            constructor <;> nlinarith [hts_le, hr01.1, hr01.2]
          simpa [uIcc, hts_le] using this
      have hρq_u : ρ q ∈ uIcc (s : ℝ) (t : ℝ) := by
        rcases le_total (s : ℝ) t with hst_le | hts_le
        · have : ρ q ∈ Icc (s : ℝ) t := by
            dsimp [ρ]
            constructor <;> nlinarith [hst_le, hq01.1, hq01.2]
          simpa [uIcc, hst_le] using this
        · have : ρ q ∈ Icc (t : ℝ) s := by
            dsimp [ρ]
            constructor <;> nlinarith [hts_le, hq01.1, hq01.2]
          simpa [uIcc, hts_le] using this
      constructor
      · by_contra hbad
        have hlt : ρ r < ts j.castSucc := lt_of_not_ge hbad
        have hboundary_u : ts j.castSucc ∈ uIcc (s : ℝ) (t : ℝ) := by
          rcases le_total (s : ℝ) t with hst_le | hts_le
          · have hru : ρ r ∈ Icc (s : ℝ) t := by simpa [uIcc, hst_le] using hρr_u
            have hqu : ρ q ∈ Icc (s : ℝ) t := by simpa [uIcc, hst_le] using hρq_u
            have : ts j.castSucc ∈ Icc (s : ℝ) t := by
              constructor <;> linarith [hru.1, hqu.2, hlt, hqj.1]
            simpa [uIcc, hst_le] using this
          · have hru : ρ r ∈ Icc (t : ℝ) s := by simpa [uIcc, hts_le] using hρr_u
            have hqu : ρ q ∈ Icc (t : ℝ) s := by simpa [uIcc, hts_le] using hρq_u
            have : ts j.castSucc ∈ Icc (t : ℝ) s := by
              constructor <;> linarith [hru.1, hqu.2, hlt, hqj.1]
            simpa [uIcc, hts_le] using this
        let z : ℝ := pullback (ts j.castSucc)
        have hzbreak : z ∈ breaks := by
          dsimp [z]
          simp only [breaks, Finset.mem_insert, Finset.mem_image]
          right; right
          refine ⟨j.castSucc, ?_, rfl⟩
          simp [oldBreaks, hboundary_u]
        have hz_between_left : us i.castSucc < z := by
          rcases lt_or_gt_of_ne hst_real with hst_lt | hts_lt
          · have hr_lt_z : r < z := by
              dsimp [z, pullback]
              exact lt_pullback_of_affine_lt_of_lt hst_lt (by simpa [ρ] using hlt)
            exact lt_of_le_of_lt hr.1 hr_lt_z
          · have hz_le_r : z < r := by
              dsimp [z, pullback]
              exact pullback_lt_of_affine_lt_of_gt hts_lt (by simpa [ρ] using hlt)
            have hq_le_z : q ≤ z := by
              dsimp [z, pullback]
              exact le_pullback_of_le_affine_of_gt hts_lt (by simpa [ρ] using hqj.1)
            exact lt_of_lt_of_le hq_left_lt hq_le_z
        have hz_between_right : z < us i.succ := by
          rcases lt_or_gt_of_ne hst_real with hst_lt | hts_lt
          · have hz_le_q : z ≤ q := by
              dsimp [z, pullback]
              exact pullback_le_of_le_affine_of_lt hst_lt (by simpa [ρ] using hqj.1)
            exact lt_of_le_of_lt hz_le_q hq_lt_right
          · have hz_lt_r : z < r := by
              dsimp [z, pullback]
              exact pullback_lt_of_affine_lt_of_gt hts_lt (by simpa [ρ] using hlt)
            exact lt_of_lt_of_le hz_lt_r hr.2
        exact hno_break z hzbreak hz_between_left hz_between_right
      · by_contra hbad
        have hlt : ts j.succ < ρ r := lt_of_not_ge hbad
        have hboundary_u : ts j.succ ∈ uIcc (s : ℝ) (t : ℝ) := by
          rcases le_total (s : ℝ) t with hst_le | hts_le
          · have hru : ρ r ∈ Icc (s : ℝ) t := by simpa [uIcc, hst_le] using hρr_u
            have hqu : ρ q ∈ Icc (s : ℝ) t := by simpa [uIcc, hst_le] using hρq_u
            have : ts j.succ ∈ Icc (s : ℝ) t := by
              constructor <;> linarith [hqu.1, hru.2, hlt, hqj.2]
            simpa [uIcc, hst_le] using this
          · have hru : ρ r ∈ Icc (t : ℝ) s := by simpa [uIcc, hts_le] using hρr_u
            have hqu : ρ q ∈ Icc (t : ℝ) s := by simpa [uIcc, hts_le] using hρq_u
            have : ts j.succ ∈ Icc (t : ℝ) s := by
              constructor <;> linarith [hqu.1, hru.2, hlt, hqj.2]
            simpa [uIcc, hts_le] using this
        let z : ℝ := pullback (ts j.succ)
        have hzbreak : z ∈ breaks := by
          dsimp [z]
          simp only [breaks, Finset.mem_insert, Finset.mem_image]
          right; right
          refine ⟨j.succ, ?_, rfl⟩
          simp [oldBreaks, hboundary_u]
        have hz_between_left : us i.castSucc < z := by
          rcases lt_or_gt_of_ne hst_real with hst_lt | hts_lt
          · have hq_le_z : q ≤ z := by
              dsimp [z, pullback]
              exact le_pullback_of_affine_le_of_lt hst_lt (by simpa [ρ] using hqj.2)
            exact lt_of_lt_of_le hq_left_lt hq_le_z
          · have hr_lt_z : r < z := by
              dsimp [z, pullback]
              exact lt_pullback_of_lt_affine_of_gt hts_lt (by simpa [ρ] using hlt)
            exact lt_of_le_of_lt hr.1 hr_lt_z
        have hz_between_right : z < us i.succ := by
          rcases lt_or_gt_of_ne hst_real with hst_lt | hts_lt
          · have hz_lt_r : z < r := by
              dsimp [z, pullback]
              exact pullback_lt_of_lt_affine_of_lt hst_lt (by simpa [ρ] using hlt)
            exact lt_of_lt_of_le hz_lt_r hr.2
          · have hz_le_q : z ≤ q := by
              dsimp [z, pullback]
              exact pullback_le_of_affine_le_of_gt hts_lt (by simpa [ρ] using hqj.2)
            exact lt_of_le_of_lt hz_le_q hq_lt_right
        exact hno_break z hzbreak hz_between_left hz_between_right) with ⟨j, hmaps⟩
    have hρ : ContDiffOn ℝ 1 ρ (Icc (us i.castSucc) (us i.succ)) := by
      dsimp [ρ]
      fun_prop
    have hcomp : ContDiffOn ℝ 1 ((⇑γ.extend) ∘ ρ)
        (Icc (us i.castSucc) (us i.succ)) :=
      (hγ_smooth j).comp hρ hmaps
    refine hcomp.congr ?_
    intro r hr
    have hleft01 : us i.castSucc ∈ Icc (0 : ℝ) 1 :=
      hbreaks_mem _ (Finset.orderEmbOfFin_mem breaks rfl (idx i.castSucc))
    have hright01 : us i.succ ∈ Icc (0 : ℝ) 1 :=
      hbreaks_mem _ (Finset.orderEmbOfFin_mem breaks rfl (idx i.succ))
    have hr01 : r ∈ Icc (0 : ℝ) 1 :=
      ⟨hleft01.1.trans hr.1, hr.2.trans hright01.2⟩
    have hρ01 : ρ r ∈ Icc (0 : ℝ) 1 := by
      dsimp [ρ]
      constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, hr01.1, hr01.2]
    rw [Path.extend_apply _ hr01]
    change (γ.subpath s t) ⟨r, hr01⟩ = γ.extend (ρ r)
    rw [Path.extend_apply γ hρ01]
    simp [Path.subpath, ρ, Set.Icc.convexCombo]

end Path
