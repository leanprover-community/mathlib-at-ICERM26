/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module

public import PiecewiseLinear.Basic

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

namespace Path

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
public noncomputable abbrev IsPiecewiseC1 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E} (γ : Path a b) : Prop :=
  ∃ S : Finset ℝ,
    (∀ t ∈ S, t ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 →
      b ∈ Set.Icc (0 : ℝ) 1 →
      Disjoint (Set.Ioo a b) (↑S : Set ℝ) →
        ContDiffOn ℝ 1 (⇑γ.extend) (Set.Icc a b)

/-- A globally `C¹` path is piecewise-`C¹`, using the one-piece subdivision. -/
lemma isPiecewiseC1_of_contDiffOn_extend {x y : E} {γ : Path x y}
    (hγ : ContDiffOn ℝ 1 (⇑γ.extend) (Set.Icc (0 : ℝ) 1)) :
    γ.IsPiecewiseC1 := by
  refine ⟨∅, ?_, ?_⟩
  · simp
  · intro a b ha hb _hdisj
    exact hγ.mono fun r hr => ⟨ha.1.trans hr.1, hr.2.trans hb.2⟩

lemma IsPiecewiseC1.cast {x y x' y' : E} {γ : Path x y}
    (hγ : γ.IsPiecewiseC1) (hx : x' = x) (hy : y' = y) :
    (γ.cast hx hy).IsPiecewiseC1 := by
  rcases hγ with ⟨S, hS, hγS⟩
  refine ⟨S, hS, ?_⟩
  intro a b ha hb hdisj
  simpa [Path.extend_cast] using hγS a b ha hb hdisj

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

private lemma pullback_lt_of_affine_lt_of_gt {a b c r : ℝ} (hba : b < a)
    (h : (1 - r) * a + r * b < c) : (c - a) / (b - a) < r := by
  rw [div_lt_iff_of_neg (sub_neg.mpr hba)]
  linarith

private lemma lt_pullback_of_lt_affine_of_gt {a b c r : ℝ} (hba : b < a)
    (h : c < (1 - r) * a + r * b) : r < (c - a) / (b - a) := by
  rw [lt_div_iff_of_neg (sub_neg.mpr hba)]
  linarith

/-- Subpaths of piecewise-`C¹` paths are piecewise-`C¹`. -/
lemma IsPiecewiseC1.subpath {x y : E} {γ : Path x y}
    (hγ : γ.IsPiecewiseC1) (s t : I) :
    (γ.subpath s t).IsPiecewiseC1 := by
  classical
  rcases hγ with ⟨S, hS01, hγ_smooth⟩
  let ρ : ℝ → ℝ := fun r => (1 - r) * (s : ℝ) + r * (t : ℝ)
  let pullback : ℝ → ℝ := fun τ => (τ - (s : ℝ)) / ((t : ℝ) - (s : ℝ))
  let S' : Finset ℝ :=
    if hst : (s : ℝ) = (t : ℝ) then ∅
    else (S.filter fun τ => τ ∈ uIcc (s : ℝ) (t : ℝ)).image pullback
  refine ⟨S', ?_, ?_⟩
  · intro r hr
    by_cases hst : (s : ℝ) = (t : ℝ)
    · simp [S', hst] at hr
    · simp only [S', hst, ↓reduceDIte, Finset.mem_image, Finset.mem_filter] at hr
      rcases hr with ⟨τ, hτ, rfl⟩
      exact pullback_mem_Icc_of_mem_uIcc hst hτ.2
  · intro a b ha hb hdisj
    by_cases hst : (s : ℝ) = (t : ℝ)
    · -- Degenerate subpaths are constant.
      let φ : ℝ → E := fun _ => γ s
      have hφ : ContDiffOn ℝ 1 φ (Icc a b) := contDiffOn_const
      refine hφ.congr ?_
      intro r hr
      have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hr.1, hr.2.trans hb.2⟩
      rw [Path.extend_apply _ hr01]
      have harg : Set.Icc.convexCombo s t ⟨r, hr01⟩ = s := by
        apply Subtype.ext
        change (1 - r) * (s : ℝ) + r * (t : ℝ) = (s : ℝ)
        rw [hst]
        ring
      simp [Path.subpath, harg, φ]
    · -- Nondegenerate subpaths are composition with the affine reparametrization `ρ`.
      -- The bad set was pulled back along `ρ`; if `(a,b)` avoids `S'`, then
      -- the image interval avoids `S`, and the defining interval condition for
      -- `γ` supplies `ContDiffOn` before composing with `ρ`.
      by_cases hab : a ≤ b
      · rcases lt_or_gt_of_ne hst with hst_lt | hts_lt
        · have hρa01 : ρ a ∈ Icc (0 : ℝ) 1 := by
            dsimp [ρ]
            constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, ha.1, ha.2]
          have hρb01 : ρ b ∈ Icc (0 : ℝ) 1 := by
            dsimp [ρ]
            constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, hb.1, hb.2]
          have hdisjγ : Disjoint (Ioo (ρ a) (ρ b)) (↑S : Set ℝ) := by
            rw [Set.disjoint_left]
            intro τ hτI hτS
            have hτ_u : τ ∈ uIcc (s : ℝ) (t : ℝ) := by
              have hρa_ge_s : (s : ℝ) ≤ ρ a := by
                dsimp [ρ]
                nlinarith [hst_lt.le, ha.1, ha.2]
              have hρb_le_t : ρ b ≤ (t : ℝ) := by
                dsimp [ρ]
                nlinarith [hst_lt.le, hb.1, hb.2]
              have : τ ∈ Icc (s : ℝ) (t : ℝ) :=
                ⟨hρa_ge_s.trans hτI.1.le, hτI.2.le.trans hρb_le_t⟩
              simpa [uIcc, hst_lt.le] using this
            have hpullI : pullback τ ∈ Ioo a b := by
              constructor
              · dsimp [pullback]
                exact lt_pullback_of_affine_lt_of_lt hst_lt (by simpa [ρ] using hτI.1)
              · dsimp [pullback]
                exact pullback_lt_of_lt_affine_of_lt hst_lt (by simpa [ρ] using hτI.2)
            have hpullS : pullback τ ∈ (↑S' : Set ℝ) := by
              simp only [S', hst, ↓reduceDIte, Finset.mem_coe, Finset.mem_image,
                Finset.mem_filter]
              exact ⟨τ, ⟨hτS, hτ_u⟩, rfl⟩
            exact (Set.disjoint_left.mp hdisj) hpullI hpullS
          have hbase := hγ_smooth (ρ a) (ρ b) hρa01 hρb01 hdisjγ
          have hρdiff : ContDiffOn ℝ 1 ρ (Icc a b) := by
            dsimp [ρ]
            fun_prop
          have hmaps : MapsTo ρ (Icc a b) (Icc (ρ a) (ρ b)) := by
            intro r hr
            dsimp [ρ]
            constructor <;> nlinarith [hst_lt.le, hr.1, hr.2]
          have hcomp : ContDiffOn ℝ 1 ((⇑γ.extend) ∘ ρ) (Icc a b) :=
            hbase.comp hρdiff hmaps
          refine hcomp.congr ?_
          intro r hr
          have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hr.1, hr.2.trans hb.2⟩
          have hρr01 : ρ r ∈ Icc (0 : ℝ) 1 := by
            dsimp [ρ]
            constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, hr01.1, hr01.2]
          rw [Path.extend_apply _ hr01]
          change (γ.subpath s t) ⟨r, hr01⟩ = γ.extend (ρ r)
          rw [Path.extend_apply γ hρr01]
          simp [Path.subpath, ρ, Set.Icc.convexCombo]
        · have hρa01 : ρ a ∈ Icc (0 : ℝ) 1 := by
            dsimp [ρ]
            constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, ha.1, ha.2]
          have hρb01 : ρ b ∈ Icc (0 : ℝ) 1 := by
            dsimp [ρ]
            constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, hb.1, hb.2]
          have hdisjγ : Disjoint (Ioo (ρ b) (ρ a)) (↑S : Set ℝ) := by
            rw [Set.disjoint_left]
            intro τ hτI hτS
            have hτ_u : τ ∈ uIcc (s : ℝ) (t : ℝ) := by
              have ht_le_ρb : (t : ℝ) ≤ ρ b := by
                dsimp [ρ]
                nlinarith [hts_lt.le, hb.1, hb.2]
              have hρa_le_s : ρ a ≤ (s : ℝ) := by
                dsimp [ρ]
                nlinarith [hts_lt.le, ha.1, ha.2]
              have : τ ∈ Icc (t : ℝ) (s : ℝ) :=
                ⟨ht_le_ρb.trans hτI.1.le, hτI.2.le.trans hρa_le_s⟩
              simpa [uIcc, hts_lt.le] using this
            have hpullI : pullback τ ∈ Ioo a b := by
              constructor
              · dsimp [pullback]
                exact lt_pullback_of_lt_affine_of_gt hts_lt (by simpa [ρ] using hτI.2)
              · dsimp [pullback]
                exact pullback_lt_of_affine_lt_of_gt hts_lt (by simpa [ρ] using hτI.1)
            have hpullS : pullback τ ∈ (↑S' : Set ℝ) := by
              simp only [S', hst, ↓reduceDIte, Finset.mem_coe, Finset.mem_image,
                Finset.mem_filter]
              exact ⟨τ, ⟨hτS, hτ_u⟩, rfl⟩
            exact (Set.disjoint_left.mp hdisj) hpullI hpullS
          have hbase := hγ_smooth (ρ b) (ρ a) hρb01 hρa01 hdisjγ
          have hρdiff : ContDiffOn ℝ 1 ρ (Icc a b) := by
            dsimp [ρ]
            fun_prop
          have hmaps : MapsTo ρ (Icc a b) (Icc (ρ b) (ρ a)) := by
            intro r hr
            dsimp [ρ]
            constructor <;> nlinarith [hts_lt.le, hr.1, hr.2]
          have hcomp : ContDiffOn ℝ 1 ((⇑γ.extend) ∘ ρ) (Icc a b) :=
            hbase.comp hρdiff hmaps
          refine hcomp.congr ?_
          intro r hr
          have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hr.1, hr.2.trans hb.2⟩
          have hρr01 : ρ r ∈ Icc (0 : ℝ) 1 := by
            dsimp [ρ]
            constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, hr01.1, hr01.2]
          rw [Path.extend_apply _ hr01]
          change (γ.subpath s t) ⟨r, hr01⟩ = γ.extend (ρ r)
          rw [Path.extend_apply γ hρr01]
          simp [Path.subpath, ρ, Set.Icc.convexCombo]
      · rw [Icc_eq_empty hab]
        exact contDiffOn_empty

/-- Straight line segments are piecewise-`C¹`. -/
lemma segment_isPiecewiseC1 (x y : E) :
    (Path.segment x y).IsPiecewiseC1 := by
  apply isPiecewiseC1_of_contDiffOn_extend
  let φ : ℝ → E := fun t => AffineMap.lineMap x y t
  have hφ : ContDiff ℝ 1 φ := by
    dsimp [φ, AffineMap.lineMap]
    fun_prop
  refine hφ.contDiffOn.congr ?_
  intro t ht
  rw [Path.extend_apply _ ht]
  simp [φ]

/-- Concatenating two piecewise-`C¹` paths gives a piecewise-`C¹` path. -/
lemma IsPiecewiseC1.trans {x y z : E} {γ : Path x y} {η : Path y z}
    (hγ : γ.IsPiecewiseC1) (hη : η.IsPiecewiseC1) :
    (γ.trans η).IsPiecewiseC1 := by
  rcases hγ with ⟨Sγ, hSγ01, hγ_smooth⟩
  rcases hη with ⟨Sη, hSη01, hη_smooth⟩
  let leftBreaks : Finset ℝ := Sγ.image fun τ => τ / 2
  let rightBreaks : Finset ℝ := Sη.image fun τ => (1 + τ) / 2
  let S : Finset ℝ := insert (1 / 2 : ℝ) (leftBreaks ∪ rightBreaks)
  refine ⟨S, ?_, ?_⟩
  · intro r hr
    simp only [S, leftBreaks, rightBreaks, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at hr
    rcases hr with rfl | ⟨τ, hτ, rfl⟩ | ⟨τ, hτ, rfl⟩
    · constructor <;> norm_num
    · have hτ01 := hSγ01 τ hτ
      constructor <;> nlinarith [hτ01.1, hτ01.2]
    · have hτ01 := hSη01 τ hτ
      constructor <;> nlinarith [hτ01.1, hτ01.2]
  · intro a b ha hb hdisj
    by_cases hab : a ≤ b
    · by_cases hble : b ≤ (1 / 2 : ℝ)
      · have ha2 : 2 * a ∈ Icc (0 : ℝ) 1 := by
          constructor <;> nlinarith [ha.1, hab, hble]
        have hb2 : 2 * b ∈ Icc (0 : ℝ) 1 := by
          constructor <;> nlinarith [hb.1, hble]
        have hdisjγ : Disjoint (Ioo (2 * a) (2 * b)) (↑Sγ : Set ℝ) := by
          rw [Set.disjoint_left]
          intro τ hτI hτS
          have hτhalfI : τ / 2 ∈ Ioo a b := by
            constructor <;> nlinarith [hτI.1, hτI.2]
          have hτhalfS : τ / 2 ∈ (↑S : Set ℝ) := by
            simp only [S, leftBreaks, rightBreaks, Finset.mem_coe, Finset.mem_insert,
              Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inl ⟨τ, hτS, rfl⟩)
          exact (Set.disjoint_left.mp hdisj) hτhalfI hτhalfS
        have hbase := hγ_smooth (2 * a) (2 * b) ha2 hb2 hdisjγ
        have hscale : ContDiffOn ℝ 1 (fun r : ℝ => 2 * r) (Icc a b) := by
          fun_prop
        have hmaps : MapsTo (fun r : ℝ => 2 * r) (Icc a b) (Icc (2 * a) (2 * b)) := by
          intro r hr
          constructor <;> nlinarith [hr.1, hr.2]
        have hcomp : ContDiffOn ℝ 1 ((⇑γ.extend) ∘ fun r : ℝ => 2 * r) (Icc a b) :=
          hbase.comp hscale hmaps
        refine hcomp.congr ?_
        intro r hr
        rw [Path.extend_trans_of_le_half γ η (by nlinarith [hr.2, hble])]
        rfl
      · have hhalf_lt_b : (1 / 2 : ℝ) < b := lt_of_not_ge hble
        have hale : (1 / 2 : ℝ) ≤ a := by
          by_contra hnot
          have ha_lt_half : a < (1 / 2 : ℝ) := lt_of_not_ge hnot
          have hhalfI : (1 / 2 : ℝ) ∈ Ioo a b := ⟨ha_lt_half, hhalf_lt_b⟩
          have hhalfS : (1 / 2 : ℝ) ∈ (↑S : Set ℝ) := by
            simp [S]
          exact (Set.disjoint_left.mp hdisj) hhalfI hhalfS
        have ha2 : 2 * a - 1 ∈ Icc (0 : ℝ) 1 := by
          constructor <;> nlinarith [hale, ha.2]
        have hb2 : 2 * b - 1 ∈ Icc (0 : ℝ) 1 := by
          constructor <;> nlinarith [hale, hab, hb.2]
        have hdisjη : Disjoint (Ioo (2 * a - 1) (2 * b - 1)) (↑Sη : Set ℝ) := by
          rw [Set.disjoint_left]
          intro τ hτI hτS
          have hτhalfI : (1 + τ) / 2 ∈ Ioo a b := by
            constructor <;> nlinarith [hτI.1, hτI.2]
          have hτhalfS : (1 + τ) / 2 ∈ (↑S : Set ℝ) := by
            simp only [S, leftBreaks, rightBreaks, Finset.mem_coe, Finset.mem_insert,
              Finset.mem_union, Finset.mem_image]
            exact Or.inr (Or.inr ⟨τ, hτS, rfl⟩)
          exact (Set.disjoint_left.mp hdisj) hτhalfI hτhalfS
        have hbase := hη_smooth (2 * a - 1) (2 * b - 1) ha2 hb2 hdisjη
        have hscale : ContDiffOn ℝ 1 (fun r : ℝ => 2 * r - 1) (Icc a b) := by
          fun_prop
        have hmaps : MapsTo (fun r : ℝ => 2 * r - 1) (Icc a b)
            (Icc (2 * a - 1) (2 * b - 1)) := by
          intro r hr
          constructor <;> nlinarith [hr.1, hr.2]
        have hcomp : ContDiffOn ℝ 1 ((⇑η.extend) ∘ fun r : ℝ => 2 * r - 1) (Icc a b) :=
          hbase.comp hscale hmaps
        refine hcomp.congr ?_
        intro r hr
        rw [Path.extend_trans_of_half_le γ η (by nlinarith [hale, hr.1])]
        rfl
    · rw [Icc_eq_empty hab]
      exact contDiffOn_empty

/-- Alias specialized to complex-valued paths. -/
public abbrev IsPiecewiseC1Complex {a b : ℂ} (γ : Path a b) : Prop :=
  γ.IsPiecewiseC1

/-- A path maps into a set if every point of its parameter interval lands in that set. -/
public abbrev MapsInto
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (U : Set X) : Prop :=
  ∀ t : I, γ t ∈ U

end Path
