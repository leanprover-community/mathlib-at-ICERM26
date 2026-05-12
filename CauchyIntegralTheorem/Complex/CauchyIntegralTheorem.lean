/-
Copyright (c) 2026 Lean community.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/

module


public import CurveIntegral.Local
public import PiecewiseLinear.Homotopy

open MeasureTheory intervalIntegral
open Set
open scoped Topology unitInterval Interval

public section

theorem complexCurveIntegral_eq_of_homotopic_piecewiseC1
    {a b : ℂ} {U : Set ℂ} {f : ℂ → ℂ} {γ γ' : Path a b}
    (hU_open : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (hγC1 : γ.IsPiecewiseC1)
    (hγ'C1 : γ'.IsPiecewiseC1)
    (H : Path.Homotopy γ γ')
    (hHU : ∀ s t : I, H (s, t) ∈ U) :
    complexCurveIntegral f γ' = complexCurveIntegral f γ := by
  have hlocal :
      ∀ {η : Path a b}, η.IsPiecewiseC1 → η.MapsInto U →
        ∃ ε > 0, ∀ {η' : Path a b},
          η'.IsPiecewiseC1 →
          η.UniformClose η' ε →
            η'.MapsInto U ∧
            complexCurveIntegral f η' = complexCurveIntegral f η := by
    intro η hηC1 hηU
    exact exists_eps_eq_complexCurveIntegral_of_uniformClose_piecewiseC1'
      hU_open hf hηU hηC1

  rcases Path.exists_piecewiseC1_homotopy_of_homotopy
      hU_open hγC1 hγ'C1 H hHU 1 zero_lt_one with
    ⟨Γ, hΓC1, hΓU, _hΓclose⟩

  let S : Set I := {s | complexCurveIntegral f (Γ.eval s) = complexCurveIntegral f γ}
  let Γc : C(I, C(I, ℂ)) := Γ.toHomotopy.curry
  have hΓc_cont : Continuous Γc := Γc.continuous

  have hclose_of_mem_ball :
      ∀ {s r : I} {ε : ℝ}, Γc r ∈ Metric.ball (Γc s) ε →
        (Γ.eval s).UniformClose (Γ.eval r) ε := by
    intro s r ε hr t
    have hdist : dist ((Γc s) t) ((Γc r) t) ≤ dist (Γc s) (Γc r) :=
      ContinuousMap.dist_apply_le_dist t
    exact lt_of_le_of_lt hdist (by simpa [Metric.mem_ball, dist_comm] using hr)

  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S]

  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    rcases hlocal (hΓC1 s) (hΓU s) with ⟨ε, hε, hεlocal⟩
    have hball : Metric.ball (Γc s) ε ∈ 𝓝 (Γc s) := Metric.ball_mem_nhds _ hε
    have hpre : Γc ⁻¹' Metric.ball (Γc s) ε ∈ 𝓝 s :=
      hΓc_cont.continuousAt hball
    refine Filter.mem_of_superset hpre ?_
    intro r hr
    have hclose : (Γ.eval s).UniformClose (Γ.eval r) ε :=
      hclose_of_mem_ball hr
    exact (hεlocal (hΓC1 r) hclose).2.trans hs

  have hS_closed : IsClosed S := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro s hs
    rcases hlocal (hΓC1 s) (hΓU s) with ⟨ε, hε, hεlocal⟩
    have hball : Metric.ball (Γc s) ε ∈ 𝓝 (Γc s) := Metric.ball_mem_nhds _ hε
    have hpre : Γc ⁻¹' Metric.ball (Γc s) ε ∈ 𝓝 s :=
      hΓc_cont.continuousAt hball
    refine Filter.mem_of_superset hpre ?_
    intro r hr hrS
    have hclose : (Γ.eval s).UniformClose (Γ.eval r) ε :=
      hclose_of_mem_ball hr
    exact hs (by
      calc
        complexCurveIntegral f (Γ.eval s) = complexCurveIntegral f (Γ.eval r) :=
          (hεlocal (hΓC1 r) hclose).2.symm
        _ = complexCurveIntegral f γ := hrS)

  have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
  have hS_univ : S = Set.univ := by
    rcases (connectedSpace_iff_clopen.mp (by infer_instance : ConnectedSpace I)).2 S hS_clopen with
      hS_empty | hS_univ
    · exact False.elim (hS_nonempty.ne_empty hS_empty)
    · exact hS_univ

  have h_one_mem : (1 : I) ∈ S := by
    rw [hS_univ]
    trivial
  have h_eval_one : complexCurveIntegral f (Γ.eval (1 : I)) = complexCurveIntegral f γ := by
    simpa [S] using h_one_mem
  simpa using h_eval_one
