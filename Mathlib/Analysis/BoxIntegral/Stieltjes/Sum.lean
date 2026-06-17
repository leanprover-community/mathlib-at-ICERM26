/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.IntegrationByParts
public import Mathlib.Analysis.BoxIntegral.Stieltjes.ChangeVariables
public import Mathlib.Analysis.BoxIntegral.Stieltjes.Riemann

/-! # Finite sums as Riemann–Stieltjes integrals

In this file we establish how various finite sums relate to the Riemann–Stieltjes integral
`∫⟨B⟩ x in a..b, f x ∂g` defined in `Analysis.BoxIntegral.Stieltjes.Defs`.

The connection is via *step-function integrators*: when the integrator `g` is constant
between integers and jumps at integer points (e.g. `g ⌊·⌋` or `g ⌊·⌋₊` for a sequence
`g : ℤ → F` or `g : ℕ → F`), the Riemann--Stieltjes integral against `g` collapses to a
finite sum over the integer jumps in the interval.  The dual perspective — the Riemann
integral against a `C¹` integrator coincides with the Stieltjes integral against the
derivative — is also developed here, and combining the two perspectives yields the
classical Abel summation identity.

## Main theorems

### Step-function integrators

* `BoxIntegral.HasStieltjesIntegral.of_fun_floor_right`: for a continuous integrand `f` and
  a sequence `g : ℤ → F`, the Stieltjes integral of `f` against the step function `g ⌊·⌋`
  equals the sum `∑ n ∈ Ioc ⌊a⌋ ⌊b⌋, B (f n) (g n - g (n - 1))`.  The corresponding
  integrability statement (`StieltjesIntegrable`) and integral-value statement
  (`stieltjesIntegral_of_fun_floor_right`) follow.
* `BoxIntegral.HasStieltjesIntegral.of_fun_Nat_floor_right` and friends: the same family
  for `g : ℕ → F` and `g ⌊·⌋₊`.
* `BoxIntegral.RiemannIntegrable.of_fun_floor` and
  `BoxIntegral.RiemannIntegrable.of_fun_Nat_floor`: the step functions `g ⌊·⌋` and `g ⌊·⌋₊`
  are themselves Riemann integrable on any `[a, b]`.
* `BoxIntegral.HasStieltjesIntegral.of_sum_Nat_Iic_right`: expressing
  `∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, B (f n) (g n)` as a Stieltjes integral against the summatory
  function `∑ n ≤ x, g n`.
* `BoxIntegral.HasStieltjesIntegral.of_Nat_floor_right` and
  `BoxIntegral.HasStieltjesIntegral.of_floor_right`: scalar special cases with integrator
  `⌊·⌋₊` or `⌊·⌋`, giving the identity `∫ f ∂⌊·⌋ = ∑ n ∈ Ioc ⌊a⌋ ⌊b⌋, f n`.
* `BoxIntegral.HasStieltjesIntegral.of_shift_Heaviside`: for the Heaviside-style integrator
  `(Set.Ici x).indicator 1`, the Stieltjes integral of a continuous `f` evaluates to `f x`
  if `x ∈ Ioc a b` and `0` otherwise — the Stieltjes-integral form of point evaluation.

### Abel summation (Equations (A.5) and (A.6) of Montgomery--Vaughan)

* `BoxIntegral.sum_mul_eq_sub_stieltjes_integral`: Equation (A.5), expressing
  `∑ n ∈ Ioc 0 N, a n * f n` as a boundary term minus a Stieltjes integral of the
  partial-sum step function against `f`.
* `BoxIntegral.sum_mul_eq_sub_integral_mul_deriv`: Equation (A.6), the same identity with
  the Stieltjes integral converted to a standard interval integral against `deriv f` (when
  `f` is `C¹`).

### Telescoping identities (top-level, outside `BoxIntegral`)

* `Int.sum_Ioc_floor_telescope` and `Nat.sum_Ioc_floor_telescope`: telescoping identities
  `∑ n ∈ Ioc ⌊a⌋ ⌊b⌋, (g n - g (n - 1)) = g ⌊b⌋ - g ⌊a⌋` (and ℕ-floor variant), proved as
  quick consequences of the step-function integration formulas above.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*,
  Cambridge Studies in Advanced Mathematics 97, Cambridge University Press, 2007 (Appendix A).

## Tags

Stieltjes integral, Riemann–Stieltjes, Abel summation, telescoping sum, step function

-/

@[expose] public section

open BoxIntegral intervalIntegral
open ContinuousLinearMap TaggedPrepartition Metric
open Prepartition hiding mem_mk
open Finset hiding Ioc mem_mk
open Fin hiding zero_lt_one

namespace BoxIntegral

variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {a b x y : ℝ} {B : E →L[ℝ] F →L[ℝ] G} {f : ℝ → E} {g : ℝ → F}

/-! ### Sums as Stieltjes integrals -/

section Sums

private lemma short {I J : Box (Fin 1)} {π : TaggedPrepartition I} (hπ : π.mesh_size ≤ 1)
    (hJ : J ∈ π) : ⌊J.upper₁⌋ = ⌊J.lower₁⌋ ∨ ⌊J.upper₁⌋ = ⌊J.lower₁⌋ + 1 := by
  simp only [mesh_size_le_iff₁, mem_boxes, mem_toPrepartition, NNReal.coe_one, Box.len,
    tsub_le_iff_right] at hπ
  replace hπ := Int.floor_mono (hπ J hJ)
  have := Int.floor_mono (J.lower_lt_upper₁).le
  rw [add_comm, Int.floor_add_one] at hπ; grind

private lemma coe_mem_Box_iff {n : ℤ} {J : Box (Fin 1)} :
    ↑n ∈ J ↔ n ∈ Finset.Ioc ⌊J.lower₁⌋ ⌊J.upper₁⌋ := by
  simp [Box.mem₁, Int.floor_lt, Int.le_floor]

private lemma floor_le (h : a ≤ x ∧ y ≤ b) : ⌊a⌋ ≤ ⌊x⌋ ∧ ⌊y⌋ ≤ ⌊b⌋ :=
  ⟨Int.floor_mono h.1, Int.floor_mono h.2⟩

/-- When the integrator is a piecewise step function `g ⌊·⌋` and the integrand
`f` is continuous, the Stieltjes integral can be expressed as a sum over the integer points. -/
theorem HasStieltjesIntegral.of_fun_floor_right (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b))
    (g : ℤ → F) :
    HasStieltjesIntegral a b B f (g ⌊·⌋) (∑ n ∈ .Ioc ⌊a⌋ ⌊b⌋, B (f n) (g n - g (n - 1))) := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  by_cases! hB : ‖B‖ = 0
  · simp_all
  rw [hasStieltjesIntegral_iff_lim_sum hab]; intro ε hε
  let M := ∑ n ∈ .Ioc ⌊a⌋ ⌊b⌋, ‖g n - g (n - 1)‖
  have hMnn : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  rcases eq_or_lt_of_le hMnn with hM | hM
  · rw [eq_comm, Finset.sum_eq_zero_iff_of_nonneg (by intros; positivity)] at hM
    simp only [norm_eq_zero] at hM
    refine ⟨1, by norm_num, fun π _ _ hmesh ↦ ?_⟩
    calc
      _ = dist (∑ J ∈ π.boxes, 0) (∑ n ∈ .Ioc ⌊a⌋ ⌊b⌋, (0:G)) := by
        congr 1
        · apply sum_congr rfl; intro J hJ
          have : g ⌊J.upper₁⌋ - g ⌊J.lower₁⌋ = 0 := by
            rcases short hmesh hJ with h | h
            · simp [h]
            convert hM _ ?_
            · simp [h]
            have := π.le_of_mem' J hJ
            simp only [Box.le_Ioc_iff hab] at this
            have := floor_le this
            grind
          simp [this]
        apply sum_congr rfl; intro n hn
        simp [hM n hn]
      _ < ε := by simp [hε]
  let ε' := ε / (2 * ‖B‖ * M)
  obtain ⟨δ, hδ, hδf⟩ := hf.metric_uniform ε' (by positivity)
  refine ⟨NNReal.mk (min (δ / 2) 1) (by positivity), show min (δ / 2) 1 > 0 by positivity,
    fun π hhen hpart hmesh ↦ ?_⟩
  have hmesh' : π.mesh_size ≤ 1 := by grw [hmesh]; exact min_le_right (δ / 2) 1
  replace hmesh : ∀ J ∈ π, J.upper₁ ≤ min (δ / 2) 1 + J.lower₁ := by
    simpa [-le_inf_iff] using hmesh
  classical
  let K : ℤ → Box (Fin 1) := fun n ↦ if h : ↑n ∈ Ioc a b then (hpart n h).choose else Ioc a b
  have hK : ∀ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, K n ∈ π ∧ ↑n ∈ K n := by
    intro n hn
    replace hn : ↑n ∈ Ioc a b := by simpa [hab, Int.floor_lt, Int.le_floor] using hn
    simp only [mem_toPrepartition, hn, ↓reduceDIte, K]
    generalize_proofs h; exact h.choose_spec
  calc
    _ = dist (∑ n ∈ .Ioc ⌊a⌋ ⌊b⌋, B (f (π.tag (K n) 0)) (g n - g (n - 1)))
      (∑ n ∈ .Ioc ⌊a⌋ ⌊b⌋, B (f n) (g n - g (n - 1))) := by
      congr 1; convert (sum_of_injOn K ?_ ?_ ?_ ?_).symm
      · intro n hn m hm hnm
        have h1 := (hK n hn).2
        have h2 := (hK m hm).2
        simp only [hnm, coe_mem_Box_iff, Finset.mem_Ioc] at h1 h2
        have := short hmesh' (hK m hm).1
        lia
      · intro n hn; exact (hK n hn).1
      · intro J hJ hJK; rcases short hmesh' hJ with h | h
        · simp [h]
        contrapose! hJK
        have : ⌊J.upper₁⌋ ∈ Finset.Ioc ⌊a⌋ ⌊b⌋ := by
          replace hJ := π.le_of_mem hJ
          simp only [Box.le_Ioc_iff hab, Finset.mem_Ioc] at hJ ⊢
          have := floor_le hJ
          lia
        refine ⟨⌊J.upper₁⌋, by grind, ?_⟩
        apply π.eq_of_mem_of_mem (hK _ this).1 hJ (hK _ this).2
        simp [Box.mem₁, h, ← Int.lt_floor_iff]
      congr! 3 with n hn <;> have := short hmesh' (hK n hn).1
      <;> have := (hK n hn).2
      <;> simp only [coe_mem_Box_iff, Finset.mem_Ioc] at this
      <;> lia
    _ ≤ (‖B‖ * ε') * M := by
      unfold M
      grw [dist_eq_norm, ← sum_sub_distrib, norm_sum_le, mul_sum]
      apply sum_le_sum; intro n hn
      grw [← sub_apply, ← map_sub, le_opNorm, le_opNorm]; gcongr
      convert (hδf _ ?_ _ ?_ ?_).le
      · simpa [hab] using π.tag_mem_Icc (K n)
      · rw [← Int.coe_mem_Ioc_iff] at hn; grind
      specialize hK n hn
      specialize hmesh (K n) hK.1
      specialize hhen (K n) hK.1
      simp [abs_lt] at hK hhen ⊢
      grind
    _ < ε := by unfold ε'; field_simp; grind

@[simp]
theorem StieltjesIntegrable.of_fun_floor_right (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b))
    (g : ℤ → F) : StieltjesIntegrable a b B f (g ⌊·⌋) :=
  (HasStieltjesIntegral.of_fun_floor_right hab hf g).stieltjesIntegrable

@[simp]
theorem stieltjesIntegral_of_fun_floor_right (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b))
    (g : ℤ → F) : ∫⟨B⟩ x in a..b, f x ∂(g ⌊·⌋) = ∑ n ∈ .Ioc ⌊a⌋ ⌊b⌋, B (f n) (g n - g (n - 1)) :=
  (HasStieltjesIntegral.of_fun_floor_right hab hf g).stieltjesIntegral_eq

@[simp]
theorem RiemannIntegrable.of_fun_floor (hab : a ≤ b) (g : ℤ → F) :
    RiemannIntegrable a b (g ⌊·⌋) := by
  simp only [RiemannIntegrable, ← StieltjesIntegrable.symm_right]
  exact StieltjesIntegrable.of_fun_floor_right hab (by fun_prop) g

/-- When the integrator is a piecewise step function `fun x ↦ g ⌊x⌋₊` and the integrand
`f` is continuous, the Stieltjes integral can be expressed as a sum over the natural
number points. -/
theorem HasStieltjesIntegral.of_fun_Nat_floor_right (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b))
    (g : ℕ → F) :
    HasStieltjesIntegral a b B f (g ⌊·⌋₊) (∑ n ∈ .Ioc ⌊a⌋₊ ⌊b⌋₊, B (f n) (g n - g (n - 1))) := by
  convert of_fun_floor_right hab hf (g ⌊·⌋₊)
  convert (sum_of_injOn (fun (n:ℕ) ↦ (n:ℤ)) ?_ ?_ ?_ ?_)
  · simp_all
  · intro n hn
    simp_all only [coe_Ioc, Set.mem_Ioc, Int.floor_lt, Int.cast_natCast,
    Int.le_floor]
    have : 0 < b := Nat.pos_of_floor_pos (by linarith)
    simp only [this.le, Nat.le_floor_iff] at hn
    exact ⟨Nat.lt_of_floor_lt hn.1, hn.2⟩
  · intro n hn hn'
    suffices ⌊n⌋₊ = ⌊n-1⌋₊ by simp [← this]
    suffices n ≤ 0 by simp [Nat.floor_of_nonpos, show n - 1 ≤ 0 by linarith, this]
    contrapose! hn'
    let m := n.toNat
    have : n = ↑m := by simp [m, hn'.le]
    have hm : m ≠ 0 := by contrapose! hn'; simp_all
    use m
    simp only [this, ← Int.coe_mem_Ioc_iff, coe_Ioc, Set.mem_Ioc, and_true, Int.cast_natCast,
      Nat.floor_lt' hm] at hn ⊢
    exact ⟨hn.1, Nat.le_floor hn.2⟩
  intros; simp

@[simp]
theorem StieltjesIntegrable.of_fun_Nat_floor_right (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b))
    (g : ℕ → F) : StieltjesIntegrable a b B f (g ⌊·⌋₊) :=
  (HasStieltjesIntegral.of_fun_Nat_floor_right hab hf g).stieltjesIntegrable

@[simp]
theorem RiemannIntegrable.of_fun_Nat_floor (hab : a ≤ b) (g : ℕ → F) :
    RiemannIntegrable a b (g ⌊·⌋₊) := by
  simp only [RiemannIntegrable, ← StieltjesIntegrable.symm_right]
  exact StieltjesIntegrable.of_fun_Nat_floor_right hab (by fun_prop) g

@[simp]
theorem stieltjesIntegral_of_fun_Nat_floor_right (hab : a ≤ b)
    (hf : ContinuousOn f (.Icc a b)) (g : ℕ → F) :
    ∫⟨B⟩ x in a..b, f x ∂(g ⌊·⌋₊) = ∑ n ∈ .Ioc ⌊a⌋₊ ⌊b⌋₊, B (f n) (g n - g (n - 1)) :=
  (HasStieltjesIntegral.of_fun_Nat_floor_right hab hf g).stieltjesIntegral_eq

/-- Sum of pairings `B (f n) (g n)` over natural `n ∈ (⌊a⌋, ⌊b⌋]`, expressed as a Stieltjes
integral of `f` against the right-continuous summatory `x ↦ ∑ n ≤ x, g n`. -/
theorem HasStieltjesIntegral.of_sum_Nat_Iic_right (hab : a ≤ b) {f : ℝ → E}
    (hf : ContinuousOn f (.Icc a b)) (g : ℕ → F) :
    HasStieltjesIntegral a b B f (∑ n ∈ .Iic ⌊·⌋₊, g n) (∑ n ∈ .Ioc ⌊a⌋₊ ⌊b⌋₊, B (f n) (g n)) := by
  convert of_fun_Nat_floor_right hab hf (∑ m ∈ .Iic ·, g m) with n hn
  rw [← add_sum_Iio_eq_sum_Iic, show Iic (n - 1) = Iio n by grind]
  abel

/-- Relate sums `∑ f n` with Stieltjes integrals `∫ f ∂(⌊·⌋₊)` -/
theorem HasStieltjesIntegral.of_Nat_floor_right (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b)) :
    HasStieltjesIntegral a b (lsmul ℝ ℝ).flip f (⌊·⌋₊)
    (∑ n ∈ .Ioc ⌊a⌋₊ ⌊b⌋₊, f n) := by
  convert of_sum_Nat_Iic_right hab hf (if · ≠ 0 then 1 else (0 : ℝ)) using 2 with x n hn
  · rw [sum_boole]; simp only [ne_eq, Nat.cast_inj]
    convert (Nat.card_Ioc 0 ⌊x⌋₊).symm
    grind
  have : n ≠ 0 := by grind
  simp [this]

@[simp]
theorem stieltjesIntegral.of_Nat_floor_right (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b)) :
    ∫⟨(lsmul ℝ ℝ).flip⟩ x in a..b, f x ∂(⌊·⌋₊) = ∑ n ∈ .Ioc ⌊a⌋₊ ⌊b⌋₊, f n :=
  (HasStieltjesIntegral.of_Nat_floor_right hab hf).stieltjesIntegral_eq

theorem HasStieltjesIntegral.of_floor_right (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b)) :
    HasStieltjesIntegral a b (lsmul ℝ ℝ).flip f (⌊·⌋) (∑ n ∈ .Ioc ⌊a⌋ ⌊b⌋, f n) := by
  convert of_fun_floor_right hab hf (fun (n:ℤ) ↦ (n:ℝ)) using 2 with n hn
  simp

@[simp]
theorem stieltjesIntegral_of_floor_right (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b)) :
    ∫⟨(lsmul ℝ ℝ).flip⟩ x in a..b, f x ∂(⌊·⌋) = ∑ n ∈ .Ioc ⌊a⌋ ⌊b⌋, f n :=
  (HasStieltjesIntegral.of_floor_right hab hf).stieltjesIntegral_eq

private theorem HasStieltjesIntegral.of_Heaviside (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b)) :
    HasStieltjesIntegral a b (lsmul ℝ ℝ).flip f ((Set.Ici 0).indicator 1)
    ((Set.Ioc a b).indicator f 0) := by
  have hint : ((Set.Ici (0:ℝ)).indicator (1:ℝ → ℝ)) = (((Set.Ici (0:ℤ)).indicator 1) ⌊·⌋) := by
    ext; simp [Set.indicator, Int.floor_nonneg]
  rw [hint]
  convert of_fun_floor_right hab hf ((Set.Ici (0:ℤ)).indicator 1) using 1
  have h_term (n : ℤ) : (lsmul ℝ ℝ).flip (f ↑n)
        ((Set.Ici 0).indicator (1:ℤ → ℝ) n - (Set.Ici 0).indicator 1 (n-1))
      = if n = 0 then f 0 else 0 := by
    obtain rfl | hn := eq_or_ne n 0
    · simp
    have hdiff : ((Set.Ici 0).indicator (1:ℤ → ℝ) n - (Set.Ici 0).indicator 1 (n - 1)) = 0 := by
      simp [Set.indicator, Set.Ici]; grind
    simp [hdiff, hn]
  simp_rw [h_term, Finset.sum_ite_eq', ← Int.coe_mem_Ioc_iff, Set.indicator]
  grind

theorem HasStieltjesIntegral.of_shift_Heaviside (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b)) :
    HasStieltjesIntegral a b (lsmul ℝ ℝ).flip f ((Set.Ici x).indicator 1)
    ((Set.Ioc a b).indicator f x) := by
  have hf' : ContinuousOn (f ∘ (· + x)) (.Icc (a - x) (b - x)) :=
    hf.comp (Continuous.continuousOn (by fun_prop)) (by intro _ _; grind)
  have hmono : StrictMonoOn (· - x : ℝ → ℝ) (.Icc a b) := fun _ _ _ _ _ ↦ by linarith
  convert (of_Heaviside (by linarith) hf').of_comp_strictMono_continuous hab hmono (by fun_prop)
    using 1
  · grind
  · ext y; simp [Set.indicator]
  · simp [Set.indicator]

theorem StieltjesIntegrable.of_shift_Heaviside (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b)) :
    StieltjesIntegrable a b (lsmul ℝ ℝ).flip f ((Set.Ici x).indicator 1) :=
  (HasStieltjesIntegral.of_shift_Heaviside hab hf).stieltjesIntegrable

@[simp]
theorem stieltjesIntegral_of_shift_Heaviside (hab : a ≤ b) (hf : ContinuousOn f (.Icc a b)) :
    ∫⟨(lsmul ℝ ℝ).flip⟩ x in a..b, f x ∂((Set.Ici x).indicator 1) =
      ((Set.Ioc a b).indicator f x) :=
  (HasStieltjesIntegral.of_shift_Heaviside hab hf).stieltjesIntegral_eq

/-- Equation (A.5) of Montgomery--Vaughan. -/
theorem sum_mul_eq_sub_stieltjes_integral {N : ℕ} {a : ℕ → ℂ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (.Icc 0 N)) :
    ∑ n ∈ .Ioc 0 N, a n * f n = (∑ n ∈ .Ioc 0 N, a n) * f N -
      ∫⟨(lsmul ℝ ℂ).flip⟩ x in 0..N, (∑ n ∈ .Ioc 0 ⌊x⌋₊, a n) ∂f := by
  have h0 : HasStieltjesIntegral 0 N (lsmul ℝ ℂ) f (fun x ↦ ∑ n ∈ .Ioc 0 ⌊x⌋₊, a n)
      (∑ n ∈ .Ioc 0 N, a n * f n) := by
    have h := HasStieltjesIntegral.of_fun_Nat_floor_right (B := lsmul ℝ ℂ)
      N.cast_nonneg hf (∑ n ∈ .Ioc 0 ·, a n)
    simp only [Nat.floor_zero, Nat.floor_natCast] at h
    convert h using 1
    apply Finset.sum_congr rfl; intro n hn
    simp only [Finset.mem_Ioc] at hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one.mpr hn.1
    simp [mul_comm, Finset.sum_Ioc_succ_top m.zero_le a]
  simp [h0.by_parts.stieltjesIntegral_eq, ← Finset.mul_sum]; ring

/-- Equation (A.6) of Montgomery--Vaughan. -/
theorem sum_mul_eq_sub_integral_mul_deriv {N : ℕ} {a : ℕ → ℂ} {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ 1 f (.Icc 0 N)) :
    ∑ n ∈ .Ioc 0 N, a n * f n = (∑ n ∈ .Ioc 0 N, a n) * f N -
      ∫ x in 0..N, (∑ n ∈ .Ioc 0 ⌊x⌋₊, a n) * (deriv f x) := by
  obtain rfl | h0 := eq_or_ne N 0
  · simp
  have hf' := hf; rw [←Set.uIcc_of_le (by positivity)] at hf'
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero h0
  rw [sum_mul_eq_sub_stieltjes_integral hf.continuousOn, (HasStieltjesIntegral.of_contDiffOn
    hf' (.of_fun_Nat_floor hN.le (∑ n ∈ .Ioc 0 ·, a n))).stieltjesIntegral_eq]
  congr 1
  refine intervalIntegral.integral_congr fun x _ ↦ ?_
  simp only [flip_apply, lsmul_apply, smul_eq_mul]
  ring

end Sums

end BoxIntegral

/-! ## Telescoping identities over Ioc-floor sums

These are quick consequences of the Stieltjes-integral / step-function correspondence above. -/

/-- Telescoping identity for integer-floor Ioc-sums. -/
theorem Int.sum_Ioc_floor_telescope {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} (hab : a ≤ b) (g : ℤ → F) :
    ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, (g n - g (n - 1)) = g ⌊b⌋ - g ⌊a⌋ := by
  convert (BoxIntegral.stieltjesIntegral_of_fun_floor_right (f := 1) (B := lsmul ℝ ℝ)
    hab (by fun_prop) g).symm using 1 <;> simp

/-- Telescoping identity for natural-floor Ioc-sums. -/
theorem Nat.sum_Ioc_floor_telescope {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} (hab : a ≤ b) (g : ℕ → F) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (g n - g (n - 1)) = g ⌊b⌋₊ - g ⌊a⌋₊ := by
  convert (BoxIntegral.stieltjesIntegral_of_fun_Nat_floor_right (f := 1) (B := lsmul ℝ ℝ)
    hab (by fun_prop) g).symm using 1 <;> simp
