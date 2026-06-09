module

public import Mathlib.Analysis.BoxIntegral.Stieltjes.Basic

open BoxIntegral

/-! ## Lexicographic ordering of one-dimensional boxes

This code is not currently in use.

-/

def Box.lexKey (J : Box (Fin 1)) : ℝ ×ₗ ℝ := toLex (J.lower₁, J.upper₁)

lemma Box.lexKey_injective : Function.Injective Box.lexKey := by
  intro J K h
  simpa [Box.lexKey, Box.congr₁] using h

def Box.lex_le (J K : Box (Fin 1)) : Prop := Box.lexKey J ≤ Box.lexKey K

noncomputable instance Box.instDecidableLexLe : DecidableRel Box.lex_le := by
  classical
  infer_instance

instance Box.instIsTransLexLe : IsTrans _ lex_le := ⟨fun _ _ _ ↦ le_trans⟩

instance Box.instIsAntisymmLexLe : Std.Antisymm lex_le :=
  ⟨fun _ _ h₁ h₂ ↦ lexKey_injective (le_antisymm h₁ h₂)⟩

instance Box.instIsTotalLexLe : Std.Total lex_le := ⟨fun _ _ ↦ le_total _ _⟩

instance Box.instIsReflLexLe : Std.Refl lex_le := ⟨fun _ ↦ le_rfl⟩

/-- Disjoint one-dimensional boxes have disjoint underlying real half-open intervals. -/
lemma disjoint_Ioc_of_disjoint_box {J K : Box (Fin 1)}
    (h : Disjoint J.toSet K) :
    Disjoint (Set.Ioc (J.lower₁) (J.upper₁)) (Set.Ioc (K.lower₁) (K.upper₁)) := by
  simp [Box.disjoint_iff₁, Set.Ioc_disjoint_Ioc] at h ⊢
  grind

/-- If two disjoint one-dimensional boxes are ordered by lower endpoint, then the first lies to the
left of the second. -/
lemma upper_le_lower_of_disjoint_box_of_lower_le {J K : Box (Fin 1)}
    (hdisj : Disjoint J.toSet K) (hlower : J.lower₁ ≤ K.lower₁) :
    J.upper₁ ≤ K.lower₁ := by
  simp [Box.disjoint_iff₁] at hdisj
  grind [Box.lower_lt_upper₁]

section Sorted

-- The material below is not currently in use.

omit [NormedSpace ℝ F] in
/-- The sum of variations over a list of ordered one-dimensional boxes is bounded by the
variation over their union. -/
lemma list_sum_eVariationOn_Icc_le_iUnion (g : ℝ → F) :
    ∀ L : List (Box (Fin 1)),
      L.Pairwise (fun J K ↦ J.upper 0 ≤ K.lower 0) →
      (L.map fun J ↦ eVariationOn g J.Icc₁).sum ≤ eVariationOn g {x | ∃ J ∈ L, x ∈ J.Icc₁ }
  | [], _ => by simp
  | J :: L, hpair => by
      rw [List.pairwise_cons] at hpair
      rcases hpair with ⟨hhead, htail⟩
      have ih := list_sum_eVariationOn_Icc_le_iUnion g L htail
      let Utail : Set ℝ := {x | ∃ K ∈ L, x ∈ K.Icc₁}
      have hleft : ∀ x ∈ J.Icc₁, ∀ y ∈ Utail, x ≤ y := by
        rintro x hx y ⟨K, hK, hyK⟩; exact hx.2.trans ((hhead K hK).trans hyK.1)
      have hU : J.Icc₁ ∪ Utail = {x | ∃ K ∈ J :: L, x ∈ K.Icc₁} := by ext x; simp [Utail]
      calc
        _ = eVariationOn g J.Icc₁ + (L.map fun J ↦ eVariationOn g J.Icc₁).sum := by simp
        _ ≤ eVariationOn g J.Icc₁ + eVariationOn g Utail := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left ih _
        _ ≤ eVariationOn g (J.Icc₁ ∪ Utail) := eVariationOn.add_le_union g hleft
        _ = _ := by rw [hU]

/-- Sorting the boxes of a one-dimensional prepartition by lower endpoint puts each box to the
left of all later boxes. -/
lemma sorted_boxes_pairwise_upper_le_lower {I : Box (Fin 1)} (π : Prepartition I) :
    (π.boxes.sort Box.lex_le).Pairwise (fun J K ↦ J.upper 0 ≤ K.lower 0) := by
  set L := π.boxes.sort Box.lex_le
  rw [List.pairwise_iff_get]
  intro i j hij
  have hne : L.get i ≠ L.get j :=
    fun h ↦ Nat.ne_of_lt hij <| val_eq_of_eq ((π.boxes.sort_nodup Box.lex_le).get_inj_iff.1 h)
  exact upper_le_lower_of_disjoint_box_of_lower_le (π.disjoint_coe_of_mem
    ((Finset.mem_sort Box.lex_le).1 (L.get_mem i))
    ((Finset.mem_sort Box.lex_le).1 (L.get_mem j)) hne)
    (Prod.Lex.monotone_fst _ _ ((π.boxes.pairwise_sort Box.lex_le).rel_get_of_lt hij))

omit [NormedSpace ℝ F] in
/-- The total variation over the boxes of a one-dimensional prepartition is bounded by the
variation on the ambient interval. -/
lemma sum_eVariationOn_Icc_le_eVariationOn (g : ℝ → F) (hab : a < b) (π : Prepartition (Ioc a b)) :
    ∑ J ∈ π.boxes, eVariationOn g J.Icc₁ ≤ eVariationOn g (Set.Icc a b) := by
  let L := π.boxes.sort Box.lex_le
  calc
    _ = (L.map fun J ↦ eVariationOn g J.Icc₁).sum := by
      rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]; rfl
    _ ≤ eVariationOn g {x | ∃ J ∈ L, x ∈ J.Icc₁ } :=
      list_sum_eVariationOn_Icc_le_iUnion g L (sorted_boxes_pairwise_upper_le_lower π)
    _ ≤ _ := by
      apply eVariationOn.mono g
      rintro x ⟨J, hJL, hxJ⟩
      exact Icc_subset_of_box_le_Ioc hab (π.le_of_mem ((Finset.mem_sort Box.lex_le).1 hJL)) hxJ

end Sorted

omit [NormedSpace ℝ F] in
/-- Real-valued form of `sum_eVariationOn_Icc_le_eVariationOn` under finite total variation. -/
lemma sum_eVariationOn_Icc_toReal_le_eVariationOn (g : ℝ → F) (hab : a < b)
    (hg : BoundedVariationOn g (Set.Icc a b)) (π : Prepartition (Ioc a b)) :
    ∑ J ∈ π.boxes, (eVariationOn g J.Icc₁).toReal ≤
      (eVariationOn g (Set.Icc a b)).toReal := by
  have hfin : ∀ J ∈ π.boxes, eVariationOn g J.Icc₁ ≠ ⊤ :=
    fun J hJ ↦ hg.mono (Icc_subset_of_box_le_Ioc hab (π.le_of_mem hJ))
  rw [← toReal_sum hfin]
  exact toReal_mono hg (sum_eVariationOn_Icc_le_eVariationOn g hab π)


end BoxIntegral

-- The old proof of `hasStieltjesIntegral_E`, given below,
-- could be useful to prove `integral_of_contDiffOn`.

-- lemma integrableOn_Icc_of_boundedVariationOn_real {f : ℝ → ℝ}
--     (hf : BoundedVariationOn f (.Icc a b)) : IntegrableOn f (.Icc a b) := by
--   rcases hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn with ⟨p, q, hp, hq, rfl⟩
--   exact (hp.integrableOn_isCompact isCompact_Icc).sub (hq.integrableOn_isCompact isCompact_Icc)

-- lemma integrableOn_Icc_of_boundedVariationOn_complex {g : ℝ → ℂ}
--     (hg : BoundedVariationOn g (.Icc a b)) : IntegrableOn g (.Icc a b) := by
--   unfold IntegrableOn; rw [← Integrable.re_im_iff]; constructor
--   · simpa using
--       integrableOn_Icc_of_boundedVariationOn_real (reCLM.lipschitz.comp_boundedVariationOn hg)
--   · simpa using
--       integrableOn_Icc_of_boundedVariationOn_real (imCLM.lipschitz.comp_boundedVariationOn hg)

-- lemma intervalIntegrable_e_mul_of_boundedVariationOn
--     (g : ℝ → ℂ) (hab : a ≤ b) (hg : BoundedVariationOn g (Set.Icc a b)) (ξ : ℝ) :
--     IntervalIntegrable (fun x : ℝ ↦ e ξ x * g x) volume a b := by
--   rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
--   exact (integrableOn_Icc_of_boundedVariationOn_complex hg).continuousOn_mul
--     (by unfold e; fun_prop) isCompact_Icc

-- lemma norm_fourier_stieltjes_subinterval_error_le
--     {g : ℝ → ℂ} {u v τ : ℝ} (huv : u ≤ v) (hτ : τ ∈ Set.Icc u v)
--     (hg : BoundedVariationOn g (.Icc u v)) {ξ : ℝ} (hξ : ξ ≠ 0) :
--     ‖(E ξ v - E ξ u) * g τ -
--         ∫ x in u..v, e ξ x * g x‖ ≤
--       (eVariationOn g (.Icc u v)).toReal * (v - u) := by
--   set V : ℝ := (eVariationOn g (.Icc u v)).toReal
--   have hKgint : IntervalIntegrable (fun x : ℝ ↦ e ξ x * g x) volume u v :=
--       intervalIntegrable_e_mul_of_boundedVariationOn g huv hg ξ
--   have hKconstint : IntervalIntegrable (fun x : ℝ ↦ e ξ x * g τ) volume u v :=
--       Continuous.intervalIntegrable (by fun_prop) u v
--   have hrewrite :
--       (E ξ v - E ξ u) * g τ -
--           ∫ x in u..v, e ξ x * g x =
--         ∫ x in u..v, e ξ x * (g τ - g x) := by
--     rw [← intervalIntegral_e_eq_primitive_sub hξ,
--       ← intervalIntegral.integral_mul_const, ← integral_sub hKconstint hKgint]
--     congr with x; ring
--   rw [hrewrite]
--   have hpoint : ∀ x ∈ Set.uIoc u v, ‖e ξ x * (g τ - g x)‖ ≤ V := by
--     intros
--     grw [norm_mul_le]
--     simpa [V, dist_eq_norm, norm_e] using BoundedVariationOn.dist_le hg hτ (by grind)
--   have habs : |v - u| = v - u := by simp [huv]
--   simpa [V, habs] using norm_integral_le_of_norm_le_const hpoint

-- lemma scalar_iUnion_boxes_eq_Ioc (hab : a < b)
--     {π : TaggedPrepartition (Ioc a b)} (hπ : π.IsPartition) :
--     ⋃ J ∈ π.boxes, J.toSet₁ = Set.Ioc a b := by
--   ext x; simp only [mem_boxes, mem_toPrepartition, Box.toSet₁_def, Set.mem_iUnion, Set.mem_Ioc,
--     exists_and_left, exists_prop]
--   refine ⟨ fun ⟨ J, _, hJ, _ ⟩ ↦ ?_, fun h ↦ ?_ ⟩
--   · have := π.le_of_mem hJ
--     simp [Box.le_iff₁, hab] at this; grind
--   obtain ⟨J, _, _⟩ := hπ (fun _ ↦ x) (by simpa [hab] using h)
--   use J; simp_all

-- lemma intervalIntegral_eq_sum_partition_integrals
--     {g : ℝ → ℂ} (hab : a < b) (hg : BoundedVariationOn g (Set.Icc a b))
--     (ξ : ℝ) {π : TaggedPrepartition (Ioc a b)} (hπ : π.IsPartition) :
--     (∫ x in a..b, e ξ x * g x) =
--       ∑ J ∈ π.boxes, ∫ x in J.lower₁..J.upper₁, e ξ x * g x := by
--   rw [intervalIntegral.integral_of_le hab.le, ← scalar_iUnion_boxes_eq_Ioc hab hπ,
--     integral_biUnion_finset _ (by measurability)]
--   · exact Finset.sum_congr rfl (fun x _ ↦
--       by simp [Box.toSet₁, ← intervalIntegral.integral_of_le x.lower_le_upper₁])
--   · exact fun J h1 K h3 h4 ↦ disjoint_Ioc_of_disjoint_box (π.disjoint_coe_of_mem h1 h3 h4)
--   intro J hJ
--   have : a ≤ J.lower₁ ∧ J.upper₁ ≤ b := by simpa [hab, Box.le_iff₁] using π.le_of_mem hJ
--   exact (intervalIntegrable_iff_integrableOn_Ioc_of_le J.lower_le_upper₁).1
--     (intervalIntegrable_e_mul_of_boundedVariationOn
--     g J.lower_le_upper₁ (hg.mono (by grind)) ξ)


-- theorem hasStieltjesIntegral_E
--     {g : ℝ → ℂ} (hab : a < b) {ξ : ℝ} (hξ : ξ ≠ 0)
--     (hg : RiemannIntegrable a b g) :
--     HasStieltjesIntegral a b (mul ℝ ℂ).flip g (E ξ)
--       (∫ x in a..b, e ξ x * g x) := by
  -- rw [HasStieltjesIntegral.of_lt _ _ _ _ hab]
  -- refine BoxIntegral.hasIntegral_iff.2 fun ε hε ↦ ?_
  -- let V : ℝ := (eVariationOn g (.Icc a b)).toReal
  -- let ρ : ℝ := ε / (4 * (V + 1))
  -- have hV_nonneg : 0 ≤ V := ENNReal.toReal_nonneg
  -- have hρ : 0 < ρ := by
  --   simp [hε, ρ]
  --   linarith
  -- let r : NNReal → (Fin 1 → ℝ) → (Set.Ioi (0 : ℝ)) :=
  --   fun (_ : NNReal) (_ : (Fin 1→ ℝ)) ↦ ⟨ρ, hρ⟩
  -- use r
  -- constructor
  -- · intro c hc' x
  --   rfl
  -- · intro c π hπ hpart
  --   let P : ℝ → ℂ := E ξ
  --   let K : ℝ → ℂ := e ξ
  --   let H : ℝ → ℂ := fun x ↦ K x * g x
  --   let vol : (Fin 1) →ᵇᵃ ℂ →L[ℝ] ℂ :=
  --     BoxAdditiveMap.ofDiff (fun x ↦ ((mul ℝ ℂ).flip).flip (P x))
  --   let term : Box (Fin 1) → ℂ := fun J ↦
  --     (P (J.upper 0) - P (J.lower 0)) * g ((π.tag J) 0) -
  --       ∫ x in J.lower 0..J.upper 0, H x
  --   have hsumInt :
  --       (∫ x in a..b, H x) =
  --         ∑ J ∈ π.boxes, ∫ x in J.lower 0..J.upper 0, H x := by
  --     simpa [H, K] using
  --       intervalIntegral_eq_sum_partition_integrals hab hg ξ hpart
  --   have hdiff :
  --       integralSum (fun x : Fin 1 → ℝ ↦ g (x 0)) vol π -
  --           ∫ x in a..b, H x =
  --         ∑ J ∈ π.boxes, term J := by
  --     unfold term integralSum H
  --     unfold vol
  --     simp only [flip_mul, BoxAdditiveMap.ofDiff_apply, Fin.isValue, coe_sub', Pi.sub_apply,
  --       mul_apply', Finset.sum_sub_distrib]
  --     rw [hsumInt]
  --     unfold H
  --     simp [sub_mul, Finset.sum_sub_distrib, Box.upper₁, Box.lower₁]
  --   have hlen : ∀ J ∈ π.boxes, J.upper 0 - J.lower 0 ≤ 2 * ρ := by
  --     intro J hJ
  --     have hJmem : J ∈ π := by
  --       apply hJ
  --     have ha : dist (J.lower) (π.tag J) ≤ ρ := by
  --       have hmem' : J.lower ∈ Metric.closedBall (π.tag J) ↑(r c (π.tag J)) :=
  --         hπ.isSubordinate J hJ (Box.lower_mem_Icc J)
  --       exact hmem'
  --     have hb : dist (π.tag J) (J.upper) ≤ ρ := by
  --       have hmem'' : J.upper ∈ Metric.closedBall (π.tag J) ↑(r c (π.tag J)):=
  --         hπ.isSubordinate J hJ (Box.upper_mem_Icc J)
  --       exact Metric.mem_closedBall'.mp hmem''
  --     have hc : dist (J.lower 0) ((π.tag J) 0) ≤ ρ := by
  --       exact le_of_max_le_left ha
  --     have hd : dist ((π.tag J) 0) (J.upper 0) ≤ ρ := by
  --       exact le_of_max_le_left hb
  --     have hdist : dist (J.lower 0) (J.upper 0) ≤ 2 * ρ := by
  --       calc
  --         dist (J.lower 0) (J.upper 0) ≤ (dist (J.lower 0) ((π.tag J) 0))
  --           + (dist ((π.tag J) 0) (J.upper 0)) := by apply dist_triangle _ _ _
  --         _ ≤ ρ + ρ := by linarith [hc, hd]
  --         _ = 2 * ρ := by ring
  --     calc
  --       (J.upper 0 - J.lower 0) ≤ |J.upper 0 - J.lower 0| := by
  --         exact le_abs_self (J.upper 0 - J.lower 0)
  --       _ ≤ dist (J.lower 0) (J.upper 0) := by
  --                   simp [Real.dist_eq, abs_sub_comm]
  --       _ ≤ 2 * ρ := by linarith [hdist]
  --   have hterm : ∀ J ∈ π.boxes,
  --       ‖term J‖ ≤
  --         2 * ρ * (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal := by
  --     intro J hJ
  --     have htagJ := hπ.isHenstock rfl J hJ
  --     have hτ : (π.tag J) 0 ∈ Set.Icc (J.lower 0) (J.upper 0) :=
  --       ⟨htagJ.1 0, htagJ.2 0⟩
  --     have hgJ : BoundedVariationOn g (Set.Icc (J.lower 0) (J.upper 0)) :=
  --       hg.mono (Icc_subset_of_box_le_Ioc hab (π.le_of_mem hJ))
  --     have hbase : ‖(E ξ (J.upper 0) -
  --       E ξ (J.lower 0)) * g (π.tag J 0) -
  --       ∫ (x : ℝ) in J.lower 0..J.upper 0, e ξ x * g x‖ ≤
  -- (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal * (J.upper 0 - J.lower 0)
  --   := norm_fourier_stieltjes_subinterval_error_le
  --       (g := g) (u := J.lower 0) (v := J.upper 0) (τ := (π.tag J) 0)
  --       (J.lower_le_upper 0) hτ hgJ hξ
  --     calc
  --       _ ≤ (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal *
  --             (J.upper 0 - J.lower 0) := by
  --         unfold term P H K
  --         apply hbase
  --       _ ≤ (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal * (2 * ρ) :=
  --           mul_le_mul_of_nonneg_left (hlen J hJ) ENNReal.toReal_nonneg
  --       _ = _ := by ring
  --   have hvarsum :
  --       ∑ J ∈ π.boxes, (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal ≤ V := by
  --     unfold V
  --     apply sum_eVariationOn_Icc_toReal_le_eVariationOn (a := a) (b := b) g hab hg
  --       π.toPrepartition
  --   have hv : 2 * ρ * V ≤ ε := by
  --     unfold ρ
  --     calc
  --       _ = ε * (1/2) * (V / (V + 1)) := by
  --         field_simp [show V + 1 ≠ 0 by linarith]
  --         ring
  --       _ ≤ ε * (V / (V + 1)) := by
  --         have hA : 0 ≤ (V / (V + 1)) := by positivity
  --         nlinarith [hA, hε]
  --       _ ≤ ε * 1 := by
  --         refine (mul_le_mul_iff_of_pos_left hε).mpr ?_
  --         have h' : 0 < V + 1 := by positivity
  --         rw [div_le_iff₀ h']
  --         simp
  --       _ = ε := by ring
  --   calc
  --     dist (integralSum (fun x : Fin 1 → ℝ ↦ g (x 0)) vol π)
  --         (∫ x in a..b, H x)
  --         = ‖∑ J ∈ π.boxes, term J‖ := by
  --       simp [dist_eq_norm, ← hdiff]
  --     _ ≤ ∑ J ∈ π.boxes, ‖term J‖ := norm_sum_le _ _
  --     _ ≤ ∑ J ∈ π.boxes,
  --         2 * ρ * (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal :=
  --       Finset.sum_le_sum hterm
  --     _ = 2 * ρ *
  --         (∑ J ∈ π.boxes, (eVariationOn g (Set.Icc (J.lower 0) (J.upper 0))).toReal) := by
  --       rw [Finset.mul_sum]
  --     _ ≤ 2 * ρ * V := by
  --         simp [hvarsum, hρ]
  --     _ ≤ ε := hv
