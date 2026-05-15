module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Topology.Covering.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Germ
import Mathlib.Topology.Homotopy.Lifting

open Filter Metric
open scoped Topology Asymptotics

structure LocalAddGerms (X G : Type*) [TopologicalSpace X] [AddGroup G] where
  germsAt (x : X) : Set (Germ (𝓝 x) G)
  exists_local_section (x : X) :
    ∃ f : X → G, ∀ᶠ x' in 𝓝 x, germsAt x' = Set.range fun c : G ↦ c +ᵥ .ofFun f
  exists_const_vadd_eq {x : X} {f₁ f₂ : X → G} :
    (∀ᶠ x' in 𝓝 x, .ofFun f₁ ∈ germsAt x') → (∀ᶠ x' in 𝓝 x, .ofFun f₂ ∈ germsAt x') →
    ∃ c : G, f₁ =ᶠ[𝓝 x] (c +ᵥ f₂)

structure LocalAddGerms.EtaleSpace {X G : Type*} [TopologicalSpace X] [AddGroup G]
    (gs : LocalAddGerms X G) where
  base (gs) : X
  value : G

@[to_additive]
structure LocalMulGerms (X G : Type*) [TopologicalSpace X] [Group G] where
  germsAt (x : X) : Set (Germ (𝓝 x) G)
  exists_local_section (x : X) :
    ∃ f : X → G, ∀ᶠ x' in 𝓝 x, germsAt x' = Set.range fun c : G ↦ c • .ofFun f
  exists_const_smul_eq {x : X} {f₁ f₂ : X → G} :
    (∀ᶠ x' in 𝓝 x, .ofFun f₁ ∈ germsAt x') → (∀ᶠ x' in 𝓝 x, .ofFun f₂ ∈ germsAt x') →
    ∃ c : G, f₁ =ᶠ[𝓝 x] (c • f₂)

@[to_additive (attr := ext)]
structure LocalMulGerms.EtaleSpace {X G : Type*} [TopologicalSpace X] [Group G]
    (gs : LocalMulGerms X G) where
  base (gs) : X
  value : G

structure WithDiscreteTopology (α : Type*) where
  val : α

instance (α : Type*) : TopologicalSpace (WithDiscreteTopology α) := ⊥
instance (α : Type*) : DiscreteTopology (WithDiscreteTopology α) := ⟨rfl⟩

namespace LocalMulGerms

variable {X G : Type*} [TopologicalSpace X] [Group G] {gs : LocalMulGerms X G}

@[to_additive]
theorem germsAt_eq_of_mem {x : X} {g : Germ (𝓝 x) G} (h : g ∈ gs.germsAt x) :
    gs.germsAt x = Set.range fun c : G ↦ c • g := by
  rcases gs.exists_local_section x with ⟨f, hf⟩
  rw [hf.self_of_nhds] at h ⊢
  rcases h with ⟨c, rfl⟩
  rw [← (mul_right_surjective c).range_comp]
  simp [Function.comp_def, mul_smul]

@[to_additive]
theorem smul_mem_germsAt {x : X} {g : Germ (𝓝 x) G} (h : g ∈ gs.germsAt x) (c : G) :
    c • g ∈ gs.germsAt x := by
  rw [germsAt_eq_of_mem h]
  exact ⟨c, rfl⟩

@[to_additive]
instance (gs : LocalMulGerms X G) : TopologicalSpace gs.EtaleSpace :=
  .generateFrom {s | ∃ (U : Set X) (f : X → G), IsOpen U ∧ (∀ x ∈ U, .ofFun f ∈ gs.germsAt x) ∧
    s = {g | g.base ∈ U ∧ g.value = f g.base}}

@[to_additive]
theorem exists_local_section_apply_eq (gs : LocalMulGerms X G) (x : X) (g : G) :
    ∃ f : X → G, (∀ᶠ x' in 𝓝 x, .ofFun f ∈ gs.germsAt x') ∧ f x = g := by
  rcases gs.exists_local_section x with ⟨f, hf⟩
  refine ⟨g • (f x)⁻¹ • f, hf.mono fun x' hx ↦ ?_, by simp⟩
  simp [hx, smul_smul]

@[to_additive]
theorem EtaleSpace.eventually_base_mem_and_value_eq (g : gs.EtaleSpace) (f : X → G)
    (hf : ∀ᶠ x in 𝓝 g.base, .ofFun f ∈ gs.germsAt x)
    (hfg : f g.base = g.value) {U : Set X} (hU : U ∈ 𝓝 g.base) :
    ∀ᶠ g' in 𝓝 g, g'.base ∈ U ∧ g'.value = f g'.base := by
  rw [(nhds_basis_opens _).restrict_subset hU |>.eventually_iff] at hf
  rcases hf with ⟨V, ⟨⟨hVg, hVo⟩, hVU⟩, hVf⟩
  simp only [TopologicalSpace.nhds_generateFrom, Set.mem_setOf_eq, iInf_and, iInf_exists]
  refine mem_iInf_of_mem {g | g.base ∈ V ∧ g.value = f g.base} ?_
  refine mem_iInf_of_mem (by simp [hfg, hVg]) ?_
  refine mem_iInf_of_mem V <| mem_iInf_of_mem f <| mem_iInf_of_mem hVo ?_
  refine mem_iInf_of_mem hVf <| mem_iInf_of_mem rfl ?_
  simp +contextual [Set.subset_def, Set.mem_of_mem_of_subset _ hVU]

@[to_additive]
theorem EtaleSpace.continuous_base : Continuous (base gs) := by
  rw [continuous_iff_continuousAt]
  intro g U hU
  rcases gs.exists_local_section_apply_eq g.base g.value with ⟨f, hf, hfg⟩
  exact g.eventually_base_mem_and_value_eq f hf hfg hU |>.mono fun _ ↦ And.left

@[to_additive (attr := simps)]
def EtaleSpace.trivialization (gs : LocalMulGerms X G) (U : Set X) (hUo : IsOpen U) (f : X → G)
    (hf : ∀ x ∈ U, .ofFun f ∈ gs.germsAt x) :
    Bundle.Trivialization (WithDiscreteTopology G) (EtaleSpace.base gs) where
  toFun g := (g.base, ⟨g.value / f g.base⟩)
  invFun | (x, y) => ⟨x, y.val * f x⟩
  baseSet := U
  source := EtaleSpace.base gs ⁻¹' U
  source_eq := rfl
  target := U ×ˢ Set.univ
  target_eq := rfl
  left_inv' g hg := by ext <;> simp
  right_inv' := by
    rintro ⟨x, ⟨y⟩⟩ ⟨hx, -⟩
    simp
  map_source' := by simp
  map_target' := by simp
  open_baseSet := hUo
  open_target := hUo.prod isOpen_univ
  open_source := hUo.preimage EtaleSpace.continuous_base
  continuousOn_toFun := by
    refine EtaleSpace.continuous_base.continuousOn.prodMk fun g hg ↦ ?_
    rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
    refine g.eventually_base_mem_and_value_eq ((g.value / f g.base) • f) ?_ (by simp)
      (hUo.mem_nhds hg) |>.mono ?_ |>.filter_mono nhdsWithin_le_nhds
    · filter_upwards [hUo.mem_nhds hg] with x hx
      rw [Germ.coe_smul]
      exact smul_mem_germsAt (hf x hx) _
    · rintro g' ⟨hg'U, hg'val⟩
      simp [hg'val]
  continuousOn_invFun := by
    simp_rw [continuousOn_prod_of_discrete_right, continuousOn_to_generateFrom_iff,
      Set.mem_setOf_eq, Set.mem_prod_eq, Set.mem_univ, and_true, Set.setOf_mem_eq]
    rintro ⟨y⟩ x hx t ⟨V, f', hVo, hfV, rfl⟩
    simp only [Set.mem_setOf_eq, ← eq_mul_inv_iff_mul_eq, hUo.nhdsWithin_eq hx]
    rintro ⟨hxV, rfl⟩
    simp only [Set.preimage_setOf_eq]
    rcases gs.exists_const_smul_eq (mem_nhds_iff.mpr ⟨U, hf, hUo, hx⟩)
      (mem_nhds_iff.mpr ⟨V, hfV, hVo, hxV⟩) with ⟨c, hc⟩
    filter_upwards [hc, hVo.mem_nhds hxV]
    simp +contextual [hc.self_of_nhds]
  proj_toFun := by simp

variable (gs) in
@[to_additive]
theorem isCoveringMap_base : IsCoveringMap (EtaleSpace.base gs) := by
  suffices ∀ x, ∃ t : Bundle.Trivialization (WithDiscreteTopology G) (EtaleSpace.base gs),
      x ∈ t.baseSet by
    choose t ht using this
    exact .mk _ _ t ht
  intro x
  rcases gs.exists_local_section x with ⟨f, hf⟩
  rcases _root_.eventually_nhds_iff.mp hf with ⟨U, hU, hUo, hxU⟩
  replace hU : ∀ y ∈ U, .ofFun f ∈ gs.germsAt y := by
    intro y hy
    rw [hU y hy]
    use 1
    simp
  use EtaleSpace.trivialization gs U hUo f hU
  simpa

theorem exists_mem_germsAt_compTendsto_eq_of_tendsto_etaleSpace {α : Type*} {l : Filter α}
    {g₀ : gs.EtaleSpace} {g : α → gs.EtaleSpace} (hg : Tendsto g l (𝓝 g₀)) :
    ∃ f ∈ gs.germsAt g₀.base,
      f.compTendsto (EtaleSpace.base gs ∘ g) (EtaleSpace.continuous_base.tendsto _ |>.comp hg) =
        ↑(fun a : α ↦ (g a).value) := by
  rcases gs.exists_local_section_apply_eq g₀.base g₀.value with ⟨f, hf, hfg⟩
  rcases _root_.eventually_nhds_iff.mp hf with ⟨U, hU, hUo, hgU⟩
  have hg' := TopologicalSpace.tendsto_nhds_generateFrom_iff.mp hg
  specialize hg' _ ⟨U, f, hUo, hU, rfl⟩ (by simp [hgU, hfg])
  refine ⟨f, hU _ hgU, ?_⟩
  rw [Germ.coe_compTendsto, Germ.coe_eq]
  filter_upwards [hg'] with a ha
  simp_all

end LocalMulGerms


#exit

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {ω : E → E →L[ℂ] F}

structure PrimitiveTotalSpace (ω : E → E →L[ℂ] F) where
  base (ω) : E
  germ : Germ (𝓝 base) F
  fderiv_germ : ∀ f : E → F, germ = f → ∀ᶠ x in 𝓝 base, HasFDerivAt f (ω x) x

def PrimitiveTotalSpace.value (g : PrimitiveTotalSpace ω) : F :=
  g.germ.value

@[simp]
theorem PrimitiveTotalSpace.value_mk (base germ fderiv_germ) :
    (mk base germ fderiv_germ : PrimitiveTotalSpace ω).value = germ.value :=
  rfl

theorem PrimitiveTotalSpace.germ_eq_coe_sub_add (g : PrimitiveTotalSpace ω)
    (f : E → F) (hf : ∀ᶠ x in 𝓝 g.base, HasFDerivAt f (ω x) x) :
    g.germ = ↑(f · - f g.base + g.value) := by
  rcases g with ⟨base, germ, fderiv_germ⟩
  cases germ using Germ.inductionOn with | _ g => ?_
  simp only [Germ.coe_eq]
  rcases Metric.eventually_nhds_iff.mp ((fderiv_germ _ rfl).and hf)
    with ⟨r, hr₀, hr⟩
  filter_upwards [ball_mem_nhds _ hr₀] with x hx
  refine convex_ball base r |>.eqOn_of_fderivWithin_eq (𝕜 := ℂ)
    (fun x hx ↦ (hr hx).1.differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hr hx).2.differentiableAt.differentiableWithinAt.sub_const _ |>.add_const _)
    isOpen_ball.uniqueDiffOn
    (fun y hy ↦ ?_)
    (mem_ball_self hr₀)
    (by simp [value])
    hx
  rw [(hr hy).1.hasFDerivWithinAt.fderivWithin, fderivWithin_add_const, fderivWithin_sub_const,
    (hr hy).2.hasFDerivWithinAt.fderivWithin] <;> exact isOpen_ball.uniqueDiffOn y hy

@[ext]
theorem PrimitiveTotalSpace.ext {g₁ g₂ : PrimitiveTotalSpace ω} (hbase : g₁.base = g₂.base)
    (hvalue : g₁.value = g₂.value) : g₁ = g₂ := by
  rcases g₂ with ⟨base₂, germ₂, fderiv_germ₂⟩
  subst hbase
  suffices g₁.germ = germ₂ by
    cases g₁
    congr
  cases germ₂ using Germ.inductionOn with | _ g₂ => ?_
  simp [g₁.germ_eq_coe_sub_add g₂ (fderiv_germ₂ _ rfl), hvalue]

@[simps]
def PrimitiveTotalSpace.ofFun (ω : E → E →L[ℂ] F) (f : E → F) (a : E)
    (hf : ∀ᶠ x in 𝓝 a, HasFDerivAt f (ω x) x) : PrimitiveTotalSpace ω where
  base := a
  germ := f
  fderiv_germ g hg := by
    rw [Germ.coe_eq] at hg
    filter_upwards [hf,
      eventually_eventuallyEq_nhds.mpr hg] with x hfx hfgx
    rwa [← hfgx.hasFDerivAt_iff]

@[simp]
theorem PrimitiveTotalSpace.value_ofFun (ω : E → E →L[ℂ] F) (f : E → F) (a : E) (hf) :
    (ofFun ω f a hf).value = f a :=
  rfl

instance : TopologicalSpace (PrimitiveTotalSpace ω) :=
  .generateFrom {s | ∃ (U : Set E) (f : E → F), IsOpen U ∧ (∀ x ∈ U, HasFDerivAt f (ω x) x) ∧
    s = {g | g.base ∈ U ∧ g.germ = ↑f}}

theorem PrimitiveTotalSpace.eventually_base_mem_and_germ_eq (g : PrimitiveTotalSpace ω)
    {f : E → F} (hf : ∀ᶠ x in 𝓝 g.base, HasFDerivAt f (ω x) x) {s : Set E} (hs : s ∈ 𝓝 g.base) :
    ∀ᶠ g' in 𝓝 g, g'.base ∈ s ∧ g'.germ = ↑(f · - f g.base + g.value) := by
  rcases Metric.mem_nhds_iff.mp (inter_mem hf hs) with ⟨ε, hε₀, hε⟩
  rw [Set.subset_inter_iff] at hε
  simp only [TopologicalSpace.nhds_generateFrom, Set.mem_setOf_eq, iInf_and, iInf_exists]
  refine mem_iInf_of_mem {g' | g'.base ∈ ball g.base ε ∧ g'.germ = ↑(f · - f g.base + g.value)} ?_
  refine mem_iInf_of_mem ⟨mem_ball_self hε₀, germ_eq_coe_sub_add _ _ hf⟩ ?_
  refine mem_iInf_of_mem (ball g.base ε) ?_
  refine mem_iInf_of_mem (f · - f g.base + g.value) ?_
  refine mem_iInf_of_mem isOpen_ball ?_
  refine mem_iInf_of_mem ?_ <| mem_iInf_of_mem ?_ ?_
  · exact fun x hx ↦ (hε.1 hx).sub_const _ |>.add_const _
  · simp
  · exact fun g' hg' ↦ ⟨hε.2 hg'.1, hg'.2⟩

theorem PrimitiveTotalSpace.continuousAt_base (g : PrimitiveTotalSpace ω)
    (hg : ∃ f : E → F, ∀ᶠ x in 𝓝 g.base, HasFDerivAt f (ω x) x) :
    ContinuousAt (base ω) g := by
  rcases hg with ⟨f, hf⟩
  intro U hU
  exact g.eventually_base_mem_and_germ_eq hf hU |>.mono fun _ ↦ And.left

variable [CompleteSpace F]

@[simps baseSet]
protected noncomputable def PrimitiveTotalSpace.trivialization (f : E → F) (a : E)
    (r : ℝ) (hr : 0 < r) (ω : E → E →L[ℂ] F) (hω : ∀ x ∈ ball a r, HasFDerivAt f (ω x) x) :
    Bundle.Trivialization (WithDiscreteTopology F) (base ω) where
  toFun g := (g.base, ⟨g.value - f g.base⟩)
  invFun xg :=
    letI := Classical.decPred (· ∈ ball a r)
    if hb : xg.fst ∈ ball a r then
      .ofFun ω (fun x ↦ f x + xg.snd.val) xg.fst <| by
        filter_upwards [isOpen_ball.mem_nhds hb] with x hx
        exact (hω x hx).add_const _
    else
      .ofFun ω f a <| by filter_upwards [ball_mem_nhds a hr] using hω
  baseSet := ball a r
  source := _
  source_eq := rfl
  target := _
  target_eq := rfl
  map_source' := by simp
  map_target' := by simp +contextual
  left_inv' := by
    intro g hg
    simp only [Set.mem_preimage] at hg
    simp only [dif_pos hg]
    ext <;> simp
  right_inv' := by
    rintro ⟨x, ⟨y⟩⟩ ⟨hx : x ∈ ball a r, -⟩
    ext <;> simp [hx]
  open_source := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    refine continuousAt_base _ ⟨f, ?_⟩ (isOpen_ball.mem_nhds hx)
    filter_upwards [isOpen_ball.mem_nhds hx] using hω
  open_target := isOpen_ball.prod isOpen_univ
  continuousOn_toFun g hg := by
    have H : ∀ᶠ x in 𝓝 g.base, HasFDerivAt f (ω x) x := by
      filter_upwards [isOpen_ball.mem_nhds hg] using hω
    refine (g.continuousAt_base ⟨f, H⟩).continuousWithinAt.prodMk ?_
    rw [ContinuousWithinAt, nhds_discrete, tendsto_pure, eventually_nhdsWithin_iff]
    refine g.eventually_base_mem_and_germ_eq H (isOpen_ball.mem_nhds hg) |>.mono fun g' hg' ↦ ?_
    simp [value, hg']
    abel
  continuousOn_invFun := by
    rw [continuousOn_prod_of_discrete_right]
    rintro ⟨y⟩
    simp only [Set.mem_prod, Set.mem_univ, and_true, Set.setOf_mem_eq]
    simp_rw [continuousOn_iff_continuous_restrict, Set.restrict_dite,
      continuous_generateFrom_iff]
    rintro s ⟨U, g, hUo, hU, rfl⟩
    rw [isOpen_iff_mem_nhds]
    rintro ⟨x, hx⟩
    simp only [Set.preimage_setOf_eq, ofFun_base, ofFun_germ, Germ.coe_eq, Set.mem_setOf_eq,
      and_imp]
    intro hxU hfyg
    filter_upwards [continuousAt_subtype_val (hUo.mem_nhds hxU),
      continuousAt_subtype_val (eventually_eventuallyEq_nhds.mpr hfyg)]
    simp +contextual
  open_baseSet := isOpen_ball
  proj_toFun := by simp

theorem PrimitiveTotalSpace.isCoveringMapOn_base {U : Set E} (hUo : IsOpen U)
    (hωd : DifferentiableOn ℝ ω U)
    (hω_symm : ∀ x ∈ U, ∀ y z, fderiv ℝ ω x y z = fderiv ℝ ω x z y) :
    IsCoveringMapOn (base ω) U := by
  suffices ∀ x ∈ U, ∃ t : Bundle.Trivialization (WithDiscreteTopology F) (base ω), x ∈ t.baseSet by
    choose t ht using this
    exact .mk _ _ (fun _ ↦ WithDiscreteTopology F) (fun x ↦ t x.1 x.2) (fun x ↦ ht x.1 x.2)
  intro x hx
  rcases Metric.isOpen_iff.mp hUo x hx with ⟨ε, hε₀, hε⟩
  rcases (convex_ball x ε).exists_forall_hasFDerivAt_of_fderiv_symmetric Metric.isOpen_ball
    (hωd.mono hε) (fun x hx ↦ hω_symm x (hε hx)) with ⟨f, hf⟩
  use PrimitiveTotalSpace.trivialization f x ε hε₀ ω hf
  simpa

theorem PrimitiveTotalSpace.isLittleO {α : Type*} {l : Filter α} {U : Set E} (hUo : IsOpen U)
    (hωd : DifferentiableOn ℝ ω U) (hω_symm : ∀ x ∈ U, ∀ y z, fderiv ℝ ω x y z = fderiv ℝ ω x z y)
    {g : α → PrimitiveTotalSpace ω} {g₀ : PrimitiveTotalSpace ω} (hg : Tendsto g l (𝓝 g₀))
    (hbase : g₀.base ∈ U) :
    (fun x ↦ (g x).value - g₀.value - ω g₀.base ((g x).base - g₀.base)) =o[l]
      (fun x ↦ (g x).base - g₀.base) := by
  rcases Metric.isOpen_iff.mp hUo g₀.base hbase with ⟨ε, hε₀, hε⟩
  rcases (convex_ball g₀.base ε).exists_forall_hasFDerivAt_of_fderiv_symmetric Metric.isOpen_ball
    (hωd.mono hε) (fun x hx ↦ hω_symm x (hε hx)) with ⟨f, hf⟩
  wlog hf₀ : f g₀.base = g₀.value generalizing f
  · exact this (f · - f g₀.base + g₀.value) (fun x hx ↦ (hf x hx).sub_const _ |>.add_const _)
      (by simp)
  have hf' : ∀ᶠ x in 𝓝 g₀.base, HasFDerivAt f (ω x) x := mem_of_superset (ball_mem_nhds _ hε₀) hf
  have hg' : Tendsto (g · |>.base) l (𝓝 g₀.base) := continuousAt_base _ ⟨f, hf'⟩ |>.tendsto.comp hg
  rw [TopologicalSpace.tendsto_nhds_generateFrom_iff] at hg
  specialize hg _ ⟨ball g₀.base ε, f, isOpen_ball, hf, rfl⟩ ⟨by simpa, ?_⟩
  · simpa [hf₀] using g₀.germ_eq_coe_sub_add f hf'
  · have := hf g₀.base (by simpa) |>.isLittleO.comp_tendsto hg'
    refine EventuallyEq.trans_isLittleO ?_ this
    simp only [Function.comp_def, hf₀]
    filter_upwards [hg] with g₁ hg₁
    simp [value, hg₁.2]

theorem PrimitiveTotalSpace.hasFDerivAt_value_of_continuousAt {U : Set E} (hUo : IsOpen U)
    (hωd : DifferentiableOn ℝ ω U) (hω_symm : ∀ x ∈ U, ∀ y z, fderiv ℝ ω x y z = fderiv ℝ ω x z y)
    {g : E → PrimitiveTotalSpace ω} {a : E} (hga : ContinuousAt g a) (hg : base ω ∘ g =ᶠ[𝓝 a] id)
    (ha : a ∈ U) :
    HasFDerivAt (fun x ↦ (g x).value) (ω a) a := by
  have H : (g a).base = a := hg.self_of_nhds
  refine .of_isLittleO <| (isLittleO hUo hωd hω_symm hga ?_).congr' ?_ ?_
  · simpa [H]
  · exact hg.mono <| by simp_all
  · exact hg.mono <| by simp_all

public theorem exists_forall_isLittleO_sub_of_fderiv_symmetric
    {X : Type*} [TopologicalSpace X] [LocPathConnectedSpace X] [SimplyConnectedSpace X]
    {U : Set E} (hUo : IsOpen U) (hωd : DifferentiableOn ℝ ω U)
    (hω_symm : ∀ x ∈ U, ∀ y z, fderiv ℝ ω x y z = fderiv ℝ ω x z y)
    {g : X → E} (hg : Continuous g) (hgU : ∀ x, g x ∈ U) :
    ∃ f : X → F, ∀ a, (fun x ↦ f x - f a - ω (g a) (g x - g a)) =o[𝓝 a] (g · - g a) := by
  cases isEmpty_or_nonempty X
  · simp
  inhabit X
  rcases Metric.isOpen_iff.mp hUo (g default) (hgU _) with ⟨ε, hε₀, hε⟩
  rcases (convex_ball (g default) ε).exists_forall_hasFDerivAt_of_fderiv_symmetric
    Metric.isOpen_ball (hωd.mono hε) (fun x hx ↦ hω_symm x (hε hx)) with ⟨f, hf⟩
  set g₀ : PrimitiveTotalSpace ω :=
    .ofFun ω f (g default) <| mem_of_superset (ball_mem_nhds (g default) hε₀) hf
  lift g to C(X, E) using hg
  rcases PrimitiveTotalSpace.isCoveringMapOn_base hUo hωd hω_symm
    |>.existsUnique_continuousMap_lifts g (e₀ := g₀) (a₀ := default) rfl hgU |>.exists
    with ⟨f', -, hf'⟩
  refine ⟨(f' · |>.value), fun a ↦ ?_⟩
  simp only [funext_iff, Function.comp_apply] at hf'
  refine PrimitiveTotalSpace.isLittleO hUo hωd hω_symm (map_continuousAt f' a) ?_ |>.congr' ?_ ?_
  all_goals simp [hf', hgU]
