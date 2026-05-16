module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Sheaves.Stalks

open Function Set CategoryTheory TopologicalSpace Opposite Filter
open scoped Topology

structure WithDiscreteTopology (α : Type*) where
  val : α

instance (α : Type*) : TopologicalSpace (WithDiscreteTopology α) := ⊥
instance (α : Type*) : DiscreteTopology (WithDiscreteTopology α) := ⟨rfl⟩

namespace TopCat.Presheaf

-- TODO: add universes everywhere
variable {X : TopCat.{0}} {C : Type} [Category.{0} C] {CC : C → Type} {FC : C → C → Type}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] [Limits.HasColimits C]

structure EspaceEtale (F : Presheaf C X) where
  base : X
  germ : ToType (F.stalk base)

instance (F : Presheaf C X) : TopologicalSpace F.EspaceEtale :=
  .generateFrom {s | ∃ U, ∃ f : ToType (F.obj (op U)),
    s = {g | ∃ h, g.germ = F.germ U g.base h f}}

variable {F : Presheaf C X}

theorem EspaceEtale.eventually_nhds (g : EspaceEtale F) {U : Opens X} (h : g.base ∈ U)
    (f : ToType (F.obj (op U))) (hf : F.germ U g.base h f = g.germ) :
    ∀ᶠ g' : EspaceEtale F in 𝓝 g, ∃ hgU : g'.base ∈ U, g'.germ = F.germ U g'.base hgU f := by
  simp only [nhds_generateFrom, Filter.Eventually, mem_setOf_eq, iInf_and, iInf_exists]
  refine mem_iInf_of_mem _ <| mem_iInf_of_mem ?_ <| mem_iInf_of_mem U <| mem_iInf_of_mem f <|
    mem_iInf_of_mem rfl <| mem_principal_self _
  simp [*]

variable [Limits.PreservesColimits (forget C)]

theorem exists_le_germ_eq {x : X} {U : Opens X} (h : x ∈ U) (g : ToType (F.stalk x)) :
    ∃ V ≤ U, ∃ (h : x ∈ V) (f : ToType (F.obj (op V))), F.germ V x h f = g := by
  rcases F.germ_exist x g with ⟨V, hxV, f, rfl⟩
  refine ⟨U ⊓ V, inf_le_left, mem_inter h hxV, F.map (.op <| homOfLE inf_le_right) f, ?_⟩
  exact germ_res_apply ..

variable (F) in
@[fun_prop]
theorem EspaceEtale.continuous_base : Continuous (base (F := F)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
  rintro U ⟨hxU, hUo⟩
  lift U to Opens X using hUo
  rcases exists_le_germ_eq hxU x.germ with ⟨V, hVU, hxV, f, hf⟩
  refine x.eventually_nhds hxV f hf |>.mono ?_
  simp +contextual [@hVU _]

@[simps apply_fst]
noncomputable def EspaceEtale.homeomorph
    (U : Opens X)
    (hF_bij : ∀ (x : X) (hx : x ∈ U), Bijective (F.germ U x hx))
    (x : X) (hx : x ∈ U) :
    (base (F := F) ⁻¹' U) ≃ₜ U × WithDiscreteTopology (ToType (F.stalk x)) where
  toFun s := (⟨s.1.base, s.2⟩,
    ⟨F.germ U x hx <| surjInv (hF_bij s.1.base s.2).surjective s.1.germ⟩)
  invFun
  | (⟨y, hy⟩, ⟨g⟩) => ⟨⟨y, F.germ U y hy <| surjInv (hF_bij x hx).surjective g⟩, hy⟩
  left_inv := by
    rintro ⟨⟨base, s⟩, hs⟩
    simp only
    congr 2
    rw [leftInverse_surjInv (hF_bij _ _), surjInv_eq (hF_bij _ _).surjective]
  right_inv := by
    rintro ⟨⟨y, hy⟩, ⟨g⟩⟩
    simp only
    congr
    rw [leftInverse_surjInv (hF_bij _ _), surjInv_eq (hF_bij _ _).surjective]
  continuous_toFun := by
    refine .prodMk (by fun_prop) ?_
    simp_rw [continuous_iff_continuousAt, ContinuousAt, nhds_discrete, tendsto_pure, nhds_subtype,
      eventually_comap]
    rintro ⟨g, hg⟩
    rcases hF_bij _ hg |>.surjective g.germ with ⟨f, hf⟩
    filter_upwards [g.eventually_nhds hg f hf]
    rintro _ ⟨hgU, hgf⟩ g' rfl
    congr 1
    rw [hgf, ← hf, leftInverse_surjInv (hF_bij _ _), leftInverse_surjInv (hF_bij _ _)]
  continuous_invFun := by
    simp_rw [continuous_iff_continuousAt, continuousAt_prod_of_discrete_right]
    rintro ⟨y, ⟨g⟩⟩
    simp only [ContinuousAt, nhds_subtype_eq_comap, tendsto_comap_iff, comp_def,
      nhds_generateFrom, tendsto_iInf, mem_setOf_eq, tendsto_principal]
    rintro _ ⟨hmem, V, f, rfl⟩
    simp only [mem_setOf_eq] at hmem
    rcases hmem with ⟨hyV, hgf⟩
    rcases F.germ_eq _ _ _ _ _ hgf with ⟨W, hyW, ιWU, ιWV, hW⟩
    filter_upwards [W.isOpen.preimage continuous_subtype_val |>.mem_nhds hyW] with z hz
    use ιWV.le hz
    rw [← F.germ_res_apply ιWU z hz, hW, F.germ_res_apply]

theorem EspaceEtale.isCoveringMap_base
    (hF_bij : ∀ x, ∃ (U : Opens X), x ∈ U ∧ ∀ y (hyU : y ∈ U), Bijective (F.germ U y hyU)) :
    IsCoveringMap (base (F := F)) := by
  refine fun x ↦ .to_isEvenlyCovered_preimage (I := WithDiscreteTopology (ToType (F.stalk x))) ?_
  use inferInstance
  rcases hF_bij x with ⟨U, hxU, hU_bij⟩
  use U, hxU, U.isOpen, U.isOpen.preimage (continuous_base F), homeomorph U hU_bij x hxU
  simp

theorem EspaceEtale.exists_section_of_tendsto {α : Type*} {l : Filter α} {g : α → F.EspaceEtale}
    {g₀ : F.EspaceEtale} (h : Tendsto g l (𝓝 g₀)) :
    ∃ (U : Opens X), g₀.base ∈ U ∧ ∃ (f : ToType (F.obj (op U))),
      ∀ᶠ a in l, ∃ ha : (g a).base ∈ U, (g a).germ = F.germ U (g a).base ha f := by
  rcases F.germ_exist _ g₀.germ with ⟨U, hU, s, hs⟩
  use U, hU, s
  exact h.eventually <| g₀.eventually_nhds hU s hs

end TopCat.Presheaf

#exit

open Filter Metric
open scoped Topology Asymptotics

structure LocalAddGerms (X G : Type*) [TopologicalSpace X] [AddGroup G] where
  germsAt (x : X) : Set (Germ (𝓝 x) G)
  exists_local_section (x : X) : ∃ f : X → G, ∀ᶠ x' in 𝓝 x, .ofFun f ∈ germsAt x'
  const_vadd_mem_germsAt {x : X} {g : Germ (𝓝 x) G} :
    g ∈ germsAt x → ∀ c : G, c +ᵥ g ∈ germsAt x
  exists_const_vadd_eq {x : X} {g₁ g₂ : Germ (𝓝 x) G} :
    g₁ ∈ germsAt x → g₂ ∈ germsAt x → ∃ c : G, c +ᵥ g₁ = g₂

structure LocalAddGerms.EtaleSpace {X G : Type*} [TopologicalSpace X] [AddGroup G]
    (gs : LocalAddGerms X G) where
  base (gs) : X
  value : G

@[to_additive]
structure LocalMulGerms (X G : Type*) [TopologicalSpace X] [Group G] where
  germsAt (x : X) : Set (Germ (𝓝 x) G)
  exists_local_section (x : X) : ∃ f : X → G, ∀ᶠ x' in 𝓝 x, .ofFun f ∈ germsAt x'
  const_smul_mem_germsAt {x : X} {g : Germ (𝓝 x) G} :
    g ∈ germsAt x → ∀ c : G, c • g ∈ germsAt x
  exists_const_smul_eq {x : X} {g₁ g₂ : Germ (𝓝 x) G} :
    g₁ ∈ germsAt x → g₂ ∈ germsAt x → ∃ c : G, c • g₁ = g₂

@[to_additive (attr := ext)]
structure LocalMulGerms.EtaleSpace {X G : Type*} [TopologicalSpace X] [Group G]
    (gs : LocalMulGerms X G) where
  base (gs) : X
  value : G

namespace LocalMulGerms

variable {X G : Type*} [TopologicalSpace X] [Group G] {gs : LocalMulGerms X G}

@[to_additive]
theorem germsAt_eq_of_mem {x : X} {g : Germ (𝓝 x) G} (h : g ∈ gs.germsAt x) :
    gs.germsAt x = Set.range fun c : G ↦ c • g := by
  ext g'
  constructor
  · exact gs.exists_const_smul_eq h
  · rintro ⟨c, rfl⟩
    exact gs.const_smul_mem_germsAt h _

@[to_additive (attr := simp)]
theorem const_smul_mem_germsAt_iff {x : X} {g : Germ (𝓝 x) G} (c : G) :
    c • g ∈ gs.germsAt x ↔ g ∈ gs.germsAt x := by
  refine ⟨fun h ↦ ?_, (gs.const_smul_mem_germsAt · c)⟩
  simpa using gs.const_smul_mem_germsAt h c⁻¹

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
      simpa using hf x hx
    · rintro g' ⟨hg'U, hg'val⟩
      simp [hg'val]
  continuousOn_invFun := by
    simp_rw [continuousOn_prod_of_discrete_right, continuousOn_to_generateFrom_iff,
      Set.mem_setOf_eq, Set.mem_prod_eq, Set.mem_univ, and_true, Set.setOf_mem_eq]
    rintro ⟨y⟩ x hx t ⟨V, f', hVo, hfV, rfl⟩
    simp only [Set.mem_setOf_eq, ← eq_mul_inv_iff_mul_eq, hUo.nhdsWithin_eq hx]
    rintro ⟨hxV, rfl⟩
    simp only [Set.preimage_setOf_eq]
    rcases gs.exists_const_smul_eq (hf x hx) (hfV x hxV) with ⟨c, hc⟩
    rw [← Germ.coe_smul, Germ.coe_eq] at hc
    filter_upwards [hc, hVo.mem_nhds hxV]
    simp +contextual [← hc.self_of_nhds]
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
  use EtaleSpace.trivialization gs U hUo f hU
  simpa

@[to_additive]
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

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ω : E → E →L[𝕜] F}

def LocalMulGerms.ofFDerivSymm (U : Set E) (hU : IsOpen U) (ω : E → E →L[𝕜] F)
    (hωd : DifferentiableOn 𝕜 ω U) (hω_symm : ∀ a x y, fderiv 𝕜 ω a x y = fderiv 𝕜 ω a y x) :
    LocalAddGerms U F where
  germsAt x := (fun f ↦ ↑(fun x : U ↦ f x)) '' {f : E → F | ∀ᶠ x' in 𝓝 x, HasFDerivAt f (ω x') x'}
  exists_local_section x := by
    sorry
  const_vadd_mem_germsAt := by
    rintro ⟨x, hxU⟩ g ⟨f, hf, rfl⟩ c
    exact ⟨c +ᵥ f, hf.mono fun x' hx' ↦ hx'.const_add c, by simp [← Germ.coe_vadd, Pi.vadd_def]⟩
  exists_const_vadd_eq := by
    rintro x _ _ ⟨f₁, hf₁, rfl⟩ ⟨f₂, hf₂, rfl⟩
    rw [Set.mem_setOf_eq] at hf₁ hf₂
    use f₂ x - f₁ x
    simp only [← Germ.coe_vadd, Germ.coe_eq]
    -- TODO: add to mean value theorems

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
