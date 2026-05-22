module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

@[expose] public section

open Function Set CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Filter
open scoped Topology

structure WithDiscreteTopology (α : Type*) where
  val : α

instance (α : Type*) : TopologicalSpace (WithDiscreteTopology α) := ⊥
instance (α : Type*) : DiscreteTopology (WithDiscreteTopology α) := ⟨rfl⟩

namespace TopCat.Presheaf

universe u v u_1 u_2 u_3

-- TODO: add universes everywhere
variable {X : TopCat.{u}} {C : Type v} [Category C] {CC : C → Type u} {FC : C → C → Type u}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] [Limits.HasColimits C]

structure EspaceEtale (F : Presheaf C X) where
  base : X
  germ : ToType (F.stalk base)

instance (F : Presheaf C X) : TopologicalSpace F.EspaceEtale :=
  .generateFrom {s | ∃ U, ∃ f : ToType (F.obj (op U)),
    s = {g | ∃ h, g.germ = F.germ U g.base h f}}

def IsLocalSystem (F : Presheaf C X) : Prop :=
  ∀ x, ∃ U : Opens X, x ∈ U ∧ ∀ y (hy : y ∈ U), Bijective (F.germ U y hy)

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
    (hF : IsLocalSystem F) :
    IsCoveringMap (base (F := F)) := by
  refine fun x ↦ .to_isEvenlyCovered_preimage (I := WithDiscreteTopology (ToType (F.stalk x))) ?_
  use inferInstance
  rcases hF x with ⟨U, hxU, hU_bij⟩
  use U, hxU, U.isOpen, U.isOpen.preimage (continuous_base F), homeomorph U hU_bij x hxU
  simp

theorem EspaceEtale.isCoveringMapOn_base
    {S : Set X}
    (hF : ∀ x ∈ S, ∃ U : Opens X, x ∈ U ∧
      ∀ y (hy : y ∈ U), Bijective (F.germ U y hy)) :
    IsCoveringMapOn (base (F := F)) S := by
  intro x hxS
  refine .to_isEvenlyCovered_preimage (I := WithDiscreteTopology (ToType (F.stalk x))) ?_
  use inferInstance
  rcases hF x hxS with ⟨U, hxU, hU_bij⟩
  use U, hxU, U.isOpen, U.isOpen.preimage (continuous_base F), homeomorph U hU_bij x hxU
  simp

-- This theorem is used nowhere (just for the record).
theorem EspaceEtale.exists_section_of_tendsto {α : Type*} {l : Filter α} {g : α → F.EspaceEtale}
    {g₀ : F.EspaceEtale} (h : Tendsto g l (𝓝 g₀)) :
    ∃ (U : Opens X), g₀.base ∈ U ∧ ∃ (f : ToType (F.obj (op U))),
      ∀ᶠ a in l, ∃ ha : (g a).base ∈ U, (g a).germ = F.germ U (g a).base ha f := by
  rcases F.germ_exist _ g₀.germ with ⟨U, hU, s, hs⟩
  use U, hU, s
  exact h.eventually <| g₀.eventually_nhds hU s hs

-- AI-generated; needs to be revised.
theorem EspaceEtale.existsUnique_globalSection_of_germ
    [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    (hF : IsLocalSystem F) (x : X) (sx : ToType (F.stalk x)) :
    ∃! s : C(X, F.EspaceEtale),
      s x = ⟨x, sx⟩ ∧ EspaceEtale.base ∘ s = ContinuousMap.id X := by
  let e₀ : F.EspaceEtale := ⟨x, sx⟩
  simpa [e₀, ContinuousMap.coe_id] using
    (EspaceEtale.isCoveringMap_base (F := F) hF).existsUnique_continuousMap_lifts
      (ContinuousMap.id X) x e₀ (by simp [e₀])


-- now come the sheaves of sections.

def TopCat.sectionLocalPredicate {X Y : TopCat.{u}} (p : Y ⟶ X) :
    LocalPredicate fun _ : X ↦ Y :=
  (continuousLocal X Y).and (isSection p)

noncomputable def TopCat.sheafOfSections {X Y : TopCat.{u}} (p : Y ⟶ X) : Sheaf (Type u) X :=
  subsheafToTypes (sectionLocalPredicate p)

noncomputable def TopCat.presheafOfSections
  {X Y : TopCat.{u}} (p : Y ⟶ X) : Presheaf (Type u) X :=
  (sheafOfSections p).presheaf

-- specialize to espace etale case:

noncomputable def EspaceEtale.presheafOfSections (F : Presheaf C X) :
    TopCat.Presheaf (Type u) X :=
  TopCat.presheafOfSections
    (TopCat.ofHom ⟨EspaceEtale.base, EspaceEtale.continuous_base F⟩)

-- The canonical morphism F → Sections(E → X) of (pre)sheaves, first defined on opens.

noncomputable def EspaceEtale.morphismOnOpens {U : Opens X}
  (F : Presheaf C X) (s : (ToType (F.obj (op U)))) :
    (EspaceEtale.presheafOfSections F).obj (op U) :=
  let f : ↑(unop ((Opens.toTopCat X).op.obj (op U))) → ↑(of F.EspaceEtale) :=
  (fun x => ⟨x.val, F.germ U x.val x.property s⟩)
  ⟨f, ⟨by
    change Continuous f
    rw [← continuousOn_univ, continuousOn_to_generateFrom_iff]
    intro x _ B hB hx
    change ↑U at x
    simp only [mem_setOf_eq] at B hB
    rcases hB with ⟨V, ⟨s', hB⟩⟩
    rw [hB] at hx
    rcases hx with ⟨hxV, hxgerm⟩
    simp [f] at hxgerm
    rcases F.germ_eq (x := (x : X)) (mU := x.property) (mV := hxV) (s := s) (t := s') hxgerm with
      ⟨W, hxW, iWU, iWV, hW⟩
    rw [nhdsWithin_univ]
    filter_upwards [(W.isOpen.preimage continuous_subtype_val).mem_nhds hxW] with y hyW
    rw [hB]
    use iWV.le hyW
    simp [f]
    exact F.germ_ext W hyW iWU iWV hW
    , by
      funext x
      rfl⟩⟩

noncomputable def EspaceEtale.morphism (F : Presheaf C X) :
    (F.comp (forget C)) ⟶ (EspaceEtale.presheafOfSections F) :=
  { app := fun U => TypeCat.ofHom (EspaceEtale.morphismOnOpens (F := F)),
    naturality := by
      intro U V incl
      set U := U.unop
      set V := V.unop
      set incl := incl.unop
      ext s
      apply Subtype.ext
      funext x
      change ↑(V) at x
      change (⟨(x : X), F.germ V (x : X) x.property (F.map incl.op s)⟩ : F.EspaceEtale) =
        ⟨(x : X), F.germ U (x : X) (incl.le x.property) s⟩
      simp only [EspaceEtale.mk.injEq, true_and]
      simpa using F.germ_res_apply incl (x : X) x.property s
  }

noncomputable def EspaceEtale.morphismStalks (F : Presheaf C X) (x : X) :
    TopCat.Presheaf.stalk (F.comp (forget C)) x ⟶
  (EspaceEtale.presheafOfSections F).stalk x :=
  (stalkFunctor (Type u) x).map (EspaceEtale.morphism F)

-- AI-generated; to be revised.
theorem EspaceEtale.exists_germ_eq_topSection
    {U : Opens X} (F : Presheaf C X) (x : X) (hx : x ∈ U)
    (s : (EspaceEtale.presheafOfSections F).obj (op U)) :
    ∃ (V : Opens X) (hxV : x ∈ V) (_iVU : V ⟶ U) (t : ToType (F.obj (op V))),
      (EspaceEtale.presheafOfSections F).germ U x hx s =
        (EspaceEtale.presheafOfSections F).germ V x hxV
          (EspaceEtale.morphismOnOpens F t) := by
  let sx : F.EspaceEtale := s.1 ⟨x, hx⟩
  rcases F.germ_exist sx.base sx.germ with ⟨V₀, hsxV₀, t₀, ht₀⟩
  let B : Set F.EspaceEtale :=
    {g | ∃ hgV₀ : g.base ∈ V₀, g.germ = F.germ V₀ g.base hgV₀ t₀}
  have hB_open : IsOpen B := by
    apply TopologicalSpace.isOpen_generateFrom_of_mem
    exact ⟨V₀, t₀, rfl⟩
  have hsxB : sx ∈ B := ⟨hsxV₀, ht₀.symm⟩
  have hpre : s.1 ⁻¹' B ∈ 𝓝 (⟨x, hx⟩ : U) :=
    s.2.1.continuousAt (hB_open.mem_nhds hsxB)
  rcases mem_nhds_iff.mp hpre with ⟨T, hTsub, hTopen, hxT⟩
  let W : Opens X := ⟨Subtype.val '' T, by simpa using hTopen.trans U.isOpen⟩
  have hxW : x ∈ W := ⟨⟨x, hx⟩, hxT, rfl⟩
  have hWU : W ≤ U := by
    intro y hy
    rcases hy with ⟨y, _hyT, rfl⟩
    exact y.2
  have hWV₀ : W ≤ V₀ := by
    intro y hy
    rcases hy with ⟨y, hyT, rfl⟩
    have hyB : s.1 y ∈ B := hTsub hyT
    rcases hyB with ⟨hyV₀, _hys⟩
    have hbase : (s.1 y).base = y := congr_fun s.2.2 y
    simpa [hbase] using hyV₀
  let t : ToType (F.obj (op W)) := F.map (homOfLE hWV₀).op t₀
  refine ⟨W, hxW, homOfLE hWU, t, ?_⟩
  apply (EspaceEtale.presheafOfSections F).germ_ext W hxW
    (homOfLE hWU) (𝟙 W)
  apply Subtype.ext
  dsimp [EspaceEtale.presheafOfSections, TopCat.presheafOfSections,
    TopCat.sheafOfSections, subsheafToTypes, subpresheafToTypes]
  funext z
  rcases z with ⟨z, hzW⟩
  rcases hzW with ⟨zU, hzT, rfl⟩
  rcases hsz : s.1 zU with ⟨b, gb⟩
  change (⟨b, gb⟩ : F.EspaceEtale) =
    ⟨zU, F.germ W zU ⟨zU, hzT, rfl⟩ t⟩
  rw [EspaceEtale.mk.injEq]
  constructor
  · simpa [hsz] using congr_fun s.2.2 zU
  · dsimp [t]
    have hzB : (⟨b, gb⟩ : F.EspaceEtale) ∈ B := by
      simpa [hsz] using hTsub hzT
    rcases hzB with ⟨_hzV₀, hzgerm⟩
    have hbase : b = zU := by
      simpa [hsz] using congr_fun s.2.2 zU
    refine HEq.trans (heq_of_eq hzgerm) ?_
    cases hbase
    apply heq_of_eq
    simp [F.germ_res_apply (homOfLE hWV₀) zU ⟨zU, hzT, rfl⟩ t₀]

-- AI-generated; to be revised.
theorem EspaceEtale.morphism_app_injective_of_isSheaf (F : Presheaf C X)
    (hF : Presheaf.IsSheaf (F.comp (forget C))) (U : Opens X) :
    Function.Injective ((EspaceEtale.morphism F).app (op U)) := by
  intro s t hst
  apply TopCat.Presheaf.IsSheaf.section_ext hF
  intro x hx
  have hpoint := congr_fun (congr_arg Subtype.val hst) ⟨x, hx⟩
  change
    (⟨x, F.germ U x hx s⟩ : F.EspaceEtale) =
      ⟨x, F.germ U x hx t⟩ at hpoint
  simp only [EspaceEtale.mk.injEq, true_and] at hpoint
  rcases F.germ_eq x hx hx s t (eq_of_heq hpoint) with ⟨V, hxV, iVU, iVU', hV⟩
  refine ⟨V, iVU.le, hxV, ?_⟩
  convert hV

-- AI-generated; to be revised.
theorem EspaceEtale.morphismStalks_surjective (F : Presheaf C X) (x : X) :
    Function.Surjective (ConcreteCategory.hom (EspaceEtale.morphismStalks F x)) := by
  intro a
  rcases (EspaceEtale.presheafOfSections F).germ_exist x a with ⟨U, hxU, s, rfl⟩
  rcases EspaceEtale.exists_germ_eq_topSection F x hxU s with
    ⟨V, hxV, _iVU, t, ht⟩
  refine ⟨TopCat.Presheaf.germ (F.comp (forget C)) V x hxV t, ?_⟩
  change (ConcreteCategory.hom ((stalkFunctor (Type u) x).map (EspaceEtale.morphism F)))
    ((ConcreteCategory.hom (TopCat.Presheaf.germ (F.comp (forget C)) V x hxV)) t) =
      (ConcreteCategory.hom ((EspaceEtale.presheafOfSections F).germ U x hxU)) s
  rw [stalkFunctor_map_germ_apply]
  exact ht.symm

-- AI-generated; to be revised.
theorem EspaceEtale.morphismIsoOfSheaf (F : Presheaf C X)
    (hF : Presheaf.IsSheaf (F.comp (forget C))) : IsIso (EspaceEtale.morphism F) := by
  let F' : Sheaf (Type u) X := ⟨F.comp (forget C), hF⟩
  let G' : Sheaf (Type u) X :=
    TopCat.sheafOfSections
      (TopCat.ofHom ⟨EspaceEtale.base, EspaceEtale.continuous_base F⟩)
  let f : F' ⟶ G' := ObjectProperty.homMk (EspaceEtale.morphism F)
  haveI : ∀ x : X, IsIso ((stalkFunctor (Type u) x).map f.1) := by
    intro x
    rw [isIso_iff_bijective]
    constructor
    · simpa [f] using
        (stalkFunctor_map_injective_of_app_injective
          (C := Type u) (X := X) (f := EspaceEtale.morphism F)
          (EspaceEtale.morphism_app_injective_of_isSheaf F hF) x)
    · simpa [f, EspaceEtale.morphismStalks] using
        EspaceEtale.morphismStalks_surjective F x
  haveI : IsIso f := isIso_of_stalkFunctor_map_iso f
  have := Functor.map_isIso (Sheaf.forget (Type u) X) f
  simpa [f, F', G', EspaceEtale.presheafOfSections] using
    (show IsIso ((Sheaf.forget (Type u) X).map f) from inferInstance)


-- Define local predicates for primitives.

def primitivePrelocal
  (𝕜 : Type u_1) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (ω : E → E →L[𝕜] F) :
    PrelocalPredicate (X := TopCat.of E) (fun _ ↦ F) where
  pred {U} f := ∀ x : U, ∃ V : Opens E, ↑x ∈ V ∧ ∃ incl : V ⟶ U,
    ∃ G : E → F, (∀ z ∈ V, HasFDerivAt G (ω z) z) ∧
      ∀ y : V, G y = f ⟨y, incl.le y.2⟩
  res {U V} incl f hf := by
    intro x
    rcases hf ⟨x, incl.le x.2⟩ with ⟨W, hxW, i, G, hG_deriv, hG_eq⟩
    refine ⟨W ⊓ U, ⟨hxW, x.2⟩, homOfLE inf_le_right, G, ?_, ?_⟩
    · intro z hz
      exact hG_deriv z hz.1
    · intro z
      exact hG_eq ⟨z, z.2.1⟩

def primitiveLocal
  (𝕜 : Type u_1) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (ω : E → E →L[𝕜] F) :
    LocalPredicate (X := TopCat.of E) (fun _ ↦ F) where
  toPrelocalPredicate := primitivePrelocal 𝕜 ω
  locality := fun {U} φ hφ ↦ by
    simp [primitivePrelocal] at hφ ⊢
    intro x hx
    rcases hφ x hx with ⟨V, hxV, incl, hV⟩
    rcases hV x hxV with ⟨W, hxW, inclWV, G, hG_deriv, hG_eq⟩
    use W
    use hxW
    use inclWV ≫ incl
    use G
    constructor
    · exact hG_deriv
    · exact hG_eq

noncomputable def sheafOfPrimitives
  (𝕜 : Type u_1) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (ω : E → E →L[𝕜] F) : Sheaf (Type _) (TopCat.of E) :=
  subsheafToTypes (primitiveLocal 𝕜 ω)

noncomputable def presheafOfPrimitives
  (𝕜 : Type u_1) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (ω : E → E →L[𝕜] F) : Presheaf (Type _) (TopCat.of E) :=
  (sheafOfPrimitives 𝕜 ω).presheaf

-- AI-generated, may be useful API to keep?
-- May it hints to the fact that the definition of primitivePrelocal is suboptimal.
noncomputable def primitiveSectionOfPrimitive
  (𝕜 : Type) [NontriviallyNormedField 𝕜]
  {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (ω : E → E →L[𝕜] F) (U : Opens (TopCat.of E)) (G : E → F)
  (hG : ∀ z : E, z ∈ U → HasFDerivAt G (ω z) z) :
    (presheafOfPrimitives 𝕜 ω).obj (op U) :=
  ⟨fun z ↦ G z, by
    intro x
    refine ⟨U, x.2, 𝟙 U, G, ?_, ?_⟩
    · exact hG
    · intro y
      rfl⟩

-- AI-generated, may be useful API to keep? -- Not if definition of primitivePrelocal is changed?
@[simp]
theorem primitiveSectionOfPrimitive_apply
  (𝕜 : Type) [NontriviallyNormedField 𝕜]
  {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (ω : E → E →L[𝕜] F) (U : Opens (TopCat.of E)) (G : E → F)
  (hG : ∀ z : E, z ∈ U → HasFDerivAt G (ω z) z) (z : U) :
  (primitiveSectionOfPrimitive 𝕜 ω U G hG).1 z = G z :=
  rfl

-- see previous comment
noncomputable def primitiveSectionFunction
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (ω : E → E →L[ℝ] F) (U : Opens (TopCat.of E))
  (s : (presheafOfPrimitives ℝ ω).obj (op U)) : E → F :=
  fun z ↦ by
    classical
    exact if hz : z ∈ (U : Set E) then s.1 ⟨z, hz⟩ else 0

-- see previous comment
theorem primitiveSectionFunction_eq_on
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (ω : E → E →L[ℝ] F) (U : Opens (TopCat.of E))
  (s : (presheafOfPrimitives ℝ ω).obj (op U)) {z : E} (hz : z ∈ U) :
    primitiveSectionFunction ω U s z = s.1 ⟨z, hz⟩ := by
  classical
  simp [primitiveSectionFunction, hz]

-- see previous comment
theorem primitiveSectionFunction_hasFDerivAt
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (ω : E → E →L[ℝ] F) (U : Opens (TopCat.of E))
  (s : (presheafOfPrimitives ℝ ω).obj (op U)) {z : E} (hz : z ∈ U) :
    HasFDerivAt (primitiveSectionFunction ω U s) (ω z) z := by
  rcases s.2 ⟨z, hz⟩ with ⟨V, hzV, incl, G, hG, hGs⟩
  refine (hG z hzV).congr_of_eventuallyEq ?_
  filter_upwards [V.isOpen.mem_nhds hzV] with w hw
  rw [primitiveSectionFunction_eq_on]
  exact (hGs ⟨w, hw⟩).symm

-- that one has more content and is essential for proving that primitiveSheaf is a local system.
-- AI-generated, to be reviewed.
theorem primitive_sections_eq_of_eq_value_on_convex
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (ω : E → E →L[ℝ] F) {U : Opens (TopCat.of E)}
  (hU_convex : Convex ℝ (U : Set E))
  (s t : (presheafOfPrimitives ℝ ω).obj (op U))
  {y : E} (hy : y ∈ U) (hst : s.1 ⟨y, hy⟩ = t.1 ⟨y, hy⟩) : s = t := by
  apply Subtype.ext
  funext z
  let fs := primitiveSectionFunction ω U s
  let ft := primitiveSectionFunction ω U t
  have hconst :
      (fun x ↦ fs x - ft x) y = (fun x ↦ fs x - ft x) z := by
    refine hU_convex.is_const_of_fderivWithin_eq_zero
      (𝕜 := ℝ) (f := fun x ↦ fs x - ft x) ?_ ?_ hy z.2
    · intro x hx
      exact ((primitiveSectionFunction_hasFDerivAt ω U s hx).sub
        (primitiveSectionFunction_hasFDerivAt ω U t hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [fderivWithin_of_isOpen (𝕜 := ℝ) U.isOpen hx]
      have hderiv :
          fderiv ℝ (fun x ↦ fs x - ft x) x = ω x - ω x :=
        ((primitiveSectionFunction_hasFDerivAt ω U s hx).sub
          (primitiveSectionFunction_hasFDerivAt ω U t hx)).fderiv
      rw [hderiv]
      simp
  simp only at hconst
  change primitiveSectionFunction ω U s y - primitiveSectionFunction ω U t y =
    primitiveSectionFunction ω U s z - primitiveSectionFunction ω U t z at hconst
  rw [primitiveSectionFunction_eq_on ω U s hy,
    primitiveSectionFunction_eq_on ω U t hy,
    primitiveSectionFunction_eq_on ω U s z.2,
    primitiveSectionFunction_eq_on ω U t z.2] at hconst
  rw [hst, sub_self] at hconst
  exact sub_eq_zero.mp hconst.symm

-- AI-generated, to be reviewed.
theorem primitive_stalkToFiber_injective
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (ω : E → E →L[ℝ] F) (y : TopCat.of E) :
    Function.Injective (ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y)) := by
  apply TopCat.stalkToFiber_injective
  intro U V fU hU fV hV hval
  have hnhds : ((U.1 : Set E) ∩ (V.1 : Set E)) ∈ 𝓝 (y : E) :=
    inter_mem (U.1.isOpen.mem_nhds U.2) (V.1.isOpen.mem_nhds V.2)
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr, hr_sub⟩
  let W : OpenNhds y := ⟨⟨Metric.ball (y : E) r, Metric.isOpen_ball⟩, Metric.mem_ball_self hr⟩
  have hWU : W.1 ≤ U.1 := fun z hz ↦ (hr_sub hz).1
  have hWV : W.1 ≤ V.1 := fun z hz ↦ (hr_sub hz).2
  let sU : (presheafOfPrimitives ℝ ω).obj (op U.1) := ⟨fU, hU⟩
  let sV : (presheafOfPrimitives ℝ ω).obj (op V.1) := ⟨fV, hV⟩
  let sW : (presheafOfPrimitives ℝ ω).obj (op W.1) :=
    (presheafOfPrimitives ℝ ω).map (homOfLE hWU).op sU
  let tW : (presheafOfPrimitives ℝ ω).obj (op W.1) :=
    (presheafOfPrimitives ℝ ω).map (homOfLE hWV).op sV
  have hsame : sW.1 ⟨y, W.2⟩ = tW.1 ⟨y, W.2⟩ := by
    exact hval
  have hsections : sW = tW :=
    primitive_sections_eq_of_eq_value_on_convex ω (convex_ball (y : E) r) sW tW W.2 hsame
  refine ⟨W, homOfLE hWU, homOfLE hWV, ?_⟩
  intro w
  exact congr_fun (congr_arg Subtype.val hsections) w

theorem exists_primitive_on_convex_open_of_closed
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (ω : E → E →L[ℝ] F)
  (hω : DifferentiableOn ℝ ω Set.univ)
  (hω_symm : ∀ a x y, (fderiv ℝ ω a x) y = (fderiv ℝ ω a y) x)
  {U : Opens (TopCat.of E)} (hU_convex : Convex ℝ (U : Set E)) :
    ∃ G : E → F, ∀ z : E, z ∈ U → HasFDerivAt G (ω z) z :=
  hU_convex.exists_forall_hasFDerivAt_of_fderiv_symmetric U.isOpen
    (hω.mono (Set.subset_univ _)) (by
      intro a _ v w
      exact hω_symm a v w)

-- AI-generated, to be reviewed.
theorem sheafOfPrimitives_isLocalSystem
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (ω : E → E →L[ℝ] F)
  (hω : DifferentiableOn ℝ ω Set.univ)
  (hω_symm : ∀ a x y, (fderiv ℝ ω a x) y = (fderiv ℝ ω a y) x) :
    IsLocalSystem (sheafOfPrimitives ℝ ω).presheaf := by
  intro x
  let U : Opens (TopCat.of E) := ⟨Metric.ball (x : E) 1, Metric.isOpen_ball⟩
  have hU_convex : Convex ℝ (U : Set E) := convex_ball (x : E) 1
  rcases exists_primitive_on_convex_open_of_closed ω hω hω_symm hU_convex with ⟨G, hG⟩
  refine ⟨U, ?_, ?_⟩
  · exact Metric.mem_ball_self zero_lt_one
  · intro y hy
    constructor
    · intro s t hst
      have hval :=
        congr_arg (ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y)) hst
      have eval (u : (presheafOfPrimitives ℝ ω).obj (op U)) :
          (ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y))
            ((ConcreteCategory.hom ((presheafOfPrimitives ℝ ω).germ U y hy)) u) =
          u.1 ⟨y, hy⟩ := by
        simpa [presheafOfPrimitives, sheafOfPrimitives] using
          TopCat.stalkToFiber_germ (primitiveLocal ℝ ω) U y hy u
      exact primitive_sections_eq_of_eq_value_on_convex ω hU_convex s t hy
        ((eval s).symm.trans (hval.trans (eval t)))
    · intro g
      let c : F :=
        ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y) g
      let H : E → F := fun z ↦ G z + (c - G y)
      have hH : ∀ z : E, z ∈ U → HasFDerivAt H (ω z) z := by
        intro z hz
        exact (hG z hz).add_const _
      let s : (presheafOfPrimitives ℝ ω).obj (op U) :=
        primitiveSectionOfPrimitive ℝ ω U H hH
      refine ⟨s, ?_⟩
      apply primitive_stalkToFiber_injective ω y
      have hs_eval :
          (ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y))
            ((ConcreteCategory.hom ((presheafOfPrimitives ℝ ω).germ U y hy)) s) =
          s.1 ⟨y, hy⟩ := by
        simpa [presheafOfPrimitives, sheafOfPrimitives] using
          TopCat.stalkToFiber_germ (primitiveLocal ℝ ω) U y hy s
      change
        (ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y))
            ((ConcreteCategory.hom ((presheafOfPrimitives ℝ ω).germ U y hy)) s) =
          (ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y)) g
      rw [hs_eval]
      change H y = c
      simp [H, c]

-- AI-generated, to be reviewed. This should be implicit in the proof of
-- `sheafOfPrimitives_isLocalSystem`.
theorem primitive_stalk_nonempty_of_closed
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (ω : E → E →L[ℝ] F)
  (hω : DifferentiableOn ℝ ω Set.univ)
  (hω_symm : ∀ a x y, (fderiv ℝ ω a x) y = (fderiv ℝ ω a y) x)
  (x : TopCat.of E) :
    Nonempty (ToType ((presheafOfPrimitives ℝ ω).stalk x)) := by
  let U : Opens (TopCat.of E) := ⟨Metric.ball (x : E) 1, Metric.isOpen_ball⟩
  have hxU : x ∈ U := Metric.mem_ball_self zero_lt_one
  have hU_convex : Convex ℝ (U : Set E) := convex_ball (x : E) 1
  rcases exists_primitive_on_convex_open_of_closed ω hω hω_symm hU_convex with ⟨G, hG⟩
  exact ⟨TopCat.Presheaf.germ (presheafOfPrimitives ℝ ω) U x hxU
    (primitiveSectionOfPrimitive ℝ ω U G hG)⟩

-- AI-generated
theorem exists_global_primitive_of_closedOn
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {U : Set E} [SimplyConnectedSpace U] [LocPathConnectedSpace U]
  (hU_open : IsOpen U)
  (ω : E → E →L[ℝ] F)
  (hω : DifferentiableOn ℝ ω U)
  (hω_symm_on_U : ∀ a ∈ U, ∀ x y, (fderiv ℝ ω a x) y = (fderiv ℝ ω a y) x) :
    ∃ G : E → F, ∀ z : E, z ∈ U → HasFDerivAt G (ω z) z := by
  let X : TopCat := TopCat.of E
  let P : Presheaf Type X := presheafOfPrimitives ℝ ω
  have hP_local_on : ∀ x ∈ U, ∃ V : Opens X, x ∈ V ∧
      ∀ y (hy : y ∈ V), Bijective (P.germ V y hy) := by
    intro x hxU
    rcases Metric.isOpen_iff.mp hU_open x hxU with ⟨r, hr, hball_sub⟩
    let V : Opens X := ⟨Metric.ball x r, Metric.isOpen_ball⟩
    have hV_convex : Convex ℝ (V : Set E) := convex_ball x r
    rcases hV_convex.exists_forall_hasFDerivAt_of_fderiv_symmetric V.isOpen
        (hω.mono hball_sub) (by
          intro a ha v w
          exact hω_symm_on_U a (hball_sub ha) v w) with ⟨G, hG⟩
    refine ⟨V, Metric.mem_ball_self hr, ?_⟩
    intro y hy
    change Bijective ((presheafOfPrimitives ℝ ω).germ V y hy)
    constructor
    · intro s t hst
      have hval :=
        congr_arg (ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y)) hst
      have eval (u : (presheafOfPrimitives ℝ ω).obj (op V)) :
          (ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y))
            ((ConcreteCategory.hom ((presheafOfPrimitives ℝ ω).germ V y hy)) u) =
          u.1 ⟨y, hy⟩ := by
        simpa [presheafOfPrimitives, sheafOfPrimitives] using
          TopCat.stalkToFiber_germ (primitiveLocal ℝ ω) V y hy u
      exact primitive_sections_eq_of_eq_value_on_convex ω hV_convex s t hy
        ((eval s).symm.trans (hval.trans (eval t)))
    · intro g
      let c : F :=
        ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y) g
      let H : E → F := fun z ↦ G z + (c - G y)
      have hH : ∀ z : E, z ∈ V → HasFDerivAt H (ω z) z := by
        intro z hz
        exact (hG z hz).add_const _
      let s : (presheafOfPrimitives ℝ ω).obj (op V) :=
        primitiveSectionOfPrimitive ℝ ω V H hH
      refine ⟨s, ?_⟩
      apply primitive_stalkToFiber_injective ω y
      have hs_eval :
          (ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y))
            ((ConcreteCategory.hom ((presheafOfPrimitives ℝ ω).germ V y hy)) s) =
          s.1 ⟨y, hy⟩ := by
        simpa [presheafOfPrimitives, sheafOfPrimitives] using
          TopCat.stalkToFiber_germ (primitiveLocal ℝ ω) V y hy s
      change
        (ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y))
            ((ConcreteCategory.hom ((presheafOfPrimitives ℝ ω).germ V y hy)) s) =
          (ConcreteCategory.hom (TopCat.stalkToFiber (primitiveLocal ℝ ω) y)) g
      rw [hs_eval]
      change H y = c
      simp [H, c]
  have hcover_on : IsCoveringMapOn (EspaceEtale.base (F := P)) U :=
    EspaceEtale.isCoveringMapOn_base (F := P) hP_local_on
  let Uop : Opens X := ⟨U, hU_open⟩
  have hne : Nonempty U := (simply_connected_iff_unique_homotopic U).mp inferInstance |>.1
  let x₀ : U := Classical.choice hne
  let sx : ToType (P.stalk (x₀ : E)) :=
    Classical.choice (by
      rcases Metric.isOpen_iff.mp hU_open (x₀ : E) x₀.2 with ⟨r, hr, hball_sub⟩
      let V : Opens X := ⟨Metric.ball (x₀ : E) r, Metric.isOpen_ball⟩
      have hxV : (x₀ : E) ∈ V := Metric.mem_ball_self hr
      have hV_convex : Convex ℝ (V : Set E) := convex_ball (x₀ : E) r
      rcases hV_convex.exists_forall_hasFDerivAt_of_fderiv_symmetric V.isOpen
          (hω.mono hball_sub) (by
            intro a ha v w
            exact hω_symm_on_U a (hball_sub ha) v w) with ⟨G, hG⟩
      exact ⟨TopCat.Presheaf.germ (presheafOfPrimitives ℝ ω) V (x₀ : E) hxV
        (primitiveSectionOfPrimitive ℝ ω V G hG)⟩)
  let e₀ : P.EspaceEtale := ⟨(x₀ : E), sx⟩
  let incl : C(U, X) := ⟨fun z ↦ (z : E), continuous_subtype_val⟩
  rcases hcover_on.existsUnique_continuousMap_lifts incl
      (a₀ := x₀) (e₀ := e₀) (by simp [e₀, incl]) (fun z ↦ z.2) with
    ⟨σ, hσ, _hσ_unique⟩
  let σsec : (EspaceEtale.presheafOfSections P).obj (op Uop) :=
    ⟨fun x : Uop ↦ σ (⟨x.1, x.2⟩ : U), ⟨by
      exact σ.continuous.comp (by fun_prop)
    , by
      funext x
      change EspaceEtale.base (σ (⟨x.1, x.2⟩ : U)) = x.1
      simpa [incl] using congr_fun hσ.2 (⟨x.1, x.2⟩ : U)⟩⟩
  have hP_sheaf : P.IsSheaf := by
    simpa [P, presheafOfPrimitives] using (sheafOfPrimitives ℝ ω).2
  haveI : IsIso (EspaceEtale.morphism P) :=
    EspaceEtale.morphismIsoOfSheaf P hP_sheaf
  let sU : (presheafOfPrimitives ℝ ω).obj (op Uop) :=
    (inv (EspaceEtale.morphism P)).app (op Uop) σsec
  refine ⟨primitiveSectionFunction ω Uop sU, ?_⟩
  intro z hz
  exact primitiveSectionFunction_hasFDerivAt ω Uop sU hz

-- AI-generated
theorem exists_global_primitive_of_holomorphic
    {U : Set ℂ} [LocPathConnectedSpace U]
    (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U)
    (hU_open : IsOpen U)
    (hU_sc : IsSimplyConnected U) :
    ∃ G : ℂ → ℂ, ∀ z : ℂ, z ∈ U → HasDerivAt G (f z) z := by
  classical
  let ω : ℂ → ℂ →L[ℝ] ℂ := fun z ↦ f z • (1 : ℂ →L[ℝ] ℂ)
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    ContinuousLinearMap.smulRight (1 : ℂ →L[ℝ] ℂ) (1 : ℂ →L[ℝ] ℂ)
  have hω : DifferentiableOn ℝ ω U := by
    change DifferentiableOn ℝ (fun z ↦ L (f z)) U
    intro z hz
    have hfz : DifferentiableAt ℂ f z :=
      (hf z hz).differentiableAt (hU_open.mem_nhds hz)
    have hfr : DifferentiableAt ℝ f z :=
      (differentiableAt_complex_iff_differentiableAt_real.mp hfz).1
    exact (L.differentiableAt.comp z hfr).differentiableWithinAt
  have hω_symm_on_U : ∀ a ∈ U, ∀ x y,
      (fderiv ℝ ω a x) y = (fderiv ℝ ω a y) x := by
    intro a ha x y
    have hfa : DifferentiableAt ℂ f a :=
      (hf a ha).differentiableAt (hU_open.mem_nhds ha)
    have hfr : DifferentiableAt ℝ f a :=
      (differentiableAt_complex_iff_differentiableAt_real.mp hfa).1
    have hCRf : fderiv ℝ f a Complex.I = Complex.I • fderiv ℝ f a 1 :=
      (differentiableAt_complex_iff_differentiableAt_real.mp hfa).2
    have hdf (v : ℂ) : fderiv ℝ f a v = v * fderiv ℝ f a 1 := by
      calc
        fderiv ℝ f a v = ((fderiv ℝ f a).complexOfReal hCRf) v := rfl
        _ = v • ((fderiv ℝ f a).complexOfReal hCRf) 1 := by
          rw [← map_smul]
          simp
        _ = v * fderiv ℝ f a 1 := by
          simp [smul_eq_mul]
    change ((fderiv ℝ (L ∘ f) a) x) y = ((fderiv ℝ (L ∘ f) a) y) x
    rw [(L.hasFDerivAt.comp a hfr.hasFDerivAt).fderiv]
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hdf x, hdf y]
    simp [L, mul_left_comm, mul_comm]
  haveI : SimplyConnectedSpace U := hU_sc.simplyConnectedSpace
  rcases exists_global_primitive_of_closedOn hU_open ω hω hω_symm_on_U with
    ⟨G, hG⟩
  refine ⟨G, ?_⟩
  intro z hz
  have hreal : HasFDerivAt G (ω z) z := hG z hz
  have hCR : (ω z) Complex.I = Complex.I • (ω z) 1 := by
    dsimp [ω]
    ring
  have hder := (hreal.complexOfReal_hasFDerivAt hCR).hasDerivAt
  convert hder using 1
  dsimp [ω]
  simp

end TopCat.Presheaf
