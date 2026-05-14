import Mathlib
import Mathlib.Tactic.CompactSet.Attr




-- def P {α} (_s : Set α) : Prop := True

-- def set1 {α} (_a : α) : Set α := fun _ ↦ False
-- def set2 {α} (_a : α) : Set α := fun _ ↦ False

-- @[grind =]
-- theorem closure_set1 (a : ℝ) : closure (set1 a) = set1 a := by
--   sorry

-- @[grind .]
-- theorem P_set1 {a : ℝ} : P (set1 a) := by trivial

-- #guard_msgs in
-- example (a : ℝ) : P (closure (set1 a)) := by grind

-- @[grind .]
-- theorem P_closure_set2 {a : ℝ} : P (closure (set2 a)) := by trivial

-- -- #help cats
-- -- set_option trace.grind.ematch true
-- example (a : ℝ) : P (closure (set1 a)) := by grind


section

open Lean Meta Elab Tactic


private def tacticToDischarge' (tacticCode : Syntax) : TacticM (IO.Ref Term.State × (Expr → MetaM (Option Expr))) := do
  let tacticCode : TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨tacticCode⟩
  let tacticCode ← `(tactic| try ($tacticCode:tacticSeq))
  let ref ← IO.mkRef (← getThe Term.State)
  let ctx ← readThe Term.Context
  let disch : Expr → MetaM (Option Expr) := fun e => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `simp.discharger
    let s ← ref.get
    let runTac? : TermElabM (Option Expr) :=
      try
        /- We must only save messages and info tree changes. Recall that `simp` uses temporary metavariables (`withNewMCtxDepth`).
            So, we must not save references to them at `Term.State`.
        -/
        Term.withoutModifyingElabMetaStateWithInfo do
          Term.withSynthesize (postpone := .no) do
            Term.runTactic (report := false) mvar.mvarId! tacticCode .term
          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            return none
          else
            return some result
      catch _ =>
        return none
    let (result?, s) ← Term.TermElabM.run runTac? ctx s
    ref.set s
    return result?
  return (ref, disch)

syntax (name:=runAutoParamStx) "run_auto_param" : tactic

@[tactic runAutoParamStx]
def runAutoParam : Tactic := fun _ => do

  let goal ← getMainGoal
  let type ← goal.getType

  let some (.const tacticDecl _) := type.getAutoParamTactic?
    | return ()
  let type := type.appFn!.appArg!

  let env ← getEnv
  let opts ← getOptions
  let .ok tacticSyntax := evalSyntaxConstant env  opts tacticDecl
    | return ()

  let (_, disch) ← tacticToDischarge' tacticSyntax

  let some prf ← disch type
    | return ()

  goal.assign prf

end

open MeasureTheory TopologicalSpace Set

-- def compactness := 1
section Tac
open Lean Parser Tactic
/--
A simple tactic that tries various lemmas to prove that a set is compact.
The explicitly marked lemmas are a temporary workaround to
https://github.com/leanprover/lean4/issues/13725. -/
macro "compactness" config:optConfig : tactic =>
  let attr : Ident := mkIdent `compactness
  `(tactic|grind $config only [$attr:term, isCompact_Icc, Ici_inter_Iic])

end Tac
/- maybe:
IsCompact.of_isClosed_subset
-/

-- workaround to https://github.com/leanprover/lean4/issues/13725
-- attribute [compactness .] isCompact_Icc
-- attribute [compactness =] Ici_inter_Iic

-- grind_pattern [compactness] IsCompact.inter_right => IsCompact (s ∩ t) where
--   check IsCompact s
-- grind_pattern [compactness] IsCompact.inter_right => IsCompact (s ∩ t), IsClosed t
-- grind_pattern [compactness] IsCompact.inter_left => IsCompact (s ∩ t), IsCompact t
-- grind_pattern [compactness] IsCompact.inter_left => IsCompact (s ∩ t), IsClosed s
-- grind_pattern [compactness] IsCompact.inter => IsCompact (s ∩ t), IsCompact t where
--   check IsCompact s
-- grind_pattern [compactness] IsCompact.inter => IsCompact (s ∩ t), IsCompact s
-- grind_pattern [compactness] IsCompact.insert => IsCompact (insert a s)

attribute [compactness .] IsCompact.isClosed

set_option diagnostics true in
example (s : Set ℝ) (h : IsCompact s) : IsClosed s ∧ IsOpen s := by compactness

attribute [compactness .] isCompact_Icc IsCompact.inter

lemma IsOpen.compl {α : Type*} [TopologicalSpace α] {s : Set α} (h : IsOpen s := by compactness) :
    IsClosed sᶜ :=
  h.isClosed_compl

@[grind .]
lemma IsCompact.isClosed' {α : Type*} [TopologicalSpace α] [T2Space α] {s : Set α}
    (h : IsCompact s := by compactness) : IsClosed s :=
  h.isClosed


example (a b c d : ℝ) : IsClosed (Icc a b ∩ Icc c d) := by
  apply IsCompact.isClosed'



attribute [compactness .]  IsCompact.union IsCompact.diff
  IsCompact.image_of_continuousOn Continuous.continuousOn isCompact_closedBall isCompact_sphere
attribute [compactness =] closure_Icc
attribute [compactness] IsClosed.closure_eq
attribute [compactness .]
  IsCompact.prod isCompact_univ isCompact_empty isCompact_singleton
  IsCompact.inter_left --  IsCompact.inter_left IsCompact.inter
attribute [compactness .] isClosed_Icc isClosed_Ici isClosed_Iic isClosed_univ IsCompact.isClosed
  IsCompact.closure IsCompact.insert
attribute [compactness →] Set.Finite.isCompact

lemma isClosed_uIcc {α : Type*} [TopologicalSpace α] [Lattice α] [OrderClosedTopology α] {a b : α} :
  IsClosed (uIcc a b) := isClosed_Icc

@[simp, compactness =]
lemma closure_uIcc {α : Type*} [TopologicalSpace α] [Lattice α] [OrderClosedTopology α] {a b : α} :
  closure (uIcc a b) = uIcc a b := isClosed_uIcc.closure_eq

@[compactness .]
lemma IsCompact_closure_uIoc
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [DenselyOrdered α]
    [CompactIccSpace α] {a b : α} : IsCompact (closure (uIoc a b)) := by
  obtain rfl|h := eq_or_ne a b
  · simp
  · simp [h, isCompact_uIcc]

@[compactness .]
lemma IsCompact_closure_Ioc
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [DenselyOrdered α]
    [CompactIccSpace α] {a b : α} : IsCompact (closure (Ioc a b)) := by
  obtain rfl|h := eq_or_ne a b
  · simp
  · simp [h, isCompact_Icc]

@[compactness .]
lemma IsCompact_closure_Ico
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [DenselyOrdered α]
    [CompactIccSpace α] {a b : α} : IsCompact (closure (Ico a b)) := by
  obtain rfl|h := eq_or_ne a b
  · simp
  · simp [h, isCompact_Icc]

@[compactness .]
lemma IsCompact_closure_Ioo
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [DenselyOrdered α]
    [CompactIccSpace α] {a b : α} : IsCompact (closure (Ioo a b)) := by
  obtain rfl|h := eq_or_ne a b
  · simp
  · simp [h, isCompact_Icc]

@[compactness .]
lemma IsCompact_closure_ball
    {α : Type*} [PseudoMetricSpace α] [ProperSpace α] {x : α} {ε : ℝ} :
    IsCompact (closure (Metric.ball x ε)) :=
  Metric.isBounded_ball.isCompact_closure


example : IsCompact <| Icc (1 : ℝ) (3 : ℝ) := by compactness
example : IsCompact <| closure (Ioo (1 : ℝ) (3 : ℝ)) := by compactness
example : IsCompact <| closure (Icc (1 : ℝ) (3 : ℝ)) := by compactness
example : closure (Icc (1 : ℝ) (3 : ℝ)) = Icc (1 : ℝ) (3 : ℝ) := by compactness
example : IsCompact <| closure (uIoc (1 : ℝ) (3 : ℝ)) := by compactness
example : IsCompact <| closure (Metric.ball (0 : Fin 5 → ℝ) 7) := by compactness
example : IsCompact <| closure (Metric.closedBall (0 : Fin 5 → ℝ) 7) := by compactness
example : IsCompact <| Metric.closedBall (0 : Fin 5 → ℝ) 7 := by compactness
example : IsCompact <| Metric.closedBall (0 : Fin 5 → ℝ) 7 := by compactness
example (x : EuclideanSpace ℝ (Fin 4)) : IsCompact <| closure (Metric.ball x 7) := by compactness

set_option maxHeartbeats 10000 in
set_option diagnostics true in
example {a b c : ℝ} : IsCompact (Icc a b ∩ Ici c ∩ Iic b ∩ Ici c ∩ Icc a b ∩ Ici c ∩ Icc a b ∩
    Ici c ∩ Icc a b ∩ Ici c ∩ Icc a b ∩ Ici c ∩ Icc a b ∩ Ici c) := by
  compactness (ematch := 30) (gen := 30)


-- lemma Icc_inter_Ici {a b c : ℝ} : Icc a b ∩ Ici c = Icc (max a c) b := by exact? --ext; grind
example {a b c : ℝ} : IsCompact (Icc a b ∩ Ici c) := by compactness
example {a b c d : ℝ} : IsCompact (Icc a b ∩ Icc c d) := by compactness
example {a b c d : ℝ} : IsCompact (closure (Icc a b ∩ Icc c d)) := by compactness
example {a b : ℝ} : IsCompact (closure (Ici a ∩ Iic b)) := by compactness
example : IsCompact {0} := by compactness
example {a b c : ℝ} : IsCompact {a, b, c} := by compactness
example {a b c d e : ℝ} : IsCompact {a, b, c, d, e} := by compactness
example {s : Set ℝ} (h : s.Finite) : IsCompact s := by compactness



attribute [fun_prop] LocallyIntegrableOn
attribute [fun_prop] LocallyIntegrableOn.enorm ContinuousOn.locallyIntegrableOn

attribute [fun_prop] LocallyIntegrable
attribute [fun_prop] LocallyIntegrable.locallyIntegrableOn --Continuous.locallyIntegrable

attribute [fun_prop] IntegrableOn

attribute [fun_prop] IntervalIntegrable
@[fun_prop] alias ⟨_, FunProp.intervalIntegrable_intro⟩ := intervalIntegrable_iff

theorem FunProp.ContinuousOn.locallyIntegrableOn {X E : Type*} [MeasurableSpace X]
    [TopologicalSpace X]
    [NormedAddCommGroup E] {μ : Measure X} [OpensMeasurableSpace X] {K : Set X} {f : X → E} [IsLocallyFiniteMeasure μ]
    [SecondCountableTopologyEither X E] (hf : ContinuousOn f K)
    (hK : MeasurableSet K := by measurability) : LocallyIntegrableOn f K μ :=
  hf.locallyIntegrableOn hK

@[fun_prop]
theorem FunProp.LocallyIntegrableOn.integrableOn_isCompact {X ε : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [TopologicalSpace ε] [ContinuousENorm ε]
    {f : X → ε} {μ : Measure X} {s : Set X}
    [PseudoMetrizableSpace ε] (hf : LocallyIntegrableOn f (closure s) μ)
    (hs : IsCompact (closure s) := by compactness) :
    IntegrableOn f s μ :=
  (hf.integrableOn_isCompact hs).mono_set subset_closure


set_option trace.Meta.Tactic.fun_prop true
example (f : ℝ → ℝ) (hf : Continuous f) : IntegrableOn f (Icc 1 3) := by
  fun_prop (maxTransitionDepth := 3) (disch := first | compactness | measurability)

example (f : ℝ → ℝ) (hf : Continuous f) : IntervalIntegrable f volume 1 3 := by
  fun_prop (maxTransitionDepth := 4) (disch := first | compactness | measurability)

example (f : ℝ → ℝ) (hf : Continuous f) : IntervalIntegrable (fun x ↦ f x) volume 1 3 := by
  fun_prop (maxTransitionDepth := 4) (disch := first | compactness | measurability)

example (f g : ℝ → ℝ) (hf : Continuous f) (hf : Continuous g) :
    IntervalIntegrable (f + g) volume 1 3 := by
  fun_prop (maxTransitionDepth := 4) (disch := first | compactness | measurability)

example (f g : ℝ → ℝ) (hf : Continuous f) (hf : Continuous g) :
    IntervalIntegrable (g ∘ f) volume 1 3 := by
  fun_prop (maxTransitionDepth := 4) (disch := first | compactness | measurability)

example (f g : ℝ → ℝ) (hf : Continuous f) (hf : Continuous g) :
    IntervalIntegrable (fun x ↦ f x + g x) volume 1 3 := by
  fun_prop (maxTransitionDepth := 4) (disch := first | compactness | measurability)

example (f g : ℝ → ℝ) (hf : Continuous f) (hf : Continuous g) :
    IntervalIntegrable (f * g) volume 1 3 := by
  fun_prop (maxTransitionDepth := 4) (disch := first | compactness | measurability)

example (f g : ℝ → ℝ) (hf : Continuous f) (hf : Continuous g) :
    IntervalIntegrable (fun x ↦ f x * g x) volume 1 3 := by
  fun_prop (maxTransitionDepth := 4) (disch := first | compactness | measurability)

example (a b : ℝ) : IntegrableOn (fun x : ℝ => (Real.sin x : ℂ)) (Icc a b) := by
  fun_prop (maxTransitionDepth := 4) (disch := first | compactness | measurability)
