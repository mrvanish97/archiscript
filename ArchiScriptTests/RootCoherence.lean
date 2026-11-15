import ArchiScript.Consequence

/-!
Single-event context regressions over one independent primitive graph.
Both Causes have the same Boolean VDP, but retain distinct source identities.
`false` is the designated root of each Cause; raw terms can still mention `true`.

The draft model tests supported input contexts and their Cone consequences only.
Its empty effect-analysis entries and permissive contracts are unchecked: no
`InputValid`, complete Effect, or `CertifiedDeclaredArchitecture` is claimed.
-/
namespace ArchiScriptTests.RootCoherence
open ArchiScript

abbrev bit : VDP := Partition.closed Bool "Bit"
  ⟨[false, true], by intro b; cases b <;> simp⟩ ⟨false⟩

inductive Cause where
  | local | external
  deriving DecidableEq

inductive Port where
  | localSource | externalSource | shared | externalResult | result
  deriving DecidableEq

inductive Arrow where
  | left | right | directJoin | fanoutJoin | externalJoin | crossJoin
  deriving DecidableEq

abbrev signature : ArchitectureSignature where
  Node := Port
  nodeDecidableEq := inferInstance
  nodes := [.localSource, .externalSource, .shared, .externalResult, .result]
  nodes_complete := by intro n; cases n <;> simp
  nodes_nodup := by decide
  object := fun _ => bit
  domains := [⟨Bool, bit.members false⟩, ⟨Bool, bit.members true⟩]
  memberDeclared := by intro _ b; cases b <;> simp
  splits := []
  Cause := Cause
  causeDecidableEq := inferInstance
  causes := [.local, .external]
  causes_complete := by intro c; cases c <;> simp
  causes_nodup := by decide
  RootInstance := Bool
  rootDecidableEq := inferInstance
  origin := fun _ => false
  start | .local => .localSource | .external => .externalSource
  owner | .externalSource | .externalResult => .external | _ => .local
  start_owner := by intro c; cases c <;> rfl
  Generator := Arrow
  generatorDecidableEq := inferInstance
  generators := [.left, .right, .directJoin, .fanoutJoin, .externalJoin, .crossJoin]
  generators_complete := by intro g; cases g <;> simp
  input
    | .left | .right => .node .localSource
    | .directJoin => .tensor (.node .localSource) (.node .localSource)
    | .fanoutJoin => .tensor (.node .shared) (.node .shared)
    | .externalJoin => .tensor (.node .externalSource) (.node .externalSource)
    | .crossJoin => .tensor (.node .localSource) (.node .externalResult)
  output
    | .left | .right => .shared
    | .externalJoin => .externalResult
    | .directJoin | .fanoutJoin | .crossJoin => .result
  operation
    | .left | .right => Operation.id bit
    | .externalJoin => ⟨fun pair => some pair.1⟩
    | .directJoin | .fanoutJoin | .crossJoin => ⟨fun pair => some (xor pair.1 pair.2)⟩
  localFactor := by
    intro g
    cases g with
    | left => exact ⟨.localSource, by simp [Inputs.nodes], rfl⟩
    | right => exact ⟨.localSource, by simp [Inputs.nodes], rfl⟩
    | directJoin => exact ⟨.localSource, by simp [Inputs.nodes], rfl⟩
    | fanoutJoin => exact ⟨.shared, by simp [Inputs.nodes], rfl⟩
    | externalJoin => exact ⟨.externalSource, by simp [Inputs.nodes], rfl⟩
    | crossJoin => exact ⟨.localSource, by simp [Inputs.nodes], rfl⟩

abbrev model : DeclaredArchitecture where
  signature := signature
  boundary := fun _ => True
  boundaryNonempty := ⟨fun _ root => root, trivial⟩
  context := fun _ _ _ => True
  admissibleInput := fun _ _ _ => True
  cyclicBoundary := fun _ => none
  effectAnalysis := { roots := [false], entries := [] }
  effectContext := fun _ _ _ => True
  admissibleEffect := fun _ _ => True

def localEvent (root : Bool) : signature.Occurrence (.node .localSource) :=
  ArchitectureSignature.Term.cause (S := signature) .local root

def externalEvent (root : Bool) : signature.Occurrence (.node .externalSource) :=
  ArchitectureSignature.Term.cause (S := signature) .external root

def rootSensitiveWorld : signature.World := fun _ root => root

/- The original counterexample remains a well-typed raw term. -/
def mixedInput : signature.Occurrence (signature.input .directJoin) :=
  ArchitectureSignature.Term.tensor (S := signature) (localEvent false) (localEvent true)

def mixedResult : signature.Occurrence (.node .result) :=
  ArchitectureSignature.Term.operation (S := signature) .directJoin mixedInput

theorem mixed_input_not_context : ¬ model.isInputContext .directJoin mixedInput := by
  intro supported
  have coherent := (model.isInputContext_iff_coherent .directJoin mixedInput).mp supported
  have impossible : true = false := coherent.2
  cases impossible

theorem mixed_result_not_inCone : ¬ model.InCone .local mixedResult := by
  intro supported
  have impossible : true = false := supported.2.2
  cases impossible

-- Merely containing the designated root was not a sufficient acceptance guard.
example : mixedResult.hasRoot Cause.local false := Or.inl ⟨rfl, rfl⟩
example : model.evaluate rootSensitiveWorld mixedInput = some (false, true) := rfl
example : model.evaluate rootSensitiveWorld mixedResult = some true := by
  simp [DeclaredArchitecture.evaluate, model, mixedResult, mixedInput, localEvent,
    rootSensitiveWorld, signature]

/- Two real producer paths from the SAME canonical occurrence remain valid. -/
def leftTrace : signature.Occurrence (.node .shared) :=
  ArchitectureSignature.Term.operation (S := signature) .left (localEvent false)

def rightTrace : signature.Occurrence (.node .shared) :=
  ArchitectureSignature.Term.operation (S := signature) .right (localEvent false)

def fanoutInput : signature.Occurrence (signature.input .fanoutJoin) :=
  ArchitectureSignature.Term.tensor (S := signature) leftTrace rightTrace

def fanoutResult : signature.Occurrence (.node .result) :=
  ArchitectureSignature.Term.operation (S := signature) .fanoutJoin fanoutInput

theorem fanout_provenance_distinct :
    leftTrace.provenance (fun _ => none) ≠ rightTrace.provenance (fun _ => none) := by
  decide

theorem fanout_same_origin :
    leftTrace.hasRoot Cause.local false ∧ rightTrace.hasRoot Cause.local false :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem fanout_context : model.isInputContext .fanoutJoin fanoutInput :=
  (model.isInputContext_iff_coherent .fanoutJoin fanoutInput).mpr (by decide)

theorem fanout_consequence : model.InCone .local fanoutResult :=
  model.input_consequence_inCone .fanoutJoin fanoutInput fanout_context

-- Equal values do not merge the producer histories or make the tensor full Reach.
theorem fanout_evaluation (w : signature.World) :
    model.evaluate w fanoutInput = some (w .local false, w .local false) := by
  simp [DeclaredArchitecture.evaluate, model, fanoutInput, leftTrace, rightTrace,
    localEvent, signature, Operation.id]

/- Distinct Causes can supply an explicit cross-Cone join despite equal VDPs. -/
def externalInput : signature.Occurrence (signature.input .externalJoin) :=
  ArchitectureSignature.Term.tensor (S := signature) (externalEvent false) (externalEvent false)

def externalProducer : signature.Occurrence (.node .externalResult) :=
  ArchitectureSignature.Term.operation (S := signature) .externalJoin externalInput

def crossInput : signature.Occurrence (signature.input .crossJoin) :=
  ArchitectureSignature.Term.tensor (S := signature) (localEvent false) externalProducer

def crossResult : signature.Occurrence (.node .result) :=
  ArchitectureSignature.Term.operation (S := signature) .crossJoin crossInput

example : signature.object (signature.start .local) =
    signature.object (signature.start .external) := rfl

theorem causes_provenance_distinct :
    (localEvent false).provenance (fun _ => none) ≠
      (externalEvent false).provenance (fun _ => none) := by
  decide

theorem cross_context : model.isInputContext .crossJoin crossInput :=
  (model.isInputContext_iff_coherent .crossJoin crossInput).mpr (by decide)

theorem cross_consequence : model.InCone .local crossResult :=
  model.input_consequence_inCone .crossJoin crossInput cross_context

theorem external_consequence : model.InCone .external externalProducer :=
  model.input_consequence_inCone .externalJoin externalInput
    ((model.isInputContext_iff_coherent .externalJoin externalInput).mpr (by decide))

theorem cross_evaluation (w : signature.World) :
    model.evaluate w crossInput = some (w .local false, w .external false) := by
  simp [DeclaredArchitecture.evaluate, model, crossInput, externalProducer,
    externalInput, localEvent, externalEvent, signature]

/- An owner's coherent local factor cannot hide another Cause's mixed roots. -/
def nestedExternalInput : signature.Occurrence (signature.input .externalJoin) :=
  ArchitectureSignature.Term.tensor (S := signature) (externalEvent false) (externalEvent true)

def nestedExternalProducer : signature.Occurrence (.node .externalResult) :=
  ArchitectureSignature.Term.operation (S := signature) .externalJoin nestedExternalInput

def nestedInput : signature.Occurrence (signature.input .crossJoin) :=
  ArchitectureSignature.Term.tensor (S := signature) (localEvent false) nestedExternalProducer

def nestedResult : signature.Occurrence (.node .result) :=
  ArchitectureSignature.Term.operation (S := signature) .crossJoin nestedInput

theorem nested_external_mixes_roots :
    nestedExternalProducer.hasRoot Cause.external false ∧
      nestedExternalProducer.hasRoot Cause.external true :=
  ⟨Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

-- Both the old local-factor witness and a guard on ONLY the owner's roots pass.
theorem nested_owner_only_guard :
    nestedInput.onlyLocalRoot Cause.local ∧
      ∃ i, model.InCone .local (nestedInput.supplier i) := by
  constructor
  · simp [nestedInput, nestedExternalProducer, nestedExternalInput, localEvent,
      externalEvent, ArchitectureSignature.Term.onlyLocalRoot, signature]
  · exact ⟨.inl (), ⟨⟨rfl, rfl⟩, rfl⟩⟩

theorem nested_input_not_context : ¬ model.isInputContext .crossJoin nestedInput := by
  intro supported
  have coherent := (model.isInputContext_iff_coherent .crossJoin nestedInput).mp supported
  have impossible : true = false := coherent.2.2
  cases impossible

theorem nested_result_not_inCone : ¬ model.InCone .local nestedResult := by
  intro supported
  have impossible : true = false := supported.2.2.2
  cases impossible

-- The ignored noncanonical factor even leaves the raw input values unchanged.
-- Acceptance must depend on full source provenance, not just equal evaluations.
example (w : signature.World) :
    model.evaluate w nestedInput = model.evaluate w crossInput := by
  simp [DeclaredArchitecture.evaluate, model, nestedInput, nestedExternalProducer,
    nestedExternalInput, crossInput, externalProducer, externalInput, localEvent,
    externalEvent, signature]

/- Root caches enumerate designated origins, not every raw RootInstance value. -/
theorem designated_origins_enumerated (c : Cause) :
    signature.origin c ∈ model.effectAnalysis.roots := List.mem_cons_self

example : true ∉ model.effectAnalysis.roots := by decide

example (c : Cause) : signature.rootHistories [false, true] c .localSource =
    [ProducerHistory.cause .local false] := by cases c <;> decide

example (c : Cause) : signature.rootHistories [false, true] c .externalSource =
    [ProducerHistory.cause .external false] := by cases c <;> decide

end ArchiScriptTests.RootCoherence
