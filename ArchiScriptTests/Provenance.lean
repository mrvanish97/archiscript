import ArchiScript

namespace ArchiScriptTests.Provenance
open ArchiScript
abbrev bit : VDP := Partition.closed Bool "Boolean" ⟨[false, true], by intro b; cases b <;> simp⟩ ⟨false⟩
inductive Source where | local | one | two deriving DecidableEq
abbrev signature : ArchitectureSignature where
  Node := Source
  nodeDecidableEq := inferInstance
  nodes := [.local, .one, .two]
  nodes_complete := by intro n; cases n <;> simp
  nodes_nodup := by decide
  object := fun _ => bit
  domains := [⟨Bool, bit.members false⟩, ⟨Bool, bit.members true⟩]
  memberDeclared := by intro n i; cases n <;> cases i <;> simp
  splits := []
  Cause := Source
  causeDecidableEq := inferInstance
  causes := [.local, .one, .two]
  causes_complete := by intro c; cases c <;> simp
  causes_nodup := by decide
  RootInstance := Bool
  rootDecidableEq := inferInstance
  origin := fun _ => false
  start := id
  owner := id
  start_owner := fun _ => rfl
  Generator := Bool
  generatorDecidableEq := inferInstance
  generators := [false, true]
  generators_complete := by intro g; cases g <;> simp
  input
    | false => .tensor (.node .local) (.tensor (.node .one) (.node .two))
    | true => .node .one
  output | false => .local | true => .one
  operation
    | false => ⟨fun triple => some triple.1⟩
    | true => ⟨fun b => some (!b)⟩
  localFactor := by
    intro g; cases g
    · exact ⟨.local, by simp [Inputs.nodes], rfl⟩
    · exact ⟨.one, List.mem_cons_self, rfl⟩

def frozen : signature.World := fun _ root => root
def contract (tuple : Bool × (Bool × Bool)) : Prop := tuple = (false, true, false)

/-- Deliberately draft: the same contract passes one context and fails another.
No Cone Effect or complete architecture certificate is claimed. -/
abbrev model : DeclaredArchitecture where
  signature := signature
  boundary := fun w => ∀ c root, w c root = root
  boundaryNonempty := ⟨frozen, fun _ _ => rfl⟩
  context := fun _ _ _ => True
  admissibleInput
    | false => fun _ => contract
    | true => fun _ _ => True
  cyclicBoundary := fun _ => none
  effectAnalysis := ⟨[false, true], []⟩
  effectContext := fun _ _ _ => True
  admissibleEffect := fun _ _ => False

abbrev root (source : Source) (instanceId : Bool) : signature.Occurrence (.node source) :=
  ArchitectureSignature.Term.cause (S := signature) source instanceId
abbrev inputs (external : Bool) : signature.Occurrence (signature.input false) :=
  .tensor (root .local false)
    (.tensor (if external then ArchitectureSignature.Term.operation (S := signature) true (root .one false)
      else root .one false) (root .two false))
abbrev good := inputs true
abbrev bad := inputs false
abbrev goodTuple : Bool × (Bool × Bool) := (false, true, false)
abbrev badTuple : Bool × (Bool × Bool) := (false, false, false)

theorem world_unique (w : signature.World) (allowed : model.boundary w) : w = frozen := by
  funext c instanceId; exact allowed c instanceId

theorem context_is_local (external : Bool) : model.isInputContext false (inputs external) := by
  apply (model.isInputContext_iff_coherent false _).mpr
  cases external <;> exact ⟨rfl, rfl, rfl⟩

theorem good_evaluation : model.Evaluates frozen good goodTuple := by
  simp [DeclaredArchitecture.Evaluates, DeclaredArchitecture.evaluate, root, frozen]

theorem good_reach (tuple : Bool × (Bool × Bool)) : model.reachInput false good tuple ↔ contract tuple := by
  constructor
  · rintro ⟨w, hw, ht, _⟩
    rw [world_unique w hw] at ht
    exact ((good_evaluation).deterministic ht).symm
  · intro h
    exact ⟨frozen, (fun _ _ => rfl), h.symm ▸ good_evaluation, trivial⟩

theorem good_valid : model.InputValid false good := by
  refine ⟨good_reach, ?_⟩
  intro i member
  constructor
  · rintro ⟨w, hw, supplied⟩
    rw [world_unique w hw] at supplied
    have whole := good_evaluation
    exact ⟨goodTuple, rfl, (whole.supplier i).deterministic supplied⟩
  · rintro ⟨tuple, allowed, same⟩
    obtain ⟨w, hw, ht, _⟩ := (good_reach tuple).mpr allowed
    exact ⟨w, hw, same ▸ ht.supplier i⟩

theorem bad_reach : model.reachInput false bad badTuple :=
  ⟨frozen, (fun _ _ => rfl), rfl, trivial⟩

theorem bad_incoming : model.incoming bad (.inr (.inl ())) false :=
  ⟨frozen, (fun _ _ => rfl), rfl⟩

theorem bad_invalid : ¬ model.InputValid false bad := by
  intro valid
  have falseTuple := valid.1 badTuple |>.mp bad_reach
  have impossible := congrArg (fun tuple : Bool × (Bool × Bool) => tuple.2.1) falseTuple
  cases impossible

theorem cannot_skip_bad_context : ¬ (∀ g t, model.isInputContext g t → model.InputStatus g t) := by
  intro complete
  cases complete false bad (context_is_local false) with
  | verified valid _ => exact bad_invalid valid
  | unreachable noSupplier _ _ => exact noSupplier (.inr (.inl ())) false bad_incoming

theorem unanchored_effect_rejected : ¬ model.ConeValid .local := by
  intro valid
  obtain ⟨i⟩ := valid.1
  exact Empty.elim i

-- Raw terms retain root labels; non-designated instances are outside supported contexts.
example : model.Evaluates frozen (root .one false) false := rfl
example : model.Evaluates frozen (root .one true) true := rfl

def whollyExternal : signature.Occurrence (signature.input false) :=
  .tensor (root .local true) (.tensor (root .one false) (root .two false))

theorem external_not_internal : ¬ model.isInputContext false whollyExternal := by
  intro supported
  have impossible : true = false := supported.1.1
  cases impossible

/-- Independent external Causes use different world coordinates. This fixture
checks the full input image, without claiming complete Effects for source-only
external Cones. The upstream inventory and provenance are unchanged. -/
abbrev independentModel : DeclaredArchitecture := {
  model with
  boundary := fun _ => True
  boundaryNonempty := ⟨frozen, trivial⟩
  admissibleInput := fun _ _ _ => True }

def independentWorld (tuple : Bool × (Bool × Bool)) : signature.World
  | .local, _ => tuple.1
  | .one, _ => !tuple.2.1
  | .two, _ => tuple.2.2

theorem independent_evaluation (tuple : Bool × (Bool × Bool)) :
    independentModel.Evaluates (independentWorld tuple) good tuple := by
  simp [DeclaredArchitecture.Evaluates, DeclaredArchitecture.evaluate, root,
    independentWorld]

theorem independent_full_tuple (tuple : Bool × (Bool × Bool)) :
    independentModel.reachInput false good tuple :=
  ⟨independentWorld tuple, trivial, independent_evaluation tuple, trivial⟩

theorem independent_valid : independentModel.InputValid false good := by
  refine ⟨fun tuple => ⟨fun _ => trivial, fun _ => independent_full_tuple tuple⟩, ?_⟩
  intro i member
  constructor
  · intro _
    cases i with
    | inl i => cases i; exact ⟨(member, (false, false)), trivial, rfl⟩
    | inr i =>
      cases i with
      | inl i => cases i; exact ⟨(false, (member, false)), trivial, rfl⟩
      | inr i => cases i; exact ⟨(false, (false, member)), trivial, rfl⟩
  · rintro ⟨tuple, _, same⟩
    have ht := independent_evaluation tuple
    exact ⟨independentWorld tuple, trivial, same ▸ ht.supplier i⟩

theorem operation_first {t : signature.Occurrence (signature.input false)} {tuple}
    (h : model.Evaluates frozen t tuple) :
    model.Evaluates frozen (ArchitectureSignature.Term.operation (S := signature) false t) tuple.1 := by
  change model.evaluate frozen (ArchitectureSignature.Term.operation (S := signature) false t) = some tuple.1
  rw [DeclaredArchitecture.evaluate, ite_eq_left trivial, h]
  rfl

abbrev outer (inner : signature.Occurrence (.node .local)) : signature.Occurrence (signature.input false) :=
  .tensor inner (.tensor (ArchitectureSignature.Term.operation (S := signature) true (root .one false)) (root .two false))
theorem outer_evaluation {inner : signature.Occurrence (.node .local)}
    (h : model.Evaluates frozen inner false) : model.Evaluates frozen (outer inner) goodTuple := by
  change model.evaluate frozen (.tensor inner (.tensor (ArchitectureSignature.Term.operation (S := signature) true (root .one false)) (root .two false))) = some goodTuple
  rw [DeclaredArchitecture.evaluate, h]
  simp [DeclaredArchitecture.evaluate, frozen]

/-- One downstream member arrow has two histories and two accompanying tuples.
An implementation memoizing only that arrow would lose a consequence. -/
theorem shared_arrow_keeps_both :
    model.Evaluates frozen
      (.tensor (ArchitectureSignature.Term.operation (S := signature) false (outer (ArchitectureSignature.Term.operation (S := signature) false good))) (ArchitectureSignature.Term.operation (S := signature) true (root .one false))) (false, true) ∧
    model.Evaluates frozen
      (.tensor (ArchitectureSignature.Term.operation (S := signature) false (outer (ArchitectureSignature.Term.operation (S := signature) false bad))) (root .one false)) (false, false) := by
  constructor
  · have inner := operation_first good_evaluation
    have output := operation_first (outer_evaluation inner)
    change model.evaluate frozen (.tensor (ArchitectureSignature.Term.operation (S := signature) false (outer (ArchitectureSignature.Term.operation (S := signature) false good))) (ArchitectureSignature.Term.operation (S := signature) true (root .one false))) = _
    rw [DeclaredArchitecture.evaluate, output]
    simp [DeclaredArchitecture.evaluate, frozen]
  · have inner := operation_first (show model.Evaluates frozen bad badTuple from rfl)
    have output := operation_first (outer_evaluation inner)
    change model.evaluate frozen (.tensor (ArchitectureSignature.Term.operation (S := signature) false (outer (ArchitectureSignature.Term.operation (S := signature) false bad))) (root .one false)) = _
    rw [DeclaredArchitecture.evaluate, output]
    simp [DeclaredArchitecture.evaluate, frozen]

end ArchiScriptTests.Provenance
