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
  Generator := Unit
  generators := [()]
  generators_complete := by intro g; cases g; simp
  input := fun _ => .tensor (.node .local) (.tensor (.node .one) (.node .two))
  output := fun _ => .local
  operation := fun _ => ⟨fun triple => some triple.1⟩
  localFactor := fun _ => ⟨.local, by simp [Inputs.nodes], rfl⟩

def frozen : signature.World := fun _ root => root
def contract (tuple : Bool × (Bool × Bool)) : Prop := tuple = (false, true, false)

/-- Deliberately draft: the same contract passes one context and fails another.
No Cone Effect or complete architecture certificate is claimed. -/
abbrev model : DeclaredArchitecture where
  signature := signature
  boundary := fun w => ∀ c root, w c root = root
  boundaryNonempty := ⟨frozen, fun _ _ => rfl⟩
  context := fun _ _ _ => True
  admissibleInput := fun _ _ => contract
  cyclicBoundary := fun _ => none
  effectContext := fun _ _ _ => True
  admissibleEffect := fun _ _ => False

abbrev root (source : Source) (instanceId : Bool) : signature.Occurrence (.node source) :=
  ArchitectureSignature.Term.cause (S := signature) source instanceId
abbrev inputs (external : Bool) : signature.Occurrence (signature.input ()) :=
  .tensor (root .local false) (.tensor (root .one external) (root .two false))
abbrev good := inputs true
abbrev bad := inputs false
abbrev goodTuple : Bool × (Bool × Bool) := (false, true, false)
abbrev badTuple : Bool × (Bool × Bool) := (false, false, false)

theorem world_unique (w : signature.World) (allowed : model.boundary w) : w = frozen := by
  funext c instanceId; exact allowed c instanceId

theorem context_is_local (external : Bool) : model.isInputContext () (inputs external) :=
  ⟨.inl (), ⟨⟨rfl, rfl⟩, fun _ => rfl⟩⟩

theorem good_reach (tuple : Bool × (Bool × Bool)) : model.reachInput () good tuple ↔ contract tuple := by
  constructor
  · rintro ⟨w, hw, ht, _⟩
    rw [world_unique w hw] at ht
    exact (Option.some.inj ht).symm
  · intro h
    exact ⟨frozen, (fun _ _ => rfl), h.symm ▸ rfl, trivial⟩

theorem good_valid : model.InputValid () good := by
  refine ⟨good_reach, ?_⟩
  intro i member
  constructor
  · rintro ⟨w, hw, supplied⟩
    rw [world_unique w hw] at supplied
    have whole : model.Evaluates frozen good goodTuple := rfl
    exact ⟨goodTuple, rfl, (whole.supplier i).deterministic supplied⟩
  · rintro ⟨tuple, allowed, same⟩
    obtain ⟨w, hw, ht, _⟩ := (good_reach tuple).mpr allowed
    exact ⟨w, hw, same ▸ ht.supplier i⟩

theorem bad_reach : model.reachInput () bad badTuple :=
  ⟨frozen, (fun _ _ => rfl), rfl, trivial⟩

theorem bad_incoming : model.incoming bad (.inr (.inl ())) false :=
  ⟨frozen, (fun _ _ => rfl), rfl⟩

theorem bad_invalid : ¬ model.InputValid () bad := by
  intro valid
  have falseTuple := valid.1 badTuple |>.mp bad_reach
  have impossible := congrArg (fun tuple : Bool × (Bool × Bool) => tuple.2.1) falseTuple
  cases impossible

theorem cannot_skip_bad_context : ¬ (∀ g t, model.isInputContext g t → model.InputStatus g t) := by
  intro complete
  cases complete () bad (context_is_local false) with
  | verified valid _ => exact bad_invalid valid
  | unreachable noSupplier _ _ => exact noSupplier (.inr (.inl ())) false bad_incoming

theorem unanchored_effect_rejected : ¬ model.ConeValid .local := by
  intro valid
  exact valid.1 rfl

-- Different instances of the same nominal source retain different values.
example : model.Evaluates frozen (root .one false) false := rfl
example : model.Evaluates frozen (root .one true) true := rfl

def whollyExternal : signature.Occurrence (signature.input ()) :=
  .tensor (root .local true) (.tensor (root .one false) (root .two false))

theorem external_not_internal : ¬ model.isInputContext () whollyExternal := by
  rintro ⟨i, belongs⟩
  cases i with
  | inl i => cases i; cases belongs.1.2
  | inr i =>
    cases i with
    | inl i => cases i; cases belongs.1.1
    | inr i => cases i; cases belongs.1.1

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
  | .one, _ => tuple.2.1
  | .two, _ => tuple.2.2

theorem independent_full_tuple (tuple : Bool × (Bool × Bool)) :
    independentModel.reachInput () good tuple := ⟨independentWorld tuple, trivial, rfl, trivial⟩

theorem independent_valid : independentModel.InputValid () good := by
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
    have ht : independentModel.Evaluates (independentWorld tuple) good tuple := rfl
    exact ⟨independentWorld tuple, trivial, same ▸ ht.supplier i⟩

theorem operation_first {t : signature.Occurrence (signature.input ())} {tuple}
    (h : model.Evaluates frozen t tuple) :
    model.Evaluates frozen (ArchitectureSignature.Term.operation (S := signature) () t) tuple.1 := by
  change model.evaluate frozen (.operation () t) = some tuple.1
  rw [DeclaredArchitecture.evaluate, ite_eq_left trivial, h]
  rfl

abbrev outer (inner : signature.Occurrence (.node .local)) : signature.Occurrence (signature.input ()) :=
  .tensor inner (.tensor (root .one true) (root .two false))
theorem outer_evaluation {inner : signature.Occurrence (.node .local)}
    (h : model.Evaluates frozen inner false) : model.Evaluates frozen (outer inner) goodTuple := by
  change model.evaluate frozen (.tensor inner (.tensor (root .one true) (root .two false))) = some goodTuple
  rw [DeclaredArchitecture.evaluate, h]
  rfl

/-- One downstream member arrow has two histories and two accompanying tuples.
An implementation memoizing only that arrow would lose a consequence. -/
theorem shared_arrow_keeps_both :
    model.Evaluates frozen
      (.tensor (.operation () (outer (.operation () good))) (root .one true)) (false, true) ∧
    model.Evaluates frozen
      (.tensor (.operation () (outer (.operation () bad))) (root .one false)) (false, false) := by
  constructor
  · have inner := operation_first (show model.Evaluates frozen good goodTuple from rfl)
    have output := operation_first (outer_evaluation inner)
    change model.evaluate frozen (.tensor (.operation () (outer (.operation () good))) (root .one true)) = _
    rw [DeclaredArchitecture.evaluate, output]
    rfl
  · have inner := operation_first (show model.Evaluates frozen bad badTuple from rfl)
    have output := operation_first (outer_evaluation inner)
    change model.evaluate frozen (.tensor (.operation () (outer (.operation () bad))) (root .one false)) = _
    rw [DeclaredArchitecture.evaluate, output]
    rfl

end ArchiScriptTests.Provenance
