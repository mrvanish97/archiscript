import ArchiScriptExamples.SimpleCone
import ArchiScript.Reachability

namespace ArchiScriptExamples.CyclicCone
open ArchiScript
abbrev bit := SimpleCone.bit

abbrev signature : ArchitectureSignature where
  Node := Unit
  nodeDecidableEq := inferInstance
  nodes := [()]
  nodes_complete := by intro n; cases n; simp
  nodes_nodup := by simp
  object := fun _ => bit
  domains := [⟨Bool, bit.members false⟩, ⟨Bool, bit.members true⟩]
  memberDeclared := by intro n i; cases n <;> cases i <;> simp
  splits := []
  Cause := Unit
  causeDecidableEq := inferInstance
  causes := [()]
  causes_complete := by intro c; cases c; simp
  causes_nodup := by simp
  RootInstance := Unit
  rootDecidableEq := inferInstance
  origin := fun _ => ()
  start := fun _ => ()
  owner := fun _ => ()
  start_owner := fun _ => rfl
  Generator := Unit
  generatorDecidableEq := inferInstance
  generators := [()]
  generators_complete := by intro g; cases g; simp
  input := fun _ => .node ()
  output := fun _ => ()
  operation := fun _ => ⟨fun b => some (!b)⟩
  localFactor := fun _ => ⟨(), by simp [Inputs.nodes], rfl⟩

def cycleEntry : signature.Term (fun k => PLift (() = k)) (.node ()) :=
  ArchitectureSignature.Term.hole (S := signature) (Hole := fun k => PLift (() = k)) () (PLift.up rfl)

def boundary : ArchitectureSignature.Term.CycleBoundary signature () where
  route := ArchitectureSignature.Term.operation (S := signature)
    (Hole := fun k => PLift (() = k)) () cycleEntry
  oneEntry := rfl
  nontrivial := by decide

/-- Independently authored expectation for the member after n swaps. -/
def alternating : Nat → Bool
  | 0 => false
  | n + 1 => !alternating n

@[archiscript_contract] def inputAdmissible (_ : Unit)
    (t : signature.Occurrence (.node ())) (b : Bool) : Prop := b = alternating t.operations

abbrev effectBasis : signature.ProvenanceAnalysis (fun _ => some boundary) :=
  derive_provenance([()], 0)

@[archiscript_contract] def effectAdmissible (_ : Unit) (_ : Bool × Unit) : Prop := True

abbrev model : DeclaredArchitecture where
  signature := signature
  boundary := fun w => w () () = false
  boundaryNonempty := ⟨fun _ _ => false, rfl⟩
  context := fun _ _ _ => True
  admissibleInput := inputAdmissible
  cyclicBoundary := fun _ => some boundary
  effectAnalysis := effectBasis
  effectContext := fun _ _ _ => True
  admissibleEffect := effectAdmissible

def initial : signature.World := fun _ _ => false
def entry : signature.Occurrence (.node ()) := .cause () ()
def once : signature.Occurrence (.node ()) := .operation () entry

theorem trace_invariant {s} (t : signature.Occurrence s) :
    ∀ n (same : s = .node n),
      model.evaluate initial (show signature.Occurrence (.node n) from same ▸ t) = some (alternating t.operations) := by
  induction t with
  | unit => intro n same; cases same
  | cause c root => intro n same; cases same; rfl
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih =>
    intro n same; cases same; cases g
    have previous := ih () rfl
    rw [DeclaredArchitecture.evaluate, ite_eq_left trivial, previous]
    rfl
  | tensor left right ihl ihr => intro n same; cases same

theorem trace_evaluation (t : signature.Occurrence (.node ())) :
    model.evaluate initial t = some (alternating t.operations) := trace_invariant t () rfl

theorem origin_invariant {s} (t : signature.Occurrence s) :
    ∀ n (same : s = .node n), model.InCone () (show signature.Occurrence (.node n) from same ▸ t) := by
  induction t with
  | unit => intro n same; cases same
  | cause c root =>
    intro n same; cases same; cases c; cases root
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih => intro n same; cases same; cases g; exact ih () rfl
  | tensor left right ihl ihr => intro n same; cases same

theorem origin (t : signature.Occurrence (.node ())) : model.InCone () t := origin_invariant t () rfl

theorem world_unique (w : signature.World) (allowed : model.boundary w) : w = initial := by
  funext c root
  cases c; cases root
  exact allowed

theorem input_exact (t : signature.Occurrence (.node ())) (b : Bool) :
    model.reachInput () t b ↔ inputAdmissible () t b := by
  constructor
  · rintro ⟨w, hw, supplied, _⟩
    rw [world_unique w hw] at supplied
    exact (Option.some.inj ((trace_evaluation t).symm.trans supplied)).symm
  · intro expected
    refine ⟨initial, rfl, ?_, trivial⟩
    exact (trace_evaluation t).trans (congrArg some expected.symm)

theorem incoming_exact (t : signature.Occurrence (.node ())) (b : Bool) :
    model.incoming t () b ↔ inputAdmissible () t b := by
  unfold DeclaredArchitecture.incoming
  dsimp only [Inputs.nodeAt]
  rw [ArchitectureSignature.Term.supplier_node]
  exact (show (∃ w, model.boundary w ∧ model.Evaluates w t b) ↔ model.reachInput () t b from
    ⟨fun ⟨w, hw, ht⟩ => ⟨w, hw, ht, trivial⟩, fun ⟨w, hw, ht, _⟩ => ⟨w, hw, ht⟩⟩).trans
    (input_exact t b)

def observed (b : Bool) : signature.Occurrence (.node ()) := if b then once else entry

theorem observed_evaluation (b : Bool) : model.Evaluates initial (observed b) b := by
  cases b with
  | false => rfl
  | true => exact trace_evaluation once

def terminal (b : Bool) : signature.Occurrence (model.effect ()) := .tensor (observed b) .unit

theorem observedProvenance (b : Bool) : (observed b).provenance model.cyclicBoundary =
    ProducerHistory.cause () () := by
  cases b <;> rfl

theorem terminalProvenance (b : Bool) : model.EffectProvenance () (terminal b) := by
  intro i
  cases i with
  | inl i =>
    cases i
    change ((observed b).supplier ()).provenance model.cyclicBoundary = ProducerHistory.cause () ()
    rw [ArchitectureSignature.Term.supplier_node]
    exact observedProvenance b
  | inr impossible => exact Empty.elim impossible

theorem effectReach (tuple : (model.effect ()).vdp.MemberIndex) : model.reachEffect () tuple := by
  rcases tuple with ⟨b, u⟩; cases u
  refine ⟨terminal b, ?_, terminalProvenance b, initial, rfl, ?_, trivial, ⟨.inl ()⟩⟩
  · intro i
    cases i with
    | inl i =>
      cases i
      simpa only [terminal, ArchitectureSignature.Term.supplier,
        ArchitectureSignature.Term.supplier_node] using origin (observed b)
    | inr impossible => exact Empty.elim impossible
  · change model.evaluate initial (.tensor (observed b) .unit) = some (b, ())
    simp only [DeclaredArchitecture.evaluate]
    have h := observed_evaluation b
    change model.evaluate initial (observed b) = some b at h
    rw [h]

theorem basis_valid : model.effectAnalysis.Valid :=
  ⟨by intro c; cases c <;> simp, by decide⟩

@[archiscript_certificate] def certified : CertifiedDeclaredArchitecture where
  model := model
  causeNonempty := ⟨()⟩
  effectCoverage := basis_valid
  inputSources := by
    intro g
    exact model.inputSources_of_catalog basis_valid g (by cases g <;> exact of_decide_eq_true rfl)
  inputs := by
    intro g t _; cases g
    refine .verified ⟨input_exact t, ?_⟩ ?_
    · intro i b; cases i
      exact (incoming_exact t b).trans
        ⟨fun h => ⟨b, h, rfl⟩, fun ⟨_, h, same⟩ => same ▸ h⟩
    · exact ⟨alternating t.operations, (input_exact t _).mpr rfl⟩
  cones := by
    intro c; cases c
    apply DeclaredArchitecture.ConeStatus.observable
    refine ⟨⟨.inl ()⟩, ⟨(false, ()), effectReach _⟩, ?_, ?_⟩
    · intro tuple
      exact ⟨fun _ => trivial, fun _ => effectReach tuple⟩
    · intro i b
      cases i with
      | inl i =>
        cases i
        exact ⟨fun _ => ⟨(b, ()), trivial, rfl⟩,
          fun _ => ⟨observed b, origin _, observedProvenance b, initial, rfl, observed_evaluation b⟩⟩
      | inr impossible => exact Empty.elim impossible
  boundariesComplete := by
    intro c n _; cases c; cases n
    apply Or.inr
    refine ⟨(), ?_, .refl _⟩
    change () ∈ [()]
    simp

/-- A finite exact analyzer is tied to the reference Effect relation below. -/
def analysis : Reachability.FiniteAnalysis Bool where
  states := [false, true]
  complete := by intro b; cases b <;> simp
  initial := fun b => b = false
  step := fun a b => b = !a
  initialDecidable := inferInstance
  stepDecidable := inferInstance
  stateDecidableEq := inferInstance

def exactClosure : analysis.Exact :=
  ⟨analysis.compute 1, analysis.compute_sound 1, analysis.compute_complete_of_closed 1 (by decide)⟩

theorem closure_exact : Reachability.ExactAbstraction
    (fun b => model.reachEffect () (b, ())) analysis where
  equivalent := by
    intro b
    constructor
    · intro _
      cases b with
      | false => exact .initial rfl
      | true => exact .next (.initial rfl) rfl
    · intro _; exact effectReach _

theorem computed_effect (b : Bool) : b ∈ exactClosure.members ↔ model.reachEffect () (b, ()) :=
  Reachability.certified_abstraction closure_exact exactClosure b

#guard (analysis.certify 0).isNone
#guard (analysis.certify 1).isSome
#guard exactClosure.members == [false, true]
#guard (signature.effectNodes model.cyclicBoundary ()).length == 1

theorem powers_do_not_stabilize (n : Nat) : alternating (n + 1) ≠ alternating n := by
  cases h : alternating n <;> simp [alternating, h]

end ArchiScriptExamples.CyclicCone
