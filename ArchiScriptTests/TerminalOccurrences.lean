import ArchiScript
import ArchiScript.ProofAudit

namespace ArchiScriptTests.TerminalOccurrences
open ArchiScript

abbrev bit : VDP := Partition.closed Bool "Boolean"
  ⟨[false, true], by intro b; cases b <;> simp⟩ ⟨false⟩
inductive Port where | source | left | right deriving DecidableEq

abbrev signature : ArchitectureSignature where
  Node := Port
  nodeDecidableEq := inferInstance
  nodes := [.source, .left, .right]
  nodes_complete := by intro n; cases n <;> simp
  nodes_nodup := by decide
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
  start := fun _ => .source
  owner := fun _ => ()
  start_owner := fun _ => rfl
  Generator := Bool
  generators := [false, true]
  generators_complete := by intro g; cases g <;> simp
  input := fun _ => .node .source
  output := fun g => if g then .right else .left
  operation := fun g => ⟨fun b => some (if g then !b else b)⟩
  localFactor := fun _ => ⟨.source, by simp [Inputs.nodes], rfl⟩

@[archiscript_contract] def effectAdmissible (_ : Unit) (tuple : Bool × (Bool × Unit)) : Prop :=
  tuple.2.1 = !tuple.1

abbrev model : DeclaredArchitecture where
  signature := signature
  boundary := fun _ => True
  boundaryNonempty := ⟨fun _ _ => false, trivial⟩
  context := fun _ _ _ => True
  admissibleInput := fun _ _ _ => True
  cyclicBoundary := fun _ => none
  effectContext := fun _ _ _ => True
  admissibleEffect := effectAdmissible

def values (b : Bool) : Port → Bool
  | .source | .left => b
  | .right => !b
def world (b : Bool) : signature.World := fun _ _ => b

theorem evaluation (w : signature.World) {s} (t : signature.Occurrence s) :
    model.evaluate w t = some (s.assign (values (w () ()))) := by
  apply model.evaluate_of_assignment
  · intro c root; cases c; cases root; rfl
  · intro g; cases g <;> rfl
  · intro g input; trivial

def terminal : signature.Occurrence (model.effect ()) :=
  .tensor (ArchitectureSignature.Term.operation (S := signature) false (.cause () ()))
    (.tensor (ArchitectureSignature.Term.operation (S := signature) true (.cause () ())) .unit)

theorem terminalOrigin (i : (model.effect ()).Position) : model.InCone () (terminal.supplier i) := by
  cases i with
  | inl i => cases i; exact ⟨⟨rfl, rfl⟩, fun _ => rfl⟩
  | inr i =>
    cases i with
    | inl i => cases i; exact ⟨⟨rfl, rfl⟩, fun _ => rfl⟩
    | inr impossible => exact Empty.elim impossible

theorem effect_exact (tuple : (model.effect ()).vdp.MemberIndex) :
    model.reachEffect () tuple ↔ effectAdmissible () tuple := by
  constructor
  · rintro ⟨t, _, w, _, supplied, _⟩
    have same := (evaluation w t).symm.trans supplied
    have member := Option.some.inj same
    rw [← member]
    rfl
  · rcases tuple with ⟨left, right, u⟩
    cases u
    intro allowed
    change right = !left at allowed
    cases allowed
    exact ⟨terminal, terminalOrigin, world left, trivial, evaluation _ terminal, trivial⟩

@[archiscript_certificate] def certified : CertifiedDeclaredArchitecture where
  model := model
  causeNonempty := ⟨()⟩
  inputs := by
    intro g t _
    have reaches (b : Bool) : model.reachInput g t b :=
      ⟨world b, trivial, evaluation _ t, trivial⟩
    refine .verified ⟨?_, ?_⟩ ⟨false, reaches false⟩
    · intro b; exact ⟨fun _ => trivial, fun _ => reaches b⟩
    · intro i b; cases i
      exact ⟨fun _ => ⟨b, trivial, rfl⟩,
        fun _ => ⟨world b, trivial,
          (show model.Evaluates (world b) t b from evaluation _ t).supplier ()⟩⟩
  cones := by
    intro c; cases c
    refine ⟨by decide, ⟨(false, (true, ())), (effect_exact _).mpr rfl⟩, effect_exact, ?_⟩
    intro i b
    constructor
    · intro _
      cases i with
      | inl i => cases i; exact ⟨(b, (!b, ())), rfl, rfl⟩
      | inr i =>
        cases i with
        | inl i =>
          cases i
          exact ⟨(!b, (b, ())), by cases b <;> rfl, rfl⟩
        | inr impossible => exact Empty.elim impossible
    · rintro ⟨tuple, allowed, coordinate⟩
      obtain ⟨t, origin, w, hw, ht, _⟩ := (effect_exact tuple).mpr allowed
      exact ⟨t.supplier i, origin i, w, hw, coordinate ▸ ht.supplier i⟩
  terminalOccurrencesFaithful := model.distinctTerminalProducers_of_injective (by
    intro g h same
    cases g <;> cases h <;> cases same <;> rfl)
  boundariesComplete := by
    intro c n _; cases c
    cases n with
    | source =>
      exact ⟨.left, by decide,
        ArchitectureSignature.Depends.step (S := signature) false Port.source
          (by change Port.source ∈ [Port.source]; simp)⟩
    | left => exact ⟨.left, by decide, .refl _⟩
    | right => exact ⟨.right, by decide, .refl _⟩

-- Equal VDPs are separate terminal coordinates; both routes participate.
example : signature.object .left = signature.object .right := rfl
#guard signature.effectNodes model.cyclicBoundary () == [.left, .right]
#guard (signature.effectNodes model.cyclicBoundary ()).length == 2
example : model.reachEffect () (true, (false, ())) := (effect_exact _).mpr rfl
example : ¬ model.reachEffect () (true, (true, ())) := by
  intro reached
  have impossible := (effect_exact _).mp reached
  cases impossible

/-- Two distinct terminal arrows sharing one unmarked slot are not accepted
as one occurrence, even though the target VDP and all member maps agree. -/
abbrev mergedSignature : ArchitectureSignature :=
  { signature with output := fun _ => .left, operation := fun _ => Operation.id bit }

abbrev merged : DeclaredArchitecture where
  signature := mergedSignature
  boundary := fun _ => True
  boundaryNonempty := ⟨fun _ _ => false, trivial⟩
  context := fun _ _ _ => True
  admissibleInput := fun _ _ _ => True
  cyclicBoundary := fun _ => none
  effectContext := fun _ _ _ => True
  admissibleEffect := fun _ _ => True

theorem merged_producers_rejected : ¬ merged.DistinctTerminalProducers := by
  intro faithful
  have impossible : false = true := faithful () .left (by decide) rfl false true rfl rfl
  cases impossible

-- The same slot may deliberately aggregate an entry and its feedback when
-- a real typed return identifies that observation. Only this policy is tested
-- here; this raw fixture does not claim a complete Cone certificate.
abbrev feedbackSignature : ArchitectureSignature := {
  mergedSignature with
  input := fun g => if g then .node .left else .node .source
  operation := by intro g; cases g <;> exact Operation.id bit
  localFactor := by
    intro g
    cases g
    · exact ⟨.source, by simp [Inputs.nodes], rfl⟩
    · exact ⟨.left, by simp [Inputs.nodes], rfl⟩ }

def feedbackBoundary : ArchitectureSignature.Term.CycleBoundary feedbackSignature .left where
  route := ArchitectureSignature.Term.operation (S := feedbackSignature)
    (Hole := fun n => PLift (Port.left = n)) true
      (ArchitectureSignature.Term.hole (S := feedbackSignature)
        (Hole := fun n => PLift (Port.left = n)) Port.left ⟨rfl⟩)
  oneEntry := rfl
  nontrivial := by decide

abbrev feedback : DeclaredArchitecture where
  signature := feedbackSignature
  boundary := fun _ => True
  boundaryNonempty := ⟨fun _ _ => false, trivial⟩
  context := fun _ _ _ => True
  admissibleInput := fun _ _ _ => True
  cyclicBoundary := fun n => match n with | .left => some feedbackBoundary | _ => none
  effectContext := fun _ _ _ => True
  admissibleEffect := fun _ _ => True

theorem marked_entry_and_feedback_preserved : feedback.DistinctTerminalProducers := by
  intro c n terminal unmarked
  cases c
  cases n with
  | source =>
    change Port.source ∈ [Port.left] at terminal
    simp at terminal
  | left => cases unmarked
  | right =>
    change Port.right ∈ [Port.left] at terminal
    simp at terminal

end ArchiScriptTests.TerminalOccurrences
