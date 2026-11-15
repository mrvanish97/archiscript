import ArchiScript
import ArchiScript.ProofAudit

namespace ArchiScriptSmoke
open ArchiScript

def booleanCarrier : Subdomain Bool :=
  .root "Bool" (fun _ => True) ⟨false, trivial⟩ (.predicate _)

def trueMember : Subdomain Bool :=
  .child "True" booleanCarrier (fun b => b = true) ⟨true, trivial, rfl⟩

def booleanSplit : SemanticSplit booleanCarrier :=
  .complement booleanCarrier trueMember trueMember.contained "False"
    ⟨false, trivial, by rintro ⟨_, h⟩; cases h⟩

abbrev bit : VDP := Partition.ofSplit booleanSplit (fun _ => trivial)

inductive Port where | input | output deriving DecidableEq

abbrev signature : ArchitectureSignature where
  Node := Port
  nodeDecidableEq := inferInstance
  nodes := [.input, .output]
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
  start := fun _ => .input
  owner := fun _ => ()
  start_owner := fun _ => rfl
  Generator := Unit
  generatorDecidableEq := inferInstance
  generators := [()]
  generators_complete := by intro g; cases g; simp
  input := fun _ => .node .input
  output := fun _ => .output
  operation := fun _ => Operation.id bit
  localFactor := fun _ => ⟨.input, by simp [Inputs.nodes], rfl⟩

@[archiscript_contract] def inputAdmissible (_ : signature.Generator)
    (_ : signature.Occurrence (.node .input)) (_ : Bool) : Prop := True

abbrev effectBasis : signature.ProvenanceAnalysis (fun _ => none) :=
  derive_provenance([()], 1)

@[archiscript_contract] def effectAdmissible (_ : Unit) (_ : Bool × Unit) : Prop := True

abbrev model : DeclaredArchitecture where
  signature := signature
  boundary := fun _ => True
  boundaryNonempty := ⟨fun _ _ => false, trivial⟩
  context := fun _ _ _ => True
  admissibleInput := inputAdmissible
  cyclicBoundary := fun _ => none
  effectAnalysis := effectBasis
  effectContext := fun _ _ _ => True
  admissibleEffect := effectAdmissible

def world (value : Bool) : signature.World := fun _ _ => value

theorem evaluation (w : signature.World) {s} (t : signature.Occurrence s) :
    model.evaluate w t = some (s.assign (fun _ => w () ())) := by
  apply model.evaluate_of_assignment
  · intro c root
    cases c; cases root; rfl
  · intro g; rfl
  · intro g input; trivial

theorem inputReach (t : signature.Occurrence (.node .input)) (value : Bool) :
    model.reachInput () t value :=
  ⟨world value, trivial, evaluation _ t, trivial⟩

theorem incoming (t : signature.Occurrence (.node .input)) (value : Bool) :
    model.incoming t () value :=
  ⟨world value, trivial, evaluation _ (t.supplier ())⟩

def terminal : signature.Occurrence (model.effect ()) :=
  .tensor (.operation () (.cause () ())) .unit

theorem terminalOrigin (i : (model.effect ()).Position) :
    model.InCone () (terminal.supplier i) := by
  cases i with
  | inl i =>
    cases i
    exact ⟨⟨rfl, rfl⟩, fun _ => rfl⟩
  | inr impossible => exact Empty.elim impossible

theorem terminalProvenance : model.EffectProvenance () terminal := by
  intro i
  cases i with
  | inl i => cases i; rfl
  | inr impossible => exact Empty.elim impossible

theorem effectReach (tuple : (model.effect ()).vdp.MemberIndex) : model.reachEffect () tuple := by
  rcases tuple with ⟨value, u⟩
  cases u
  exact ⟨terminal, terminalOrigin, terminalProvenance, world value, trivial, evaluation _ terminal, trivial⟩

theorem effectIncoming (i : (model.effect ()).Position)
    (value : (signature.object ((model.effect ()).nodeAt i)).MemberIndex) :
    model.effectIncoming () i value := by
  cases i with
  | inl i =>
    cases i
    exact ⟨terminal.supplier (.inl ()), terminalOrigin _, rfl,
      world value, trivial, evaluation _ _⟩
  | inr impossible => exact Empty.elim impossible

@[archiscript_certificate] def certified : CertifiedDeclaredArchitecture where
  model := model
  causeNonempty := ⟨()⟩
  effectCoverage := ⟨by intro root; cases root; simp, by decide⟩
  inputs := by
    intro g t _
    cases g
    refine .verified ⟨?_, ?_⟩ ⟨false, inputReach t false⟩
    · intro value
      exact ⟨fun _ => trivial, fun _ => inputReach t value⟩
    · intro i value
      cases i
      exact ⟨fun _ => ⟨value, trivial, rfl⟩, fun _ => incoming t value⟩
  cones := by
    intro c
    cases c
    refine ⟨by decide, ⟨(false, ()), effectReach _⟩, ?_, ?_⟩
    · intro tuple
      exact ⟨fun _ => trivial, fun _ => effectReach tuple⟩
    · intro i value
      cases i with
      | inl i =>
        cases i
        exact ⟨fun _ => ⟨(value, ()), trivial, rfl⟩, fun _ => effectIncoming _ _⟩
      | inr impossible => exact Empty.elim impossible
  boundariesComplete := by
    intro c n _
    cases c
    refine ⟨Port.output, ?_, ?_⟩
    · change Port.output ∈ [Port.output]
      simp
    · cases n with
      | input =>
        exact ArchitectureSignature.Depends.step (S := signature) () Port.input
          (by change Port.input ∈ [Port.input]; exact List.mem_cons_self)
      | output => exact .refl _

#guard certified.coverageStatus == "Global Cone/Expression coverage: NOT AUTOMATICALLY VERIFIED"

def linearRoute : Expression signature.generatorsInventory (Inputs.node Port.input) (Inputs.node Port.output) :=
  Expression.step (G := signature.generatorsInventory) ()
    (Expression.identity (G := signature.generatorsInventory) (Inputs.node Port.input))

example : linearRoute.denote = Operation.id bit := by
  simp [linearRoute, Expression.denote]

def constantTrue : Operation bit bit := ⟨fun _ => some true⟩
example : constantTrue.image (fun _ => True) true := ⟨false, trivial, rfl⟩
example : ¬ constantTrue.image (fun _ => True) false := by
  rintro ⟨_, _, impossible⟩
  cases impossible

end ArchiScriptSmoke

#audit_archiscript
