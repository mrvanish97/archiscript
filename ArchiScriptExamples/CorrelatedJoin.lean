import ArchiScriptExamples.SimpleCone

namespace ArchiScriptExamples.CorrelatedJoin
open ArchiScript
abbrev bit := SimpleCone.bit
inductive Port where | source | left | right | joined deriving DecidableEq
inductive Arrow where | left | right | join deriving DecidableEq

abbrev object : Port → VDP
  | .joined => bit.tensor bit
  | _ => bit

abbrev signature (rightMeaning : Bool → Bool) : ArchitectureSignature where
  Node := Port
  nodeDecidableEq := inferInstance
  nodes := [.source, .left, .right, .joined]
  nodes_complete := by intro n; cases n <;> simp
  nodes_nodup := by decide
  object := object
  domains := [⟨Bool, bit.members false⟩, ⟨Bool, bit.members true⟩,
    ⟨Bool × Bool, (bit.tensor bit).members (false, false)⟩,
    ⟨Bool × Bool, (bit.tensor bit).members (false, true)⟩,
    ⟨Bool × Bool, (bit.tensor bit).members (true, false)⟩,
    ⟨Bool × Bool, (bit.tensor bit).members (true, true)⟩]
  memberDeclared := by
    intro n i
    cases n <;> cases i <;> try simp
    rename_i a b
    cases a <;> cases b <;> simp
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
  Generator := Arrow
  generatorDecidableEq := inferInstance
  generators := [.left, .right, .join]
  generators_complete := by intro g; cases g <;> simp
  input
    | .left | .right => .node .source
    | .join => .tensor (.node .left) (.node .right)
  output
    | .left => .left
    | .right => .right
    | .join => .joined
  operation
    | .left => Operation.id bit
    | .right => ⟨fun b => some (rightMeaning b)⟩
    | .join => Operation.id (bit.tensor bit)
  localFactor := by
    intro g
    cases g
    · exact ⟨.source, List.mem_cons_self, rfl⟩
    · exact ⟨.source, List.mem_cons_self, rfl⟩
    · exact ⟨.left, by simp [Inputs.nodes], rfl⟩

@[archiscript_contract] def inputAdmissible (rightMeaning : Bool → Bool)
    (g : Arrow) (_ : (signature rightMeaning).Occurrence ((signature rightMeaning).input g)) :
    ((signature rightMeaning).input g).vdp.MemberIndex → Prop :=
  match g with
  | .left | .right => fun _ => True
  | .join => fun pair => pair.2 = rightMeaning pair.1

abbrev effectBasis (f : Bool → Bool) : (signature f).ProvenanceAnalysis (fun _ => none) :=
  derive_provenance([()], 2)

@[archiscript_contract] def effectAdmissible (rightMeaning : Bool → Bool) (_ : Unit)
    (tuple : (Bool × Bool) × Unit) : Prop := tuple.1.2 = rightMeaning tuple.1.1

abbrev model (rightMeaning : Bool → Bool) : DeclaredArchitecture where
  signature := signature rightMeaning
  boundary := fun _ => True
  boundaryNonempty := ⟨fun _ _ => false, trivial⟩
  context := fun _ _ _ => True
  admissibleInput := inputAdmissible rightMeaning
  cyclicBoundary := fun _ => none
  effectAnalysis := effectBasis rightMeaning
  effectContext := fun _ _ _ => True
  admissibleEffect := effectAdmissible rightMeaning

def values (rightMeaning : Bool → Bool) (root : Bool) : (n : Port) → (object n).MemberIndex
  | .source | .left => root
  | .right => rightMeaning root
  | .joined => (root, rightMeaning root)

def world (rightMeaning : Bool → Bool) (root : Bool) : (signature rightMeaning).World := fun _ _ => root

theorem evaluation (f : Bool → Bool) (w : (signature f).World) {s}
    (t : (signature f).Occurrence s) :
    (model f).evaluate w t = some (s.assign (values f (w () ()))) := by
  apply (model f).evaluate_of_assignment
  · intro c root; cases c; cases root; rfl
  · intro g; cases g <;> rfl
  · intro g t; trivial

theorem input_image (f : Bool → Bool) (g : Arrow)
    (t : (signature f).Occurrence ((signature f).input g)) (tuple) :
    (model f).reachInput g t tuple ↔
      ∃ root, ((signature f).input g).assign (values f root) = tuple := by
  constructor
  · rintro ⟨w, _, supplied, _⟩
    exact ⟨w () (), Option.some.inj ((evaluation f w t).symm.trans supplied)⟩
  · rintro ⟨root, same⟩
    exact ⟨world f root, trivial, (evaluation f _ t).trans (congrArg some same), trivial⟩

theorem input_exact (f : Bool → Bool) (g : Arrow)
    (t : (signature f).Occurrence ((signature f).input g)) (tuple) :
    (model f).reachInput g t tuple ↔ inputAdmissible f g t tuple := by
  rw [input_image]
  cases g with
  | left => exact ⟨fun _ => trivial, fun _ => ⟨tuple, rfl⟩⟩
  | right => exact ⟨fun _ => trivial, fun _ => ⟨tuple, rfl⟩⟩
  | join =>
    constructor
    · rintro ⟨root, same⟩
      cases same
      rfl
    · intro h
      exact ⟨tuple.1, Prod.ext rfl h.symm⟩

theorem incoming_image (f : Bool → Bool) {s} (t : (signature f).Occurrence s)
    (i : s.Position) (member) :
    (model f).incoming t i member ↔ ∃ root, values f root (s.nodeAt i) = member := by
  constructor
  · rintro ⟨w, _, supplied⟩
    exact ⟨w () (), Option.some.inj ((evaluation f w (t.supplier i)).symm.trans supplied)⟩
  · rintro ⟨root, same⟩
    exact ⟨world f root, trivial, (evaluation f _ (t.supplier i)).trans (congrArg some same)⟩

theorem input_valid (f : Bool → Bool) (g : Arrow)
    (t : (signature f).Occurrence ((signature f).input g)) : (model f).InputValid g t := by
  refine ⟨input_exact f g t, ?_⟩
  intro i member
  constructor
  · intro h
    obtain ⟨root, same⟩ := (incoming_image f t i member).mp h
    refine ⟨_, (input_exact f g t _).mp ((input_image f g t _).mpr ⟨root, rfl⟩), ?_⟩
    exact (Inputs.coordinate_assign (values f root) _ i).trans same
  · rintro ⟨tuple, allowed, same⟩
    obtain ⟨w, hw, ht, _⟩ := (input_exact f g t tuple).mpr allowed
    exact ⟨w, hw, same ▸ ht.supplier i⟩

def sourceTrace (f : Bool → Bool) : (signature f).Occurrence (.node .source) :=
  ArchitectureSignature.Term.cause (S := signature f) () ()

def leftTrace (f : Bool → Bool) : (signature f).Occurrence (.node .left) :=
  ArchitectureSignature.Term.operation (S := signature f) .left (sourceTrace f)

def rightTrace (f : Bool → Bool) : (signature f).Occurrence (.node .right) :=
  ArchitectureSignature.Term.operation (S := signature f) .right (sourceTrace f)

def joinInput (f : Bool → Bool) : (signature f).Occurrence ((signature f).input .join) :=
  ArchitectureSignature.Term.tensor (S := signature f) (leftTrace f) (rightTrace f)

def joinedTrace (f : Bool → Bool) : (signature f).Occurrence (.node .joined) :=
  ArchitectureSignature.Term.operation (S := signature f) .join (joinInput f)

def terminal (f : Bool → Bool) : (signature f).Occurrence ((model f).effect ()) :=
  ArchitectureSignature.Term.tensor (S := signature f) (joinedTrace f) .unit

theorem terminal_origin (f : Bool → Bool) (i : ((model f).effect ()).Position) :
    (model f).InCone () ((terminal f).supplier i) := by
  cases i with
  | inl i =>
    cases i
    exact ⟨Or.inl ⟨rfl, rfl⟩, ⟨fun _ => rfl, fun _ => rfl⟩⟩
  | inr impossible => exact Empty.elim impossible

theorem terminal_provenance (f : Bool → Bool) : (model f).EffectProvenance () (terminal f) := by
  intro i
  cases i with
  | inl i => cases i; rfl
  | inr impossible => exact Empty.elim impossible

theorem effect_image (f : Bool → Bool) (tuple : (Bool × Bool) × Unit) :
    (model f).reachEffect () tuple ↔ ∃ root, ((root, f root), ()) = tuple := by
  have image := DeclaredArchitecture.effect_image_of_assignment (model f) ()
    (fun w => values f (w () ())) (fun w _ t => evaluation f w t)
    (terminal f) (terminal_origin f) (terminal_provenance f) (fun _ _ => trivial) tuple
  constructor
  · intro reached
    obtain ⟨w, _, same⟩ := image.mp reached
    exact ⟨w () (), same⟩
  · rintro ⟨root, same⟩
    exact image.mpr ⟨world f root, trivial, same⟩

theorem effect_exact (f : Bool → Bool) (tuple : (Bool × Bool) × Unit) :
    (model f).reachEffect () tuple ↔ effectAdmissible f () tuple := by
  apply Iff.trans (effect_image f tuple)
  change (∃ root, ((root, f root), ()) = tuple) ↔ tuple.1.2 = f tuple.1.1
  constructor
  · rintro ⟨root, same⟩; cases same; rfl
  · rcases tuple with ⟨⟨left, right⟩, u⟩; cases u
    intro allowed
    exact ⟨left, Prod.ext (Prod.ext rfl allowed.symm) rfl⟩

theorem effect_projection (f : Bool → Bool) (i : ((model f).effect ()).Position)
    (member : ((signature f).object (((model f).effect ()).nodeAt i)).MemberIndex) :
    (model f).effectIncoming () i member ↔
      ∃ tuple, (model f).admissibleEffect () tuple ∧ ((model f).effect ()).coordinate tuple i = member :=
  DeclaredArchitecture.effect_projection_of_assignment (model f) ()
    (fun w => values f (w () ())) (fun w _ t => evaluation f w t)
    (fun _ _ => rfl) (effect_exact f) i member

def certificate (f : Bool → Bool) : CertifiedDeclaredArchitecture where
  model := model f
  causeNonempty := ⟨()⟩
  effectCoverage := ⟨by intro root; cases root; simp, by exact of_decide_eq_true rfl⟩
  inputs := by
    intro g t _
    exact .verified (input_valid f g t)
      ⟨((signature f).input g).assign (values f false),
        (input_image f g t _).mpr ⟨false, rfl⟩⟩
  cones := by
    intro c; cases c
    refine ⟨?_, ⟨((false, f false), ()), (effect_exact f _).mpr rfl⟩, effect_exact f, ?_⟩
    · change [Port.joined] ≠ []
      decide
    exact effect_projection f
  boundariesComplete := by
    intro c n _; cases c
    refine ⟨Port.joined, ?_, ?_⟩
    · change Port.joined ∈ [Port.joined]
      exact List.mem_cons_self
    · cases n with
      | source =>
        exact .trans (ArchitectureSignature.Depends.step (S := signature f) Arrow.left Port.source List.mem_cons_self)
          (ArchitectureSignature.Depends.step (S := signature f) Arrow.join Port.left (by simp [Inputs.nodes]))
      | left => exact ArchitectureSignature.Depends.step (S := signature f) Arrow.join Port.left (by simp [Inputs.nodes])
      | right => exact ArchitectureSignature.Depends.step (S := signature f) Arrow.join Port.right (by simp [Inputs.nodes])
      | joined => exact .refl _

@[archiscript_certificate] def diagonalCertified := certificate id
@[archiscript_certificate] def constantCertified := certificate (fun _ => true)

/-- Full mathematical product, proper source-correlated admissible relation. -/
example : ¬ inputAdmissible id .join (joinInput id) (false, true) := by
  change ¬ true = false
  decide

example : (bit.tensor bit).member (false, true) (false, true) := ⟨rfl, rfl⟩

end ArchiScriptExamples.CorrelatedJoin
