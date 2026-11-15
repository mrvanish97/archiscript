import ArchiScriptExamples.SharedTargets

/-! A separate, explicitly declared C tensor C -> R join. The graph has one C.
This fixture proves every input-context obligation; it does not advertise a
complete Cone certificate. The shared-target Cone certificates are in SharedTargets. -/
namespace ArchiScriptExamples.SharedTargetJoin
open ArchiScript
abbrev bit := SharedTargets.bit
inductive Port where | x | a | b | c | result deriving DecidableEq
inductive Arrow where | p | q | f | g | join deriving DecidableEq

abbrev object : Port → VDP
  | .result => bit.tensor bit
  | _ => bit

abbrev signature : ArchitectureSignature where
  Node := Port
  nodeDecidableEq := inferInstance
  nodes := [.x, .a, .b, .c, .result]
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
  start := fun _ => .x
  owner := fun _ => ()
  start_owner := fun _ => rfl
  Generator := Arrow
  generatorDecidableEq := inferInstance
  generators := [.p, .q, .f, .g, .join]
  generators_complete := by intro arrow; cases arrow <;> simp
  input
    | .p | .q => .node .x
    | .f => .node .a
    | .g => .node .b
    | .join => .tensor (.node .c) (.node .c)
  output
    | .p => .a
    | .q => .b
    | .f | .g => .c
    | .join => .result
  operation
    | .p | .q | .f | .g => Operation.id bit
    | .join => Operation.id (bit.tensor bit)
  localFactor := by
    intro arrow; cases arrow
    · exact ⟨.x, List.mem_cons_self, rfl⟩
    · exact ⟨.x, List.mem_cons_self, rfl⟩
    · exact ⟨.a, List.mem_cons_self, rfl⟩
    · exact ⟨.b, List.mem_cons_self, rfl⟩
    · exact ⟨.c, by simp [Inputs.nodes], rfl⟩

@[archiscript_contract] def inputAdmissible (arrow : Arrow)
    (_ : signature.Occurrence (signature.input arrow)) : (signature.input arrow).vdp.MemberIndex → Prop :=
  match arrow with
  | .join => fun pair => pair.2 = pair.1
  | _ => fun _ => True

abbrev basis : signature.ProvenanceAnalysis (fun _ => none) := derive_provenance([()], 3)
abbrev model : DeclaredArchitecture where
  signature := signature
  boundary := fun _ => True
  boundaryNonempty := ⟨fun _ _ => false, trivial⟩
  context := fun _ _ _ => True
  admissibleInput := inputAdmissible
  cyclicBoundary := fun _ => none
  effectAnalysis := basis
  effectContext := fun _ _ _ => True
  admissibleEffect := fun _ _ => True

def values (root : Bool) : (n : Port) → (object n).MemberIndex
  | .result => (root, root)
  | .x | .a | .b | .c => root

def world (root : Bool) : signature.World := fun _ _ => root

theorem evaluation (w : signature.World) {s} (t : signature.Occurrence s) :
    model.Evaluates w t (s.assign (values (w () ()))) := by
  apply model.evaluate_of_assignment
  · intro c root; cases c; cases root; rfl
  · intro arrow; cases arrow <;> rfl
  · intro arrow t; trivial

theorem input_image (arrow : Arrow) (t : signature.Occurrence (signature.input arrow)) (tuple) :
    model.reachInput arrow t tuple ↔ ∃ root, (signature.input arrow).assign (values root) = tuple := by
  constructor
  · rintro ⟨w, _, supplied, _⟩
    exact ⟨w () (), Option.some.inj ((evaluation w t).symm.trans supplied)⟩
  · rintro ⟨root, same⟩
    exact ⟨world root, trivial, (evaluation _ t).trans (congrArg some same), trivial⟩

theorem input_exact (arrow : Arrow) (t : signature.Occurrence (signature.input arrow)) (tuple) :
    model.reachInput arrow t tuple ↔ inputAdmissible arrow t tuple := by
  rw [input_image]
  cases arrow with
  | p | q | f | g => exact ⟨fun _ => trivial, fun _ => ⟨tuple, rfl⟩⟩
  | join =>
    constructor
    · rintro ⟨root, same⟩; cases same; rfl
    · intro h; exact ⟨tuple.1, Prod.ext rfl h.symm⟩

theorem input_valid (arrow : Arrow) (t : signature.Occurrence (signature.input arrow)) : model.InputValid arrow t := by
  refine ⟨input_exact arrow t, ?_⟩
  intro i member
  constructor
  · rintro ⟨w, _, supplied⟩
    have value := Option.some.inj ((evaluation w (t.supplier i)).symm.trans supplied)
    exact ⟨_, (input_exact arrow t _).mp ((input_image arrow t _).mpr ⟨w () (), rfl⟩),
      (Inputs.coordinate_assign (values (w () ())) _ i).trans value⟩
  · rintro ⟨tuple, allowed, same⟩
    obtain ⟨w, hw, ht, _⟩ := (input_exact arrow t tuple).mpr allowed
    exact ⟨w, hw, same ▸ ht.supplier i⟩

abbrev leftC : signature.Occurrence (.node .c) :=
  ArchitectureSignature.Term.operation (S := signature) .f
    (ArchitectureSignature.Term.operation (S := signature) .p
      (ArchitectureSignature.Term.cause (S := signature) () ()))
abbrev rightC : signature.Occurrence (.node .c) :=
  ArchitectureSignature.Term.operation (S := signature) .g
    (ArchitectureSignature.Term.operation (S := signature) .q
      (ArchitectureSignature.Term.cause (S := signature) () ()))
def joinInput : signature.Occurrence (signature.input .join) := .tensor leftC rightC
def joined : signature.Occurrence (.node .result) :=
  ArchitectureSignature.Term.operation (S := signature) .join joinInput

theorem supplied_join_valid : model.InputValid .join joinInput := input_valid .join joinInput
example : model.reachInput .join joinInput (true, true) := (input_exact _ _ _).mpr rfl
example : ¬ model.reachInput .join joinInput (false, true) := by
  intro reached
  have impossible := (input_exact _ _ _).mp reached
  cases impossible
example : model.Evaluates (world true) joined (true, true) := evaluation _ _
example : leftC.history ≠ rightC.history := by decide

end ArchiScriptExamples.SharedTargetJoin
