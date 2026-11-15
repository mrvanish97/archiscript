import ArchiScriptExamples.CyclicCone

/-! A mutually dependent pair of Cones. The intended Boolean formula semantics
is declared independently of the primitive truth tables. The finite analysis
below treats the dependency component jointly; neither Cone is evaluated first. -/
namespace ArchiScriptExamples.MutualCones
open ArchiScript
abbrev bit := SimpleCone.bit
abbrev signature : ArchitectureSignature where
  Node := Bool
  nodeDecidableEq := inferInstance
  nodes := [false, true]
  nodes_complete := by intro n; cases n <;> simp
  nodes_nodup := by decide
  object := fun _ => bit
  domains := [⟨Bool, bit.members false⟩, ⟨Bool, bit.members true⟩]
  memberDeclared := by intro n i; cases n <;> cases i <;> simp
  splits := []
  Cause := Bool
  causeDecidableEq := inferInstance
  causes := [false, true]
  causes_complete := by intro c; cases c <;> simp
  causes_nodup := by decide
  RootInstance := Unit
  rootDecidableEq := inferInstance
  origin := fun _ => ()
  start := id
  owner := id
  start_owner := fun _ => rfl
  Generator := Bool
  generatorDecidableEq := inferInstance
  generators := [false, true]
  generators_complete := by intro g; cases g <;> simp
  input := fun _ => .tensor (.node false) (.node true)
  output := id
  operation
    | false => ⟨fun | (_, false) => some true | (_, true) => some false⟩
    | true => ⟨fun | (false, _) => some false | (true, _) => some true⟩
  localFactor := by
    intro g; cases g
    · exact ⟨false, by simp [Inputs.nodes], rfl⟩
    · exact ⟨true, by simp [Inputs.nodes], rfl⟩

def entryA : signature.Term (fun n => PLift (false = n)) (.node false) :=
  ArchitectureSignature.Term.hole (S := signature) (Hole := fun n => PLift (false = n)) false ⟨rfl⟩
def entryB : signature.Term (fun n => PLift (true = n)) (.node true) :=
  ArchitectureSignature.Term.hole (S := signature) (Hole := fun n => PLift (true = n)) true ⟨rfl⟩
def cycleA : ArchitectureSignature.Term.CycleBoundary signature false where
  route := ArchitectureSignature.Term.operation (S := signature) (Hole := fun n => PLift (false = n))
    false (.tensor entryA (ArchitectureSignature.Term.cause (S := signature) (Hole := fun n => PLift (false = n)) true ()))
  oneEntry := rfl
  nontrivial := by decide
def cycleB : ArchitectureSignature.Term.CycleBoundary signature true where
  route := ArchitectureSignature.Term.operation (S := signature) (Hole := fun n => PLift (true = n))
    true (.tensor (ArchitectureSignature.Term.cause (S := signature) (Hole := fun n => PLift (true = n)) false ()) entryB)
  oneEntry := rfl
  nontrivial := by decide
abbrev marked : (n : Bool) → Option (ArchitectureSignature.Term.CycleBoundary signature n)
  | false => some cycleA | true => some cycleB

/-- Normative formula interpretation: roots are false, A means not B, B means A.
No Operation map or implementation reachability function is consulted here. -/
def specification {s} : signature.Occurrence s → s.vdp.MemberIndex
  | .unit => ()
  | .cause .. => false
  | .hole _ impossible => nomatch impossible
  | .operation g input => if g then (specification input).1 else !(specification input).2
  | .tensor left right => (specification left, specification right)

@[archiscript_contract] def inputAdmissible (_ : Bool)
    (t : signature.Occurrence (.tensor (.node false) (.node true))) (pair : Bool × Bool) : Prop :=
  pair = specification t
abbrev effectBasis : signature.ProvenanceAnalysis marked :=
  derive_provenance([()], 0)

@[archiscript_contract] def effectAdmissible (c : Bool) :
    (signature.effectInputs effectBasis c).vdp.MemberIndex → Prop := fun _ => True

abbrev model : DeclaredArchitecture where
  signature := signature
  boundary := fun w => ∀ c, w c () = false
  boundaryNonempty := ⟨fun _ _ => false, fun _ => rfl⟩
  context := fun _ _ _ => True
  admissibleInput := inputAdmissible
  cyclicBoundary := marked
  effectAnalysis := effectBasis
  effectContext := fun _ _ _ => True
  admissibleEffect := effectAdmissible

def initial : signature.World := fun _ _ => false
theorem world_unique (w : signature.World) (allowed : model.boundary w) : w = initial := by
  funext c root; cases root; exact allowed c

theorem evaluation {s} (t : signature.Occurrence s) : model.Evaluates initial t (specification t) := by
  induction t with
  | unit => rfl
  | cause c root => rfl
  | hole n h => exact Empty.elim h
  | operation g input ih =>
    change model.evaluate initial (.operation g input) = _
    rw [DeclaredArchitecture.evaluate, ite_eq_left trivial, ih]
    rcases h : specification input with ⟨a, b⟩
    cases g <;> simp only [specification, h] <;> cases a <;> cases b <;> rfl
  | tensor left right ihl ihr =>
    change model.evaluate initial (.tensor left right) = _
    rw [DeclaredArchitecture.evaluate, ihl, ihr]
    rfl

theorem input_exact (g : Bool) (t : signature.Occurrence (signature.input g)) (tuple) :
    model.reachInput g t tuple ↔ inputAdmissible g t tuple := by
  constructor
  · rintro ⟨w, hw, supplied, _⟩
    rw [world_unique w hw] at supplied
    exact ((evaluation t).deterministic supplied).symm
  · intro same
    exact ⟨initial, fun _ => rfl, same.symm ▸ evaluation t, trivial⟩

theorem input_valid (g : Bool) (t : signature.Occurrence (signature.input g)) : model.InputValid g t := by
  refine ⟨input_exact g t, ?_⟩
  intro i member
  constructor
  · rintro ⟨w, hw, supplied⟩
    rw [world_unique w hw] at supplied
    exact ⟨specification t, rfl, ((evaluation t).supplier i).deterministic supplied⟩
  · rintro ⟨tuple, allowed, same⟩
    obtain ⟨w, hw, ht, _⟩ := (input_exact g t tuple).mpr allowed
    exact ⟨w, hw, same ▸ ht.supplier i⟩

abbrev aOne : signature.Occurrence (.node false) :=
  ArchitectureSignature.Term.operation (S := signature) false (.tensor (ArchitectureSignature.Term.cause (S := signature) false ()) (ArchitectureSignature.Term.cause (S := signature) true ()))
abbrev bOne : signature.Occurrence (.node true) :=
  ArchitectureSignature.Term.operation (S := signature) true (.tensor aOne (ArchitectureSignature.Term.cause (S := signature) true ()))
abbrev nodeValue : (n : Bool) → Bool → signature.Occurrence (.node n)
  | false, false => ArchitectureSignature.Term.cause (S := signature) false () | false, true => aOne
  | true, false => ArchitectureSignature.Term.cause (S := signature) true () | true, true => bOne
theorem nodeValue_evaluation (n value : Bool) : model.Evaluates initial (nodeValue n value) value := by
  cases n <;> cases value <;> exact evaluation _
theorem nodeValue_origin (n value : Bool) : model.InCone n (nodeValue n value) := by
  cases n <;> cases value
  · exact ⟨⟨rfl, rfl⟩, fun _ => rfl⟩
  · exact ⟨Or.inl ⟨rfl, rfl⟩, ⟨fun _ => rfl, fun h => Bool.noConfusion h⟩⟩
  · exact ⟨⟨rfl, rfl⟩, fun _ => rfl⟩
  · exact ⟨Or.inr ⟨rfl, rfl⟩, ⟨⟨fun h => Bool.noConfusion h, fun _ => rfl⟩, fun _ => rfl⟩⟩

theorem nodeValue_provenance (n value : Bool) : (nodeValue n value).provenance marked =
    ProducerHistory.cause n () := by
  cases n <;> cases value <;> rfl

def observedTerminal (n value : Bool) : signature.Occurrence (model.effect n) :=
  match n with
  | false => .tensor (nodeValue false value) .unit
  | true => .tensor (nodeValue true value) .unit

theorem terminal_provenance (n value : Bool) : model.EffectProvenance n (observedTerminal n value) := by
  cases n <;> intro i <;> cases i with
  | inl i =>
    cases i
    first
      | change ((nodeValue false value).supplier ()).provenance marked = ProducerHistory.cause false ()
        rw [ArchitectureSignature.Term.supplier_node]
        exact nodeValue_provenance false value
      | change ((nodeValue true value).supplier ()).provenance marked = ProducerHistory.cause true ()
        rw [ArchitectureSignature.Term.supplier_node]
        exact nodeValue_provenance true value
  | inr impossible => exact Empty.elim impossible

theorem effectReach (c : Bool) (tuple : (model.effect c).vdp.MemberIndex) : model.reachEffect c tuple := by
  cases c <;> rcases tuple with ⟨value, u⟩ <;> cases u
  all_goals
    refine ⟨.tensor (nodeValue _ value) .unit, ?_, terminal_provenance _ value,
      initial, (fun _ => rfl), ?_, trivial⟩
    · intro i
      cases i with
      | inl i =>
        cases i
        first
          | change model.InCone false ((nodeValue false value).supplier ())
          | change model.InCone true ((nodeValue true value).supplier ())
        rw [ArchitectureSignature.Term.supplier_node]
        exact nodeValue_origin _ value
      | inr impossible => exact Empty.elim impossible
    · change model.evaluate initial (.tensor (nodeValue _ value) .unit) = some (value, ())
      rw [DeclaredArchitecture.evaluate, nodeValue_evaluation]
      rfl

@[archiscript_certificate] def certified : CertifiedDeclaredArchitecture where
  model := model
  causeNonempty := ⟨false⟩
  effectCoverage := ⟨by intro root; cases root; simp, by decide⟩
  inputs := by
    intro g t _
    exact .verified (input_valid g t) ⟨specification t, (input_exact g t _).mpr rfl⟩
  cones := by
    intro c
    cases c <;> refine ⟨by decide, ⟨(false, ()), effectReach _ _⟩, ?_, ?_⟩
    all_goals first
      | (intro tuple; exact ⟨fun _ => trivial, fun _ => effectReach _ tuple⟩)
      | (intro i value
         cases i with
         | inl i =>
           cases i
           exact ⟨fun _ => ⟨(value, ()), trivial, rfl⟩,
             fun _ => ⟨nodeValue _ value, nodeValue_origin _ value, nodeValue_provenance _ value, initial,
               (fun _ => rfl), nodeValue_evaluation _ value⟩⟩
         | inr impossible => exact Empty.elim impossible)
  boundariesComplete := by
    intro c n same
    change n = c at same
    subst c
    refine ⟨n, ?_, .refl _⟩
    cases n <;> change _ ∈ [_] <;> exact List.mem_cons_self

def pairTrace (pair : Bool × Bool) : signature.Occurrence (signature.input false) :=
  .tensor (nodeValue false pair.1) (nodeValue true pair.2)
def JointReach (pair : Bool × Bool) : Prop :=
  ∃ t, model.isInputContext false t ∧ model.reachInput false t pair
theorem joint_reachable (pair : Bool × Bool) : JointReach pair := by
  refine ⟨pairTrace pair, ⟨.inl (), ?_⟩, initial, (fun _ => rfl), ?_, trivial⟩
  · change model.InCone false ((nodeValue false pair.1).supplier ())
    rw [ArchitectureSignature.Term.supplier_node]
    exact nodeValue_origin false pair.1
  · change model.evaluate initial (.tensor (nodeValue false pair.1) (nodeValue true pair.2)) = some pair
    rw [DeclaredArchitecture.evaluate, nodeValue_evaluation, nodeValue_evaluation]

def analysis : Reachability.FiniteAnalysis (Bool × Bool) where
  states := [(false, false), (false, true), (true, false), (true, true)]
  complete := by intro ⟨a, b⟩; cases a <;> cases b <;> simp
  initial := fun pair => pair = (false, false)
  step := fun before after => after = (!before.2, before.2) ∨ after = (before.1, before.1)
  initialDecidable := inferInstance
  stepDecidable := inferInstance
  stateDecidableEq := inferInstance
def exactClosure : analysis.Exact :=
  ⟨analysis.compute 3, analysis.compute_sound 3, analysis.compute_complete_of_closed 3 (by decide)⟩
theorem closure_exact : Reachability.ExactAbstraction JointReach analysis where
  equivalent := by
    intro pair
    constructor
    · intro _
      apply analysis.compute_sound 3 pair
      rcases pair with ⟨a, b⟩; cases a <;> cases b <;> decide
    · intro _; exact joint_reachable pair
theorem computed_joint (pair : Bool × Bool) : pair ∈ exactClosure.members ↔ JointReach pair :=
  Reachability.certified_abstraction closure_exact exactClosure pair

#guard (analysis.certify 1).isNone
#guard (analysis.certify 3).isSome
#guard exactClosure.members.length == 4

end ArchiScriptExamples.MutualCones
