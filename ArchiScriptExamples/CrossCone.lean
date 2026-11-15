import ArchiScriptExamples.CyclicCone

/-! One Cause supplies B; an external Cause supplies A through a swap cycle.
The B Cone uses A ⊗ B with explicit factor derivations. No storage, scheduling
or universal Cartesian co-availability rule is inferred. -/
namespace ArchiScriptExamples.CrossCone
open ArchiScript
abbrev bit := SimpleCone.bit
inductive Port where | a | b | c deriving DecidableEq
inductive Arrow where | swap | join deriving DecidableEq
abbrev object : Port → VDP | .c => bit.tensor bit | _ => bit

abbrev signature : ArchitectureSignature where
  Node := Port
  nodeDecidableEq := inferInstance
  nodes := [.a, .b, .c]
  nodes_complete := by intro n; cases n <;> simp
  nodes_nodup := by decide
  object := object
  domains := [⟨Bool, bit.members false⟩, ⟨Bool, bit.members true⟩,
    ⟨Bool × Bool, (bit.tensor bit).members (false, false)⟩,
    ⟨Bool × Bool, (bit.tensor bit).members (false, true)⟩,
    ⟨Bool × Bool, (bit.tensor bit).members (true, false)⟩,
    ⟨Bool × Bool, (bit.tensor bit).members (true, true)⟩]
  memberDeclared := by
    intro n i; cases n <;> cases i <;> try simp
    rename_i a b; cases a <;> cases b <;> simp
  splits := []
  Cause := Bool
  causeDecidableEq := inferInstance
  causes := [false, true]
  causes_complete := by intro c; cases c <;> simp
  causes_nodup := by decide
  RootInstance := Unit
  rootDecidableEq := inferInstance
  origin := fun _ => ()
  start | false => .a | true => .b
  owner | .a => false | .b | .c => true
  start_owner := by intro c; cases c <;> rfl
  Generator := Arrow
  generatorDecidableEq := inferInstance
  generators := [.swap, .join]
  generators_complete := by intro g; cases g <;> simp
  input | .swap => .node .a | .join => .tensor (.node .a) (.node .b)
  output | .swap => .a | .join => .c
  operation | .swap => ⟨fun a => some (!a)⟩ | .join => Operation.id (bit.tensor bit)
  localFactor := by
    intro g; cases g
    · exact ⟨.a, List.mem_cons_self, rfl⟩
    · exact ⟨.b, by simp [Inputs.nodes], rfl⟩

def cycleEntry : signature.Term (fun n => PLift (Port.a = n)) (.node .a) :=
  ArchitectureSignature.Term.hole (S := signature) (Hole := fun n => PLift (Port.a = n)) .a ⟨rfl⟩
def cycleBoundary : ArchitectureSignature.Term.CycleBoundary signature .a where
  route := ArchitectureSignature.Term.operation (S := signature) (Hole := fun n => PLift (Port.a = n)) .swap cycleEntry
  oneEntry := rfl
  nontrivial := by decide

@[archiscript_contract] def inputAdmissible (g : Arrow)
    (t : signature.Occurrence (signature.input g)) : (signature.input g).vdp.MemberIndex → Prop :=
  match g with
  | .swap => fun a => a = CyclicCone.alternating t.operations
  | .join => fun pair => pair.1 = CyclicCone.alternating (t.supplier (.inl ())).operations

abbrev marked : (n : Port) → Option (ArchitectureSignature.Term.CycleBoundary signature n)
  | .a => some cycleBoundary
  | .b | .c => none

abbrev effectBasis : signature.ProvenanceAnalysis marked :=
  derive_provenance([()], 1)

@[archiscript_contract] def effectAdmissible (c : Bool) :
    (signature.effectInputs effectBasis c).vdp.MemberIndex → Prop := fun _ => True

abbrev model : DeclaredArchitecture where
  signature := signature
  boundary := fun w => w false () = false
  boundaryNonempty := ⟨fun c _ => match c with | false => false | true => false, rfl⟩
  context := fun _ _ _ => True
  admissibleInput := inputAdmissible
  cyclicBoundary := marked
  effectAnalysis := effectBasis
  effectContext := fun _ _ _ => True
  admissibleEffect := effectAdmissible

def world (b : Bool) : signature.World | false, _ => false | true, _ => b
theorem world_unique (w : signature.World) (allowed : model.boundary w) : w = world (w true ()) := by
  funext c root; cases root; cases c
  · exact allowed
  · rfl

theorem a_invariant (b : Bool) {s} (t : signature.Occurrence s) :
    ∀ same : s = .node .a, model.evaluate (world b)
      (show signature.Occurrence (.node .a) from same ▸ t) = some (CyclicCone.alternating t.operations) := by
  induction t with
  | unit => intro same; cases same
  | cause c root => cases c <;> intro same <;> cases same; rfl
  | hole n h => exact Empty.elim h
  | operation g input ih =>
    cases g
    · intro same; cases same
      rw [DeclaredArchitecture.evaluate, ite_eq_left trivial, ih rfl]
      rfl
    · intro same; cases same
  | tensor a b iha ihb => intro same; cases same

theorem b_invariant (b : Bool) {s} (t : signature.Occurrence s) :
    ∀ same : s = .node .b, model.evaluate (world b)
      (show signature.Occurrence (.node .b) from same ▸ t) = some b := by
  induction t with
  | unit => intro same; cases same
  | cause c root => cases c <;> intro same <;> cases same; rfl
  | hole n h => exact Empty.elim h
  | operation g input ih => cases g <;> intro same <;> cases same
  | tensor a b iha ihb => intro same; cases same

def expected (g : Arrow) (t : signature.Occurrence (signature.input g)) (b : Bool) :
    (signature.input g).vdp.MemberIndex :=
  match g with
  | .swap => CyclicCone.alternating t.operations
  | .join => (CyclicCone.alternating (t.supplier (.inl ())).operations, b)

theorem source_evaluation (g : Arrow) (t : signature.Occurrence (signature.input g)) (b : Bool) :
    model.Evaluates (world b) t (expected g t b) := by
  cases g with
  | swap => exact a_invariant b t rfl
  | join =>
    cases t with
    | tensor left right =>
      change model.evaluate (world b) (.tensor left right) = _
      rw [DeclaredArchitecture.evaluate, a_invariant b left rfl, b_invariant b right rfl]
      simp only [ArchitectureSignature.Term.supplier, ArchitectureSignature.Term.supplier_node, expected]

theorem input_image (g : Arrow) (t : signature.Occurrence (signature.input g)) (tuple) :
    model.reachInput g t tuple ↔ ∃ b, expected g t b = tuple := by
  constructor
  · rintro ⟨w, hw, supplied, _⟩
    rw [world_unique w hw] at supplied
    exact ⟨w true (), (source_evaluation g t _).deterministic supplied⟩
  · rintro ⟨b, same⟩
    exact ⟨world b, rfl, same ▸ source_evaluation g t b, trivial⟩

theorem input_exact (g : Arrow) (t : signature.Occurrence (signature.input g)) (tuple) :
    model.reachInput g t tuple ↔ inputAdmissible g t tuple := by
  rw [input_image]
  cases g with
  | swap => exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨false, h.symm⟩⟩
  | join =>
    constructor
    · rintro ⟨b, same⟩
      exact (congrArg Prod.fst same).symm
    · intro h
      exact ⟨tuple.2, Prod.ext h.symm rfl⟩

theorem input_valid (g : Arrow) (t : signature.Occurrence (signature.input g)) : model.InputValid g t := by
  refine ⟨input_exact g t, ?_⟩
  intro i member
  constructor
  · rintro ⟨w, hw, supplied⟩
    rw [world_unique w hw] at supplied
    have full := source_evaluation g t (w true ())
    have same := (full.supplier i).deterministic supplied
    exact ⟨expected g t (w true ()), (input_exact g t _).mp ⟨world (w true ()), rfl, full, trivial⟩, same⟩
  · rintro ⟨tuple, allowed, same⟩
    obtain ⟨w, hw, ht, _⟩ := (input_exact g t tuple).mpr allowed
    exact ⟨w, hw, same ▸ ht.supplier i⟩

abbrev aValue (a : Bool) : signature.Occurrence (.node .a) :=
  if a then ArchitectureSignature.Term.operation (S := signature) .swap
    (ArchitectureSignature.Term.cause (S := signature) false ())
  else ArchitectureSignature.Term.cause (S := signature) false ()
abbrev cValue (a : Bool) : signature.Occurrence (.node .c) :=
  ArchitectureSignature.Term.operation (S := signature) .join
    (.tensor (aValue a) (ArchitectureSignature.Term.cause (S := signature) true ()))

theorem aValue_evaluation (a b : Bool) : model.Evaluates (world b) (aValue a) a := by
  have h := a_invariant b (aValue a) rfl
  cases a <;> exact h

theorem cValue_evaluation (a b : Bool) : model.Evaluates (world b) (cValue a) (a, b) := by
  change model.evaluate (world b) (ArchitectureSignature.Term.operation (S := signature) Arrow.join (.tensor (aValue a) (ArchitectureSignature.Term.cause (S := signature) true ()))) = some (a, b)
  rw [DeclaredArchitecture.evaluate, ite_eq_left trivial]
  have ha := aValue_evaluation a b
  change model.evaluate (world b) (aValue a) = some a at ha
  rw [DeclaredArchitecture.evaluate, ha]
  rfl

def terminal : (c : Bool) → signature.Occurrence (model.effect c)
  | false => .tensor (aValue false) .unit
  | true => .tensor (cValue false) .unit

theorem aValue_origin (a : Bool) : model.InCone false (aValue a) := by
  cases a <;> exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem cValue_origin (a : Bool) : model.InCone true (cValue a) := by
  cases a <;> exact ⟨Or.inr ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem aValue_provenance (a : Bool) : (aValue a).provenance marked = ProducerHistory.cause false () := by
  cases a <;> rfl

theorem cValue_provenance (a : Bool) : (cValue a).provenance marked =
    ProducerHistory.operation Arrow.join (.tensor (.cause false ()) (.cause true ())) := by
  cases a <;> rfl

theorem terminal_provenance (c value : Bool) : model.EffectProvenance c
    (match c with | false => .tensor (aValue value) .unit | true => .tensor (cValue value) .unit) := by
  cases c <;> intro i <;> cases i with
  | inl i =>
    cases i
    first
      | change ((aValue value).supplier ()).provenance marked = ProducerHistory.cause false ()
        rw [ArchitectureSignature.Term.supplier_node]
        exact aValue_provenance value
      | change ((cValue value).supplier ()).provenance marked =
          ProducerHistory.operation Arrow.join (.tensor (.cause false ()) (.cause true ()))
        rw [ArchitectureSignature.Term.supplier_node]
        exact cValue_provenance value
  | inr impossible => exact Empty.elim impossible

theorem effectReach (c : Bool) (tuple : (model.effect c).vdp.MemberIndex) : model.reachEffect c tuple := by
  cases c with
  | false =>
    rcases tuple with ⟨a, u⟩; cases u
    refine ⟨.tensor (aValue a) .unit, ?_, terminal_provenance false a, world false, rfl, ?_, trivial, ⟨.inl ()⟩⟩
    · intro i
      cases i with
      | inl i =>
        cases i
        change model.InCone false ((aValue a).supplier ())
        rw [ArchitectureSignature.Term.supplier_node]
        exact aValue_origin a
      | inr impossible => exact Empty.elim impossible
    · change model.evaluate (world false) (.tensor (aValue a) .unit) = some (a, ())
      rw [DeclaredArchitecture.evaluate, aValue_evaluation a false]
      rfl
  | true =>
    rcases tuple with ⟨⟨a, b⟩, u⟩; cases u
    refine ⟨.tensor (cValue a) .unit, ?_, terminal_provenance true a, world b, rfl, ?_, trivial, ⟨.inl ()⟩⟩
    · intro i
      cases i with
      | inl i =>
        cases i
        change model.InCone true ((cValue a).supplier ())
        rw [ArchitectureSignature.Term.supplier_node]
        exact cValue_origin a
      | inr impossible => exact Empty.elim impossible
    · change model.evaluate (world b) (.tensor (cValue a) .unit) = some ((a, b), ())
      rw [DeclaredArchitecture.evaluate, cValue_evaluation a b]
      rfl

theorem basis_valid : model.effectAnalysis.Valid :=
  ⟨by intro c; cases c <;> simp, by decide⟩

@[archiscript_certificate] def certified : CertifiedDeclaredArchitecture where
  model := model
  causeNonempty := ⟨false⟩
  effectCoverage := basis_valid
  inputSources := by
    intro g
    exact model.inputSources_of_catalog basis_valid g (by cases g <;> exact of_decide_eq_true rfl)
  inputs := by
    intro g t _
    exact .verified (input_valid g t) ⟨expected g t false, (input_image g t _).mpr ⟨false, rfl⟩⟩
  cones := by
    intro c
    apply DeclaredArchitecture.ConeStatus.observable
    cases c with
    | false =>
      refine ⟨⟨.inl ()⟩, ⟨(false, ()), effectReach false _⟩, ?_, ?_⟩
      · intro tuple; exact ⟨fun _ => trivial, fun _ => effectReach false tuple⟩
      · intro i a
        cases i with
        | inl i =>
          cases i
          exact ⟨fun _ => ⟨(a, ()), trivial, rfl⟩,
            fun _ => ⟨aValue a, aValue_origin a, aValue_provenance a,
              world false, rfl, aValue_evaluation a false⟩⟩
        | inr impossible => exact Empty.elim impossible
    | true =>
      refine ⟨⟨.inl ()⟩, ⟨((false, false), ()), effectReach true _⟩, ?_, ?_⟩
      · intro tuple; exact ⟨fun _ => trivial, fun _ => effectReach true tuple⟩
      · intro i pair
        cases i with
        | inl i =>
          cases i
          exact ⟨fun _ => ⟨(pair, ()), trivial, rfl⟩,
            fun _ => ⟨cValue pair.1, cValue_origin _, cValue_provenance _,
              world pair.2, rfl, cValue_evaluation _ _⟩⟩
        | inr impossible => exact Empty.elim impossible
  boundariesComplete := by
    intro c n owns
    apply Or.inr
    cases n with
    | a =>
      cases owns
      exact ⟨.a, by change Port.a ∈ [Port.a]; exact List.mem_cons_self, .refl _⟩
    | b =>
      cases owns
      refine ⟨.c, ?_, ArchitectureSignature.Depends.step (S := signature) .join .b ?_⟩
      · change Port.c ∈ [Port.c]; exact List.mem_cons_self
      · simp [Inputs.nodes]
    | c =>
      cases owns
      exact ⟨.c, by change Port.c ∈ [Port.c]; exact List.mem_cons_self, .refl _⟩

end ArchiScriptExamples.CrossCone
