import ArchiScriptTests.SourceCoverage

namespace ArchiScriptTests.Unobservable
open ArchiScript ArchiScriptTests.SourceCoverage
inductive Arrow where | undefined | join deriving DecidableEq

abbrev signature : ArchitectureSignature := {
  SourceCoverage.signature with
  Generator := Arrow
  generatorDecidableEq := inferInstance
  generators := [.undefined, .join]
  generators_complete := by intro g; cases g <;> simp
  input | .undefined => .node .x | .join => .tensor (.node .y) (.node .y)
  output | .undefined => .y | .join => .effect
  operation | .undefined => ⟨fun _ => none⟩ | .join => ⟨fun pair => some pair.1⟩
  localFactor := by
    intro g; cases g
    · exact ⟨.x, List.mem_cons_self, rfl⟩
    · exact ⟨.y, by simp [Inputs.nodes], rfl⟩ }

abbrev basis : signature.ProvenanceAnalysis (fun _ => none) := derive_provenance([false], 2)

@[archiscript_contract] def inputAdmissible (g : Arrow)
    (_ : signature.Occurrence (signature.input g)) : (signature.input g).vdp.MemberIndex → Prop :=
  match g with
  | .undefined => fun _ => True
  | .join => fun _ => False

abbrev model : DeclaredArchitecture where
  signature := signature
  boundary := fun _ => True
  boundaryNonempty := ⟨fun _ _ => false, trivial⟩
  context := fun _ _ _ => True
  admissibleInput := inputAdmissible
  cyclicBoundary := fun _ => none
  effectAnalysis := basis
  effectContext := fun _ _ _ => True
  admissibleEffect := fun _ _ => False

theorem basis_valid : basis.Valid := ⟨by intro c; cases c; simp, by decide⟩

theorem silent_invariant (w : signature.World) {s} (t : signature.Occurrence s) :
    ∀ i : s.Position, s.nodeAt i ≠ .x → model.evaluate w (t.supplier i) = none := by
  induction t with
  | unit => intro i; exact Empty.elim i
  | cause c root => intro i different; cases c; exact False.elim (different rfl)
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih =>
    intro i _; cases i
    rw [ArchitectureSignature.Term.supplier_node]
    cases g with
    | undefined =>
      rw [DeclaredArchitecture.evaluate, ite_eq_left trivial]
      cases model.evaluate w input <;> rfl
    | join =>
      have absent := ih (.inl ()) (by decide)
      rw [DeclaredArchitecture.evaluate, ite_eq_left trivial]
      cases computed : model.evaluate w input with
      | none => rfl
      | some pair =>
        have supplied := (show model.Evaluates w input pair from computed).supplier (.inl ())
        change model.evaluate w (input.supplier (.inl ())) = some pair.1 at supplied
        rw [absent] at supplied
        cases supplied
  | tensor left right ihl ihr =>
    intro i different
    cases i with
    | inl i => exact ihl i different
    | inr i => exact ihr i different

theorem noYvalue (w : signature.World) (t : signature.Occurrence (.node .y)) (b : Bool) :
    ¬ model.Evaluates w t b := by
  intro supplied
  have absent := silent_invariant w t () (by decide)
  rw [ArchitectureSignature.Term.supplier_node] at absent
  have impossible : (none : Option Bool) = some b := absent.symm.trans supplied
  cases impossible

theorem noEffectValue (w : signature.World) (t : signature.Occurrence (.node .effect)) (b : Bool) :
    ¬ model.Evaluates w t b := by
  intro supplied
  have absent := silent_invariant w t () (by decide)
  rw [ArchitectureSignature.Term.supplier_node] at absent
  have impossible : (none : Option Bool) = some b := absent.symm.trans supplied
  cases impossible

theorem start_evaluation (b : Bool) {s} (t : signature.Occurrence s) :
    ∀ n (same : s = .node n), n = .x →
      model.Evaluates (fun _ _ => b) (show signature.Occurrence (.node n) from same ▸ t) b := by
  induction t with
  | unit => intro n same; cases same
  | cause c root => intro n same _; cases same; cases c; rfl
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih => intro n same atStart; cases same; cases g <;> cases atStart
  | tensor left right ihl ihr => intro n same; cases same

theorem join_no_incoming (i : (signature.input .join).Position) (b : Bool) :
    ¬ model.supplierImage ((signature.input .join).nodeAt i) b := by
  cases i <;> rename_i i <;> cases i
  all_goals
    rintro ⟨t, _, w, _, supplied⟩
    exact noYvalue w t b supplied

theorem input_status (g : Arrow) (t : signature.Occurrence (signature.input g)) :
    model.InputStatus g t := by
  cases g with
  | undefined =>
    have reach (b : Bool) : model.reachInput .undefined t b :=
      ⟨(fun _ _ => b), trivial, start_evaluation b t .x rfl rfl, trivial⟩
    refine .verified ⟨?_, ?_⟩ ⟨false, reach false⟩
    · intro b; exact ⟨fun _ => trivial, fun _ => reach b⟩
    · intro i b; cases i
      exact ⟨fun _ => ⟨b, trivial, rfl⟩,
        fun _ => ⟨(fun _ _ => b), trivial, (start_evaluation b t .x rfl rfl).supplier ()⟩⟩
  | join =>
    apply DeclaredArchitecture.InputStatus.unreachable
    · intro i b
      cases i <;> rename_i i <;> cases i
      all_goals
        rintro ⟨w, _, supplied⟩
        exact noYvalue w _ b supplied
    · intro tuple
      rintro ⟨w, _, supplied, _⟩
      exact noYvalue w (t.supplier (.inl ())) tuple.1 (supplied.supplier (.inl ()))
    · intro tuple impossible; exact impossible

theorem unobservable : model.NoObservableEffect () := by
  constructor
  · intro i b
    cases i with
    | inl i =>
      cases i
      rintro ⟨t, _, _, w, _, supplied⟩
      exact noEffectValue w t b supplied
    | inr impossible => exact Empty.elim impossible
  · intro tuple impossible; exact impossible

@[archiscript_certificate] def certified : CertifiedDeclaredArchitecture where
  model := model
  causeNonempty := ⟨()⟩
  effectCoverage := basis_valid
  inputSources := by
    intro g; cases g with
    | undefined => exact model.inputSources_of_catalog basis_valid .undefined (by decide)
    | join => exact .unreachable join_no_incoming
  inputs := fun g t _ => input_status g t
  cones := by intro c; cases c; exact .unobservable unobservable
  boundariesComplete := by intro c n _; cases c; exact Or.inl unobservable

-- Structural suppliers exist, yet neither factor has an incoming value.
abbrev unavailableInput : signature.Occurrence (signature.input .join) :=
  .tensor (ArchitectureSignature.Term.operation (S := signature) .undefined (.cause () false))
    (ArchitectureSignature.Term.operation (S := signature) .undefined (.cause () false))
example : model.isInputContext .join unavailableInput :=
  (model.isInputContext_iff_coherent .join unavailableInput).mpr ⟨rfl, rfl⟩
example (tuple : (model.effect ()).vdp.MemberIndex) : ¬ model.reachEffect () tuple :=
  unobservable.not_reachable tuple
example : Nonempty (model.effect ()).Position := ⟨.inl ()⟩

end ArchiScriptTests.Unobservable
