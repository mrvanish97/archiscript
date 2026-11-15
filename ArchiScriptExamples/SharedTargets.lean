import ArchiScriptExamples.SimpleCone

namespace ArchiScriptExamples.SharedTargets
open ArchiScript
abbrev bit := SimpleCone.bit

/-- X=0, A=1, B=2, C=3, followed by one shared suffix. The first four
Operations are p,q,f,g; each additional Operation is declared exactly once. -/
def sourceIndex (length : Nat) (g : Fin (length + 4)) : Fin (length + 4) :=
  ⟨if g.val < 2 then 0 else if g.val = 2 then 1 else if g.val = 3 then 2 else g.val - 1, by
    split
    · omega
    · split
      · omega
      · split <;> omega⟩

def targetIndex (length : Nat) (g : Fin (length + 4)) : Fin (length + 4) :=
  ⟨if g.val = 0 then 1 else if g.val = 1 then 2 else if g.val < 4 then 3 else g.val, by
    split
    · omega
    · split
      · omega
      · split <;> omega⟩

abbrev signature (length : Nat) (rightMeaning : Bool → Bool) : ArchitectureSignature where
  Node := Fin (length + 4)
  nodeDecidableEq := inferInstance
  nodes := List.finRange (length + 4)
  nodes_complete := List.mem_finRange
  nodes_nodup := List.nodup_finRange _
  object := fun _ => bit
  domains := [⟨Bool, bit.members false⟩, ⟨Bool, bit.members true⟩]
  memberDeclared := by intro n i; cases i <;> simp
  splits := []
  Cause := Unit
  causeDecidableEq := inferInstance
  causes := [()]
  causes_complete := by intro c; cases c; simp
  causes_nodup := by simp
  RootInstance := Unit
  rootDecidableEq := inferInstance
  origin := fun _ => ()
  start := fun _ => ⟨0, by omega⟩
  owner := fun _ => ()
  start_owner := fun _ => rfl
  Generator := Fin (length + 4)
  generatorDecidableEq := inferInstance
  generators := List.finRange (length + 4)
  generators_complete := List.mem_finRange
  input := fun g => .node (sourceIndex length g)
  output := targetIndex length
  operation := fun g => ⟨fun b => some (if g.val = 3 then rightMeaning b else b)⟩
  localFactor := fun g => ⟨sourceIndex length g, List.mem_cons_self, rfl⟩

/-- Independent truth-table intention: g is the only policy-transforming
arrow; p,q,f and every shared suffix arrow preserve their input member. -/
def intended (length : Nat) (policy : Bool → Bool) (root : Bool) :
    (signature length policy).History → Bool
  | .cause _ _ => root
  | .operation g input => if g.val = 3 then policy (intended length policy root input)
      else intended length policy root input
  | .unit | .tensor _ _ => false

noncomputable def specification (length : Nat) (policy : Bool → Bool)
    {s : Inputs (signature length policy).Node (signature length policy).object}
    (t : (signature length policy).Occurrence s) : Bool → s.vdp.MemberIndex := by
  induction t with
  | unit => exact fun _ => ()
  | cause => exact fun root => root
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih => exact fun root => if g.val = 3 then policy (ih root) else ih root
  | tensor left right ihl ihr => exact fun root => (ihl root, ihr root)

@[archiscript_contract] def inputAdmissible (length : Nat) (policy : Bool → Bool)
    (_g : (signature length policy).Generator)
    (t : (signature length policy).Occurrence ((signature length policy).input _g))
    (value : Bool) : Prop := ∃ root, value = specification length policy t root

def expected (length : Nat) (policy : Bool → Bool) (root : Bool) :
    (coordinates : List ((signature length policy).Node × (signature length policy).History)) →
    (Inputs.ofNodes (object := (signature length policy).object)
      (coordinates.map Prod.fst)).vdp.MemberIndex
  | [] => ()
  | (_, history) :: rest => (intended length policy root history, expected length policy root rest)

@[archiscript_contract] def effectAdmissible (length : Nat) (policy : Bool → Bool)
    (basis : (signature length policy).ProvenanceAnalysis (fun _ => none)) (_ : Unit)
    (tuple : ((signature length policy).effectInputs basis ()).vdp.MemberIndex) : Prop :=
  ∃ root, tuple = expected length policy root ((signature length policy).effectCoordinates basis ())

abbrev model (length : Nat) (policy : Bool → Bool)
    (basis : (signature length policy).ProvenanceAnalysis (fun _ => none)) : DeclaredArchitecture where
  signature := signature length policy
  boundary := fun _ => True
  boundaryNonempty := ⟨fun _ _ => false, trivial⟩
  context := fun _ _ _ => True
  admissibleInput := inputAdmissible length policy
  cyclicBoundary := fun _ => none
  effectAnalysis := basis
  effectContext := fun _ _ _ => True
  admissibleEffect := effectAdmissible length policy basis

def world (length : Nat) (policy : Bool → Bool) (value : Bool) :
    (signature length policy).World := fun _ _ => value

theorem evaluation (length : Nat) (policy : Bool → Bool) (basis)
    (w : (signature length policy).World) {s} (t : (signature length policy).Occurrence s) :
    (model length policy basis).evaluate w t = some (specification length policy t (w () ())) := by
  induction t with
  | unit => rfl
  | cause c root => cases c; cases root; rfl
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih =>
    rw [DeclaredArchitecture.evaluate, ite_eq_left trivial, ih]
    rfl
  | tensor left right ihl ihr =>
    simp only [DeclaredArchitecture.evaluate, specification, ihl, ihr]

theorem node_specification (length : Nat) (policy : Bool → Bool) {s}
    (t : (signature length policy).Occurrence s) :
    ∀ n (same : s = .node n) (root : Bool),
      specification length policy
        (show (signature length policy).Occurrence (.node n) from same ▸ t) root =
          intended length policy root t.history := by
  induction t with
  | unit => intro n same; cases same
  | cause c instanceId => intro n same root; cases same; rfl
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih =>
    intro n same root; cases same
    have previous := ih (sourceIndex length g) rfl root
    change specification length policy input root = intended length policy root input.history at previous
    change (if g.val = 3 then policy (specification length policy input root)
      else specification length policy input root) =
        if g.val = 3 then policy (intended length policy root input.history)
        else intended length policy root input.history
    rw [previous]
  | tensor left right ihl ihr => intro n same; cases same

theorem input_exact (length : Nat) (policy : Bool → Bool) (basis) (g)
    (t : (signature length policy).Occurrence ((signature length policy).input g)) (value) :
    (model length policy basis).reachInput g t value ↔ inputAdmissible length policy g t value := by
  constructor
  · rintro ⟨w, _, supplied, _⟩
    exact ⟨w () (), (Option.some.inj ((evaluation length policy basis w t).symm.trans supplied)).symm⟩
  · rintro ⟨root, same⟩
    exact ⟨world length policy root, trivial,
      (evaluation length policy basis _ t).trans (congrArg some same.symm), trivial⟩

theorem input_valid (length : Nat) (policy : Bool → Bool) (basis) (g)
    (t : (signature length policy).Occurrence ((signature length policy).input g)) :
    (model length policy basis).InputValid g t := by
  refine ⟨input_exact length policy basis g t, ?_⟩
  intro i value; cases i
  constructor
  · rintro ⟨w, allowed, supplied⟩
    rw [ArchitectureSignature.Term.supplier_node] at supplied
    exact ⟨value, (input_exact length policy basis g t value).mp ⟨w, allowed, supplied, trivial⟩, rfl⟩
  · rintro ⟨tuple, admissible, same⟩
    obtain ⟨w, hw, ht, _⟩ := (input_exact length policy basis g t tuple).mpr admissible
    exact ⟨w, hw, same ▸ ht.supplier ()⟩

theorem expected_coordinate (length : Nat) (policy : Bool → Bool)
    (coordinates : List ((signature length policy).Node × (signature length policy).History))
    (root : Bool) (i : (Inputs.ofNodes (object := (signature length policy).object)
      (coordinates.map Prod.fst)).Position) :
    (Inputs.ofNodes (object := (signature length policy).object) (coordinates.map Prod.fst)).coordinate
      (expected length policy root coordinates) i =
      intended length policy root (ArchitectureSignature.coordinateHistory coordinates i) := by
  induction coordinates with
  | nil => exact Empty.elim i
  | cons head rest ih =>
    cases i with
    | inl i => cases i; rfl
    | inr i => exact ih i

theorem effect_evaluation (length : Nat) (policy : Bool → Bool) (basis)
    (t : (signature length policy).Occurrence ((model length policy basis).effect ()))
    (history : (model length policy basis).EffectProvenance () t)
    (w : (signature length policy).World) (tuple)
    (supplied : (model length policy basis).Evaluates w t tuple) :
    tuple = expected length policy (w () ()) ((signature length policy).effectCoordinates basis ()) := by
  apply Inputs.coordinate_ext
  intro i
  have actual := supplied.supplier i
  have semantic := evaluation length policy basis w (t.supplier i)
  have value := Option.some.inj (semantic.symm.trans actual)
  have meaning := node_specification length policy (t.supplier i) _ rfl (w () ())
  have source := history i
  rw [ArchitectureSignature.Term.provenance_without_cycles] at source
  rw [source] at meaning
  exact value.symm.trans (meaning.trans (expected_coordinate length policy _ _ i).symm)

theorem effectReach (length : Nat) (policy : Bool → Bool) (basis)
    (verified : basis.Valid) (root : Bool) :
    (model length policy basis).reachEffect ()
      (expected length policy root ((signature length policy).effectCoordinates basis ())) := by
  obtain ⟨t, origins, histories⟩ := (model length policy basis).effect_realized verified ()
  have supplied : (model length policy basis).Evaluates (world length policy root) t
      (specification length policy t root) := evaluation length policy basis _ t
  have same := effect_evaluation length policy basis t histories (world length policy root) _ supplied
  exact ⟨t, origins, histories, world length policy root, trivial, same ▸ supplied, trivial⟩

theorem effect_exact (length : Nat) (policy : Bool → Bool) (basis)
    (verified : basis.Valid) (tuple) :
    (model length policy basis).reachEffect () tuple ↔ effectAdmissible length policy basis () tuple := by
  constructor
  · rintro ⟨t, _, histories, w, _, supplied, _⟩
    exact ⟨w () (), effect_evaluation length policy basis t histories w tuple supplied⟩
  · rintro ⟨root, same⟩
    exact same ▸ effectReach length policy basis verified root

def terminalIndex (length : Nat) : Fin (length + 4) := ⟨length + 3, by omega⟩

def baseIndex (length : Nat) (index : Fin 4) : Fin (length + 4) :=
  ⟨index.val, Nat.lt_of_lt_of_le index.isLt (by omega)⟩

theorem to_terminal (length : Nat) (policy : Bool → Bool) (node : Fin (length + 4)) :
    (signature length policy).Depends node (terminalIndex length) := by
  have walk : ∀ distance (current : Fin (length + 4)),
      current.val + distance = length + 3 → 3 ≤ current.val →
      (signature length policy).Depends current (terminalIndex length) := by
    intro distance
    induction distance with
    | zero =>
      intro current atEnd _
      have same : current = terminalIndex length := Fin.ext (by change current.val = length + 3; omega)
      rw [same]
      exact ArchitectureSignature.Depends.refl (S := signature length policy) _
    | succ distance ih =>
      intro current remaining afterBranch
      let next : Fin (length + 4) := ⟨current.val + 1, by omega⟩
      have source : sourceIndex length next = current := by
        apply Fin.ext
        dsimp [sourceIndex, next]
        split
        · omega
        · split
          · omega
          · split <;> omega
      have target : targetIndex length next = next := by
        apply Fin.ext
        dsimp [targetIndex, next]
        split
        · omega
        · split <;> omega
      have step : (signature length policy).Depends current (targetIndex length next) :=
        ArchitectureSignature.Depends.step (S := signature length policy) next current
          (by change current ∈ [sourceIndex length next]; rw [source]; exact List.mem_cons_self)
      rw [target] at step
      exact .trans step (ih next (by dsimp [next]; omega) (by dsimp [next]; omega))
  have fromC := walk length (baseIndex length ⟨3, by decide⟩)
    (by dsimp [baseIndex]; omega) (by dsimp [baseIndex]; omega)
  by_cases atX : node.val = 0
  · have same : node = baseIndex length ⟨0, by decide⟩ := Fin.ext atX
    subst node
    exact .trans (ArchitectureSignature.Depends.step (S := signature length policy) ⟨0, by omega⟩ _ List.mem_cons_self)
      (.trans (ArchitectureSignature.Depends.step (S := signature length policy) ⟨2, by omega⟩ _ List.mem_cons_self) fromC)
  by_cases atA : node.val = 1
  · have same : node = baseIndex length ⟨1, by decide⟩ := Fin.ext atA
    subst node
    exact .trans (ArchitectureSignature.Depends.step (S := signature length policy) ⟨2, by omega⟩ _ List.mem_cons_self) fromC
  by_cases atB : node.val = 2
  · have same : node = baseIndex length ⟨2, by decide⟩ := Fin.ext atB
    subst node
    exact .trans (ArchitectureSignature.Depends.step (S := signature length policy) ⟨3, by omega⟩ _ List.mem_cons_self) fromC
  exact walk (length + 3 - node.val) node (by omega) (by omega)

abbrev certificate (length : Nat) (policy : Bool → Bool)
    (basis : (signature length policy).ProvenanceAnalysis (fun _ => none))
    (verified : basis.Valid)
    (terminal : terminalIndex length ∈ (signature length policy).effectNodes (fun _ => none) ()) :
    CertifiedDeclaredArchitecture where
  model := model length policy basis
  causeNonempty := ⟨()⟩
  effectCoverage := verified
  inputs := by
    intro g t _
    exact .verified (input_valid length policy basis g t)
      ⟨specification length policy t false, (input_exact length policy basis g t _).mpr ⟨false, rfl⟩⟩
  cones := by
    intro c; cases c
    refine ⟨?_, ⟨_, effectReach length policy basis verified false⟩,
      effect_exact length policy basis verified, ?_⟩
    · intro empty
      rw [empty] at terminal
      cases terminal
    · intro i member
      constructor
      · rintro ⟨t, _, history, w, _, supplied⟩
        have value := Option.some.inj ((evaluation length policy basis w t).symm.trans supplied)
        have meaning := node_specification length policy t _ rfl (w () ())
        rw [ArchitectureSignature.Term.provenance_without_cycles] at history
        rw [history] at meaning
        exact ⟨_, ⟨w () (), rfl⟩,
          (expected_coordinate length policy _ (w () ()) i).trans (meaning.symm.trans value)⟩
      · rintro ⟨tuple, admissible, same⟩
        obtain ⟨t, origins, histories, w, allowed, supplied, _⟩ :=
          (effect_exact length policy basis verified tuple).mpr admissible
        exact ⟨t.supplier i, origins i, histories i, w, allowed, same ▸ supplied.supplier i⟩
  boundariesComplete := by
    intro c n _; cases c
    exact ⟨terminalIndex length, terminal, to_terminal length policy n⟩

abbrev baseBasis (policy : Bool → Bool) :
    (signature 0 policy).ProvenanceAnalysis (fun _ => none) := derive_provenance([()], 2)
abbrev suffixBasis (policy : Bool → Bool) :
    (signature 2 policy).ProvenanceAnalysis (fun _ => none) := derive_provenance([()], 4)

abbrev baseCertificate (policy : Bool → Bool) : CertifiedDeclaredArchitecture :=
  certificate 0 policy (baseBasis policy)
    ⟨by intro root; cases root; simp, by exact of_decide_eq_true rfl⟩
    (by exact of_decide_eq_true rfl)

abbrev suffixCertificate (policy : Bool → Bool) : CertifiedDeclaredArchitecture :=
  certificate 2 policy (suffixBasis policy)
    ⟨by intro root; cases root; simp, by exact of_decide_eq_true rfl⟩
    (by exact of_decide_eq_true rfl)

@[archiscript_certificate] abbrev equalImages : CertifiedDeclaredArchitecture := baseCertificate id
@[archiscript_certificate] abbrev differentImages : CertifiedDeclaredArchitecture := baseCertificate (fun _ => true)
@[archiscript_certificate] abbrev correlatedImages : CertifiedDeclaredArchitecture := baseCertificate Bool.not
@[archiscript_certificate] abbrev sharedSuffix : CertifiedDeclaredArchitecture := suffixCertificate id
@[archiscript_certificate] abbrev differentSuffix : CertifiedDeclaredArchitecture := suffixCertificate (fun _ => true)

-- Both routes target one C; both suffix routes end at one E.
#guard (signature 0 id).output ⟨2, by decide⟩ == (signature 0 id).output ⟨3, by decide⟩
#guard ((signature 0 id).effectCoordinates (baseBasis id) ()).map (fun coordinate => coordinate.1.val) == [3, 3]
#guard ((signature 2 id).effectCoordinates (suffixBasis id) ()).map (fun coordinate => coordinate.1.val) == [5, 5]
#guard (signature 2 id).nodes.length == 6
#guard (signature 2 id).generators.length == 6

abbrev leftC (length : Nat) (policy : Bool → Bool) :
    (signature length policy).Occurrence (.node (baseIndex length ⟨3, by decide⟩)) :=
  ArchitectureSignature.Term.operation (S := signature length policy) (baseIndex length ⟨2, by decide⟩)
    (ArchitectureSignature.Term.operation (S := signature length policy) (baseIndex length ⟨0, by decide⟩)
      (ArchitectureSignature.Term.cause (S := signature length policy) () ()))

abbrev rightC (length : Nat) (policy : Bool → Bool) :
    (signature length policy).Occurrence (.node (baseIndex length ⟨3, by decide⟩)) :=
  ArchitectureSignature.Term.operation (S := signature length policy) (baseIndex length ⟨3, by decide⟩)
    (ArchitectureSignature.Term.operation (S := signature length policy) (baseIndex length ⟨1, by decide⟩)
      (ArchitectureSignature.Term.cause (S := signature length policy) () ()))

/-- One authored h;k, supplied by either derivation into the very same C. -/
def sharedChain : Expression (signature 2 id).generatorsInventory
    (.node ⟨3, by decide⟩) (.node ⟨5, by decide⟩) :=
  Expression.step (G := (signature 2 id).generatorsInventory) ⟨5, by decide⟩
    (Expression.step (G := (signature 2 id).generatorsInventory) ⟨4, by decide⟩ (.identity _))

theorem shared_chain_distinguishes_producers :
    (sharedChain.supply (leftC 2 id)).provenance (fun _ => none) ≠
      (sharedChain.supply (rightC 2 id)).provenance (fun _ => none) :=
  sharedChain.supply_preserves_provenance (fun _ => none)
    (by change (True ∧ none = none) ∧ none = none; exact ⟨⟨trivial, rfl⟩, rfl⟩)
    _ _ (by decide)

theorem base_joint_relation (policy : Bool → Bool) (left right : Bool) :
    (baseCertificate policy).model.reachEffect () (left, (right, ())) ↔ right = policy left := by
  apply Iff.trans (effect_exact 0 policy (baseBasis policy) (baseCertificate policy).effectCoverage _)
  change (∃ root : Bool, (left, (right, ())) = (root, (policy root, ()))) ↔ _
  constructor
  · rintro ⟨root, same⟩; cases same; rfl
  · intro same; exact ⟨left, by rw [same]⟩

theorem suffix_joint_relation (policy : Bool → Bool) (left right : Bool) :
    (suffixCertificate policy).model.reachEffect () (left, (right, ())) ↔ right = policy left := by
  apply Iff.trans (effect_exact 2 policy (suffixBasis policy) (suffixCertificate policy).effectCoverage _)
  change (∃ root : Bool, (left, (right, ())) = (root, (policy root, ()))) ↔ _
  constructor
  · rintro ⟨root, same⟩; cases same; rfl
  · intro same; exact ⟨left, by rw [same]⟩

theorem incoming_left_image (policy : Bool → Bool) (value : Bool) :
    (baseCertificate policy).model.effectIncoming () (.inl ()) value := by
  apply (((baseCertificate policy).cones ()).2.2.2 (.inl ()) value).mpr
  exact ⟨(value, (policy value, ())), ⟨value, rfl⟩, rfl⟩

theorem incoming_right_image (policy : Bool → Bool) (value : Bool) :
    (baseCertificate policy).model.effectIncoming () (.inr (.inl ())) value ↔
      ∃ root, value = policy root := by
  apply Iff.trans (((baseCertificate policy).cones ()).2.2.2 (.inr (.inl ())) value)
  change (∃ tuple : Bool × (Bool × Unit),
    (∃ root, tuple = (root, (policy root, ()))) ∧ tuple.2.1 = value) ↔ _
  constructor
  · rintro ⟨tuple, ⟨root, same⟩, coordinate⟩
    cases same
    exact ⟨root, coordinate.symm⟩
  · rintro ⟨root, same⟩
    exact ⟨(root, (policy root, ())), ⟨root, rfl⟩, same.symm⟩

end ArchiScriptExamples.SharedTargets
