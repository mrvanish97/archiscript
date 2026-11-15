import ArchiScript.Provenance

namespace ArchiScript

/-- Declared context/availability assumptions and independent domain contracts.
These are mathematical model inputs, not runtime persistence or liveness rules.
The reference reachability relation is defined afterwards. -/
structure DeclaredArchitecture where
  signature : ArchitectureSignature
  boundary : signature.World → Prop
  boundaryNonempty : ∃ w, boundary w
  context : (g : signature.Generator) → signature.Occurrence (signature.input g) →
    signature.World → Prop
  admissibleInput : (g : signature.Generator) → signature.Occurrence (signature.input g) →
    (signature.input g).vdp.MemberIndex → Prop
  cyclicBoundary : (n : signature.Node) → Option (ArchitectureSignature.Term.CycleBoundary signature n)
  effectAnalysis : signature.ProvenanceAnalysis cyclicBoundary
  effectContext : (c : signature.Cause) →
    signature.Occurrence (signature.effectInputs effectAnalysis c) → signature.World → Prop
  admissibleEffect : (c : signature.Cause) →
    (signature.effectInputs effectAnalysis c).vdp.MemberIndex → Prop

namespace DeclaredArchitecture

abbrev S (a : DeclaredArchitecture) := a.signature

/-- Reference denotation of a finite provenance derivation. Quantification
over all such terms includes every finite traversal of a recursive generator
inventory. This function is not an executable saturation algorithm. -/
noncomputable def evaluate (a : DeclaredArchitecture) (world : a.S.World) :
    {s : Inputs a.S.Node a.S.object} → a.S.Occurrence s → Option s.vdp.MemberIndex
  | _, .unit => some ()
  | _, .cause c root => some (world c root)
  | _, .hole _ impossible => nomatch impossible
  | _, .operation g input =>
    letI := Classical.propDecidable (a.context g input world)
    if a.context g input world then (a.evaluate world input).bind (a.S.operation g).run else none
  | _, .tensor left right =>
    match a.evaluate world left, a.evaluate world right with
    | some i, some j => some (i, j)
    | _, _ => none

def Evaluates (a : DeclaredArchitecture) (world : a.S.World)
    {s : Inputs a.S.Node a.S.object} (t : a.S.Occurrence s)
    (tuple : s.vdp.MemberIndex) : Prop := a.evaluate world t = some tuple

/-- Changing the proposed input contract does not change the reference
producer semantics. Agreement with that contract remains a separate proof. -/
theorem evaluate_inputContract (a : DeclaredArchitecture)
    (contract : (g : a.S.Generator) → a.S.Occurrence (a.S.input g) →
      (a.S.input g).vdp.MemberIndex → Prop)
    (world : a.S.World) {s} (t : a.S.Occurrence s) :
    ({ a with admissibleInput := contract } : DeclaredArchitecture).evaluate world t =
      a.evaluate world t := by
  induction t with
  | unit | cause => rfl
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih => simp only [evaluate, ih]
  | tensor left right ihl ihr =>
    simp only [evaluate, ihl, ihr]
    cases a.evaluate world left <;> cases a.evaluate world right <;> rfl

/-- A reusable invariant for a particular architecture interpretation. This
does not impose stationary values on cyclic models: the premises must hold. -/
theorem evaluate_of_assignment (a : DeclaredArchitecture) (world : a.S.World)
    (values : (n : a.S.Node) → (a.S.object n).MemberIndex)
    (roots : ∀ c root, world c root = values (a.S.start c))
    (maps : ∀ g, a.S.operation g ((a.S.input g).assign values) = some (values (a.S.output g)))
    (available : ∀ g t, a.context g t world) {s} (t : a.S.Occurrence s) :
    a.evaluate world t = some (s.assign values) := by
  induction t with
  | unit => rfl
  | cause c root => exact congrArg some (roots c root)
  | hole n h => exact Empty.elim h
  | operation g input ih =>
    simp only [evaluate]
    split
    · rw [ih]
      exact maps g
    · rename_i missing
      exact False.elim (missing (available g input))
  | tensor left right ihl ihr =>
    simp only [evaluate, ihl, ihr, Inputs.assign]

theorem Evaluates.deterministic {a : DeclaredArchitecture} {w s}
    {t : a.S.Occurrence s} {i j} (hi : a.Evaluates w t i) (hj : a.Evaluates w t j) : i = j :=
  Option.some.inj (hi.symm.trans hj)

theorem Evaluates.supplier {a : DeclaredArchitecture} {w s}
    {t : a.S.Occurrence s} {tuple} (h : a.Evaluates w t tuple) (i : s.Position) :
    a.Evaluates w (t.supplier i) (s.coordinate tuple i) := by
  induction t with
  | unit => exact Empty.elim i
  | cause c root =>
    cases i
    simpa only [Evaluates, ArchitectureSignature.Term.supplier, Inputs.coordinate, Inputs.nodeAt] using h
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih =>
    cases i
    simpa only [Evaluates, ArchitectureSignature.Term.supplier, Inputs.coordinate, Inputs.nodeAt] using h
  | @tensor l r left right ihl ihr =>
    rcases tuple with ⟨x, y⟩
    unfold Evaluates at h
    simp only [evaluate] at h
    cases hl : a.evaluate w left <;> cases hr : a.evaluate w right <;>
      simp only [hl, hr, reduceCtorEq] at h
    rcases h with ⟨rfl, rfl⟩
    cases i with
    | inl k => exact ihl hl k
    | inr k => exact ihr hr k

def InCone (a : DeclaredArchitecture) (c : a.S.Cause) {s}
    (t : a.S.Occurrence s) : Prop :=
  t.hasRoot c (a.S.origin c) ∧ t.RootCoherent

/-- Derived actual uses belonging to the owning Cone. Exact root provenance
is required; a wholly external tensor is not an internal join of this Cone. -/
def isInputContext (a : DeclaredArchitecture) (g : a.S.Generator)
    (t : a.S.Occurrence (a.S.input g)) : Prop :=
  t.RootCoherent ∧ ∃ i, a.InCone (a.S.owner (a.S.output g)) (t.supplier i)

theorem isInputContext_iff_coherent (a : DeclaredArchitecture) (g : a.S.Generator)
    (t : a.S.Occurrence (a.S.input g)) : a.isInputContext g t ↔ t.RootCoherent := by
  constructor
  · exact And.left
  · intro coherent
    obtain ⟨n, member, own⟩ := a.S.localFactor g
    obtain ⟨i, same⟩ := (a.S.input g).node_position member
    have supplierCoherent := coherent.supplier i
    have origin := (t.supplier i).owned_origin (supplierCoherent.local _)
    refine ⟨coherent, i, ?_, supplierCoherent⟩
    simpa only [same, own] using origin

theorem input_consequence_inCone (a : DeclaredArchitecture) (g : a.S.Generator)
    (t : a.S.Occurrence (a.S.input g)) (supported : a.isInputContext g t) :
    a.InCone (a.S.owner (a.S.output g)) (ArchitectureSignature.Term.operation g t) :=
  ⟨(ArchitectureSignature.Term.operation g t).owned_origin (supported.1.local _), supported.1⟩

/-- Incoming images are obtained from each supplier before restricting the
current join. An orphan therefore cannot disappear by definition. -/
def incoming (a : DeclaredArchitecture) {s} (t : a.S.Occurrence s)
    (i : s.Position) (member : (a.S.object (s.nodeAt i)).MemberIndex) : Prop :=
  ∃ w, a.boundary w ∧ a.Evaluates w (t.supplier i) member

/-- A factor's possible values from all coherent upstream producers. This can
be asked before any complete input tuple or input term exists. Individual
producer identities remain explicit in `incoming` and `InputValid`. -/
def supplierImage (a : DeclaredArchitecture) (n : a.S.Node)
    (member : (a.S.object n).MemberIndex) : Prop :=
  ∃ t : a.S.Occurrence (.node n), t.RootCoherent ∧
    ∃ w, a.boundary w ∧ a.Evaluates w t member

/-- Every declared generator must either have a rooted supplier at every
factor, or prove that *all* independently derived incoming images are empty.
A missing partner cannot remove this per-generator obligation. -/
inductive InputSources (a : DeclaredArchitecture) (g : a.S.Generator) : Prop where
  | grounded (suppliers : ∀ i : (a.S.input g).Position,
      ∃ t : a.S.Occurrence (.node ((a.S.input g).nodeAt i)), t.RootCoherent)
  | unreachable (noIncoming : ∀ i member, ¬ a.supplierImage ((a.S.input g).nodeAt i) member)

theorem inputSources_of_catalog (a : DeclaredArchitecture) (verified : a.effectAnalysis.Valid)
    (g : a.S.Generator) (present : a.effectAnalysis.SourcesPresent g) : a.InputSources g := by
  apply InputSources.grounded
  intro i
  have available := present _ ((a.S.input g).nodeAt_mem i)
  cases catalog : a.effectAnalysis.catalog (a.S.owner (a.S.output g)) ((a.S.input g).nodeAt i) with
  | nil => simp [catalog] at available
  | cons key rest =>
    obtain ⟨t, coherent, _⟩ := a.effectAnalysis.sound verified _ _ key
      (by rw [catalog]; exact List.mem_cons_self)
    exact ⟨t, coherent⟩

def reachInput (a : DeclaredArchitecture) (g : a.S.Generator)
    (t : a.S.Occurrence (a.S.input g)) (tuple : (a.S.input g).vdp.MemberIndex) : Prop :=
  ∃ w, a.boundary w ∧ a.Evaluates w t tuple ∧ a.context g t w

/-- Exact full tuples plus every upstream coordinate. The contract is authored
in `admissibleInput`, independently of this subsequently defined relation. -/
def InputValid (a : DeclaredArchitecture) (g : a.S.Generator)
    (t : a.S.Occurrence (a.S.input g)) : Prop :=
  (∀ tuple, a.reachInput g t tuple ↔ a.admissibleInput g t tuple) ∧
  (∀ i member, a.incoming t i member ↔
    ∃ tuple, a.admissibleInput g t tuple ∧ (a.S.input g).coordinate tuple i = member)

/-- Unreachable contexts are reported separately from inhabited verified uses. -/
inductive InputStatus (a : DeclaredArchitecture) (g : a.S.Generator)
    (t : a.S.Occurrence (a.S.input g)) : Prop where
  | verified (valid : a.InputValid g t) (inhabited : ∃ tuple, a.reachInput g t tuple)
  | unreachable (noSupplier : ∀ i member, ¬ a.incoming t i member)
      (noTuple : ∀ tuple, ¬ a.reachInput g t tuple)
      (noContract : ∀ tuple, ¬ a.admissibleInput g t tuple)

abbrev effect (a : DeclaredArchitecture) (c : a.S.Cause) := a.S.effectInputs a.effectAnalysis c

/-- Every factor must come from its own derived history, even when all nodes,
member values and downstream Operations happen to coincide. -/
def EffectProvenance (a : DeclaredArchitecture) (c : a.S.Cause)
    (t : a.S.Occurrence (a.effect c)) : Prop :=
  ∀ i, (t.supplier i).provenance a.cyclicBoundary =
    ArchitectureSignature.coordinateHistory (a.S.effectCoordinates a.effectAnalysis c) i

theorem terminal_positions (a : DeclaredArchitecture) (verified : a.effectAnalysis.Valid)
    (c : a.S.Cause) (n : a.S.Node) (terminal : n ∈ a.S.effectNodes a.cyclicBoundary c)
    (t : a.S.Occurrence (.node n)) (origin : a.InCone c t) :
    ∃ i : (a.effect c).Position, (a.effect c).nodeAt i = n ∧
      ArchitectureSignature.coordinateHistory (a.S.effectCoordinates a.effectAnalysis c) i =
        t.provenance a.cyclicBoundary :=
  ArchitectureSignature.coordinateHistory_complete _ n _
    (ArchitectureSignature.terminal_provenance_complete a.effectAnalysis verified c n terminal t origin.2)

/-- Every cached Effect coordinate has an actual rooted typed supplier.
Reachability/availability and the independent full tuple contract remain
separate obligations; this theorem does not create an architectural join. -/
theorem effect_realized (a : DeclaredArchitecture) (verified : a.effectAnalysis.Valid) (c : a.S.Cause) :
    ∃ t : a.S.Occurrence (a.effect c),
      (∀ i, a.InCone c (t.supplier i)) ∧ a.EffectProvenance c t := by
  let all := a.S.effectCoordinates a.effectAnalysis c
  have assemble : ∀ coordinates : List (a.S.Node × a.S.History),
      (∀ entry ∈ coordinates, entry ∈ all) →
      ∃ t : a.S.Occurrence (Inputs.ofNodes (coordinates.map Prod.fst)),
        (∀ i, a.InCone c (t.supplier i)) ∧
        (∀ i, (t.supplier i).provenance a.cyclicBoundary =
          ArchitectureSignature.coordinateHistory coordinates i) := by
    intro coordinates
    induction coordinates with
    | nil =>
      intro _
      exact ⟨.unit, (fun i => Empty.elim i), (fun i => Empty.elim i)⟩
    | cons entry rest ih =>
      intro included
      obtain ⟨n, atBoundary, supplied⟩ := List.mem_flatMap.mp (included entry List.mem_cons_self)
      obtain ⟨key, inCatalog, entryEq⟩ := List.mem_map.mp supplied
      cases entryEq
      obtain ⟨head, localRoots, history⟩ := a.effectAnalysis.sound verified c n key inCatalog
      have own := a.S.effectNode_owner a.cyclicBoundary c n atBoundary
      have headOrigin : a.InCone c head := by
        refine ⟨?_, localRoots⟩
        have root := head.owned_origin (localRoots.local _)
        simpa only [own] using root
      obtain ⟨tail, tailOrigins, tailHistories⟩ := ih
        (fun value member => included value (List.mem_cons_of_mem _ member))
      refine ⟨.tensor head tail, ?_, ?_⟩
      · intro i
        cases i with
        | inl i =>
          cases i
          change a.InCone c (head.supplier ())
          rw [ArchitectureSignature.Term.supplier_node]
          exact headOrigin
        | inr i => exact tailOrigins i
      · intro i
        cases i with
        | inl i =>
          cases i
          change (head.supplier ()).provenance a.cyclicBoundary = key
          rw [ArchitectureSignature.Term.supplier_node]
          exact history
        | inr i => exact tailHistories i
  exact assemble all (fun _ member => member)

def effectIncoming (a : DeclaredArchitecture) (c : a.S.Cause)
    (i : (a.effect c).Position) (member : (a.S.object ((a.effect c).nodeAt i)).MemberIndex) : Prop :=
  ∃ t : a.S.Occurrence (.node ((a.effect c).nodeAt i)),
    a.InCone c t ∧
    t.provenance a.cyclicBoundary =
      ArchitectureSignature.coordinateHistory (a.S.effectCoordinates a.effectAnalysis c) i ∧
    ∃ w, a.boundary w ∧ a.Evaluates w t member

/-- All finite supplier derivations at the derived boundary occurrences, under
the explicitly declared full-tuple provenance context. Repeated visits to one
boundary enlarge this relation, not the number of tensor coordinates. -/
def reachEffect (a : DeclaredArchitecture) (c : a.S.Cause)
    (tuple : (a.effect c).vdp.MemberIndex) : Prop :=
  ∃ t : a.S.Occurrence (a.effect c),
    (∀ i, a.InCone c (t.supplier i)) ∧
    a.EffectProvenance c t ∧
    ∃ w, a.boundary w ∧ a.Evaluates w t tuple ∧ a.effectContext c t w ∧
      Nonempty (a.effect c).Position

theorem reachEffect.supplier {a : DeclaredArchitecture} {c tuple}
    (reachable : a.reachEffect c tuple) (i : (a.effect c).Position) :
    a.effectIncoming c i ((a.effect c).coordinate tuple i) := by
  obtain ⟨t, origins, histories, w, allowed, supplied, _⟩ := reachable
  exact ⟨t.supplier i, origins i, histories i, w, allowed, supplied.supplier i⟩

/-- Full Effect image for a proved stationary interpretation and an actual
complete terminal supplier. This retains the common boundary world. -/
theorem effect_image_of_assignment (a : DeclaredArchitecture) (c : a.S.Cause)
    (values : a.S.World → (n : a.S.Node) → (a.S.object n).MemberIndex)
    (evaluation : ∀ w {s} (t : a.S.Occurrence s), a.Evaluates w t (s.assign (values w)))
    (terminal : a.S.Occurrence (a.effect c))
    (origins : ∀ i, a.InCone c (terminal.supplier i))
    (provenance : a.EffectProvenance c terminal)
    (observed : Nonempty (a.effect c).Position)
    (available : ∀ w, a.boundary w → a.effectContext c terminal w) (tuple) :
    a.reachEffect c tuple ↔ ∃ w, a.boundary w ∧ (a.effect c).assign (values w) = tuple := by
  constructor
  · rintro ⟨t, _, _, w, allowed, supplied, _⟩
    exact ⟨w, allowed, Option.some.inj ((evaluation w t).symm.trans supplied)⟩
  · rintro ⟨w, allowed, same⟩
    exact ⟨terminal, origins, provenance, w, allowed,
      same ▸ evaluation w terminal, available w allowed, observed⟩

/-- Projection preservation for an explicitly proved stationary interpretation.
The premises do not hold for arbitrary cyclic or occurrence-sensitive models. -/
theorem effect_projection_of_assignment (a : DeclaredArchitecture) (c : a.S.Cause)
    (values : a.S.World → (n : a.S.Node) → (a.S.object n).MemberIndex)
    (evaluation : ∀ w {s} (t : a.S.Occurrence s), a.Evaluates w t (s.assign (values w)))
    (admissible : ∀ w, a.boundary w → a.admissibleEffect c ((a.effect c).assign (values w)))
    (exactEffect : ∀ tuple, a.reachEffect c tuple ↔ a.admissibleEffect c tuple)
    (i : (a.effect c).Position) (member : (a.S.object ((a.effect c).nodeAt i)).MemberIndex) :
    a.effectIncoming c i member ↔
      ∃ tuple, a.admissibleEffect c tuple ∧ (a.effect c).coordinate tuple i = member := by
  constructor
  · rintro ⟨t, _, _, w, allowed, supplied⟩
    have value := Option.some.inj ((evaluation w t).symm.trans supplied)
    exact ⟨_, admissible w allowed, (Inputs.coordinate_assign (values w) _ i).trans value⟩
  · rintro ⟨tuple, allowed, same⟩
    exact same ▸ reachEffect.supplier ((exactEffect tuple).mpr allowed) i

def ConeValid (a : DeclaredArchitecture) (c : a.S.Cause) : Prop :=
  Nonempty (a.effect c).Position ∧
  (∃ tuple, a.reachEffect c tuple) ∧
  (∀ tuple, a.reachEffect c tuple ↔ a.admissibleEffect c tuple) ∧
  (∀ i member, a.effectIncoming c i member ↔
    ∃ tuple, a.admissibleEffect c tuple ∧ (a.effect c).coordinate tuple i = member)

/-- An explicitly proved lack of observable consequences, with no claimed
admissible full Effect. This is separate from reaching the tensor unit. -/
def NoObservableEffect (a : DeclaredArchitecture) (c : a.S.Cause) : Prop :=
  (∀ i member, ¬ a.effectIncoming c i member) ∧
  (∀ tuple, ¬ a.admissibleEffect c tuple)

theorem NoObservableEffect.not_reachable {a : DeclaredArchitecture} {c}
    (empty : a.NoObservableEffect c) (tuple) : ¬ a.reachEffect c tuple := by
  intro reached
  have incoming := reachEffect.supplier reached
  obtain ⟨_, _, _, _, _, _, _, ⟨i⟩⟩ := reached
  exact empty.1 i _ (incoming i)

theorem NoObservableEffect.exact {a : DeclaredArchitecture} {c}
    (empty : a.NoObservableEffect c) (tuple) :
    a.reachEffect c tuple ↔ a.admissibleEffect c tuple :=
  ⟨fun reached => False.elim (empty.not_reachable tuple reached),
    fun admitted => False.elim (empty.2 tuple admitted)⟩

inductive ConeStatus (a : DeclaredArchitecture) (c : a.S.Cause) : Prop where
  | observable (valid : a.ConeValid c)
  | unobservable (empty : a.NoObservableEffect c)

theorem ConeStatus.valid_of_reachable {a : DeclaredArchitecture} {c}
    (status : a.ConeStatus c) {tuple} (reached : a.reachEffect c tuple) : a.ConeValid c := by
  cases status with
  | observable valid => exact valid
  | unobservable empty => exact False.elim (empty.not_reachable tuple reached)

/-- An observable Cone's declared local nodes must lead structurally to a
terminal or typed cyclic boundary. Otherwise all Effect images and the contract
must be proved empty. This is separate from global Expression/Cone coverage. -/
def BoundariesComplete (a : DeclaredArchitecture) : Prop :=
  ∀ c n, a.S.owner n = c →
    a.NoObservableEffect c ∨
      ∃ b ∈ a.S.effectNodes a.cyclicBoundary c, a.S.Depends n b

theorem defined_consequence (a : DeclaredArchitecture) (g : a.S.Generator)
    (t : a.S.Occurrence (a.S.input g)) (tuple member)
    (mapping : a.S.operation g tuple = some member) (reachable : a.reachInput g t tuple) :
    ∃ w, a.boundary w ∧ a.Evaluates w (.operation g t) member := by
  obtain ⟨w, hw, supplied, available⟩ := reachable
  refine ⟨w, hw, ?_⟩
  change a.evaluate w t = some tuple at supplied
  simp [Evaluates, evaluate, available, supplied, Option.bind, mapping]

end DeclaredArchitecture

/-- Certification of the declared model and every derived input context.
Global Cone/Expression coverage is NOT AUTOMATICALLY VERIFIED. This restricted
certificate cannot be presented as a globally exhaustive architecture theorem. -/
structure CertifiedDeclaredArchitecture where
  model : DeclaredArchitecture
  causeNonempty : Nonempty model.S.Cause
  effectCoverage : model.effectAnalysis.Valid
  inputSources : ∀ g, model.InputSources g
  inputs : ∀ g t, model.isInputContext g t → model.InputStatus g t
  cones : ∀ c, model.ConeStatus c
  boundariesComplete : model.BoundariesComplete

def CertifiedDeclaredArchitecture.coverageStatus (_ : CertifiedDeclaredArchitecture) : String :=
  "Global Cone/Expression coverage: NOT AUTOMATICALLY VERIFIED"

theorem CertifiedDeclaredArchitecture.hasCone (certified : CertifiedDeclaredArchitecture) :
    ∃ c, certified.model.ConeStatus c := by
  obtain ⟨c⟩ := certified.causeNonempty
  exact ⟨c, certified.cones c⟩

/-- The mandatory source and context fields jointly account for every
independently incoming member. A missing factor cannot erase the obligation,
and a chosen grounding witness does not limit the universally checked contexts. -/
theorem CertifiedDeclaredArchitecture.input_partner (certified : CertifiedDeclaredArchitecture)
    (g : certified.model.S.Generator) (i : (certified.model.S.input g).Position)
    (member : (certified.model.S.object ((certified.model.S.input g).nodeAt i)).MemberIndex)
    (supplied : certified.model.supplierImage ((certified.model.S.input g).nodeAt i) member) :
    ∃ t : certified.model.S.Occurrence (certified.model.S.input g),
      certified.model.isInputContext g t ∧
      ∃ tuple, certified.model.admissibleInput g t tuple ∧
        certified.model.reachInput g t tuple ∧
        (certified.model.S.input g).coordinate tuple i = member := by
  classical
  let a := certified.model
  obtain ⟨supplier, coherent, worlds⟩ := supplied
  cases certified.inputSources g with
  | unreachable empty => exact False.elim (empty i member ⟨supplier, coherent, worlds⟩)
  | grounded available =>
    let supply (j : (a.S.input g).Position) : a.S.Occurrence (.node ((a.S.input g).nodeAt j)) :=
      if same : i = j then same ▸ supplier else Classical.choose (available j)
    let full := ArchitectureSignature.Term.fromSuppliers (a.S.input g) supply
    have allCoherent : full.RootCoherent := by
      apply ArchitectureSignature.Term.fromSuppliers_coherent
      intro j
      dsimp [supply]
      split
      · rename_i same; cases same; exact coherent
      · exact Classical.choose_spec (available j)
    have context := (a.isInputContext_iff_coherent g full).mpr allCoherent
    have same : full.supplier i = supplier := by
      rw [ArchitectureSignature.Term.supplier_fromSuppliers]
      simp [supply]
    have incoming : a.incoming full i member := by
      unfold DeclaredArchitecture.incoming
      rw [same]
      exact worlds
    cases certified.inputs g full context with
    | unreachable empty _ _ => exact False.elim (empty i member incoming)
    | verified valid _ =>
      obtain ⟨tuple, admissible, coordinate⟩ := (valid.2 i member).mp incoming
      exact ⟨full, context, tuple, admissible, (valid.1 tuple).mpr admissible, coordinate⟩

end ArchiScript
