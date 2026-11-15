import ArchiScript.Architecture

namespace ArchiScript

/-- Structural producer history. It records the existing derivation, without
author-declared usage names or a second architecture graph. -/
inductive ProducerHistory (Generator Cause Root : Type) where
  | unit
  | cause (cause : Cause) (root : Root)
  | operation (generator : Generator) (input : ProducerHistory Generator Cause Root)
  | tensor (left right : ProducerHistory Generator Cause Root)
  deriving DecidableEq

namespace ArchitectureSignature

abbrev History (S : ArchitectureSignature) := ProducerHistory S.Generator S.Cause S.RootInstance

namespace Term

def history {S : ArchitectureSignature} {s} : S.Occurrence s → History S
  | .unit => .unit
  | .cause c root => .cause c root
  | .hole _ impossible => nomatch impossible
  | .operation g input => .operation g input.history
  | .tensor left right => .tensor left.history right.history

/-- Reconstruct a typed derivation from its structural history. Endpoint tests
use the original graph; no new Operation or VDP usage is declared. -/
def decodeHistory (S : ArchitectureSignature) : (h : History S) →
    (s : Inputs S.Node S.object) → Option (S.Occurrence s)
  | .unit, .unit => some .unit
  | .cause c root, .node n =>
    if same : S.start c = n then some (same ▸ Term.cause c root) else none
  | .operation g input, .node n =>
    if same : S.output g = n then
      (decodeHistory S input (S.input g)).map fun t => same ▸ Term.operation g t
    else none
  | .tensor left right, .tensor a b => do
    return .tensor (← decodeHistory S left a) (← decodeHistory S right b)
  | _, _ => none

theorem decode_history {S : ArchitectureSignature} {s} (t : S.Occurrence s) :
    decodeHistory S t.history s = some t := by
  induction t with
  | unit => rfl
  | cause c root => simp [history, decodeHistory]
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih => simp [history, decodeHistory, ih]
  | tensor left right ihl ihr => simp [history, decodeHistory, ihl, ihr]

theorem history_injective {S : ArchitectureSignature} {s} (left right : S.Occurrence s)
    (same : left.history = right.history) : left = right := by
  have decoded := congrArg (fun h => decodeHistory S h s) same
  rw [decode_history, decode_history] at decoded
  exact Option.some.inj decoded

/-- Match an actual declared one-hole return, retaining the captured entry.
All non-hole generators, root instances and auxiliary suppliers must match.
This is an observation-boundary analysis, not equality of Operations/values. -/
def matchHistory {S : ArchitectureSignature} {Hole : S.Node → Type} {s} :
    S.Term Hole s → History S → Option (List (History S))
  | .unit, .unit => some []
  | .cause c root, .cause d other => if c = d ∧ root = other then some [] else none
  | .hole _ _, h => some [h]
  | .operation g input, .operation h supplied =>
    if g = h then input.matchHistory supplied else none
  | .tensor left right, .tensor suppliedLeft suppliedRight => do
    return (← left.matchHistory suppliedLeft) ++ (← right.matchHistory suppliedRight)
  | _, _ => none

end Term

abbrev Markers (S : ArchitectureSignature) := (n : S.Node) → Option (Term.CycleBoundary S n)

def normalizeOperation (S : ArchitectureSignature) (marked : S.Markers)
    (g : S.Generator) (input : History S) : History S :=
  let produced := ProducerHistory.operation g input
  match marked (S.output g) with
  | none => produced
  | some boundary =>
    match boundary.route.matchHistory produced with
    | some [entry] => entry
    | _ => produced

/-- Only repetitions of the supplied typed cyclic return are contracted.
Unmarked shared targets and arbitrarily long shared suffixes retain history. -/
def Term.provenance {S : ArchitectureSignature} (marked : S.Markers) {s} :
    S.Occurrence s → History S
  | .unit => .unit
  | .cause c root => .cause c root
  | .hole _ impossible => nomatch impossible
  | .operation g input => S.normalizeOperation marked g (input.provenance marked)
  | .tensor left right => .tensor (left.provenance marked) (right.provenance marked)

theorem Term.provenance_without_cycles {S : ArchitectureSignature} {s} (t : S.Occurrence s) :
    t.provenance (fun _ => none) = t.history := by
  induction t with
  | unit | cause => rfl
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih => simp [Term.provenance, normalizeOperation, Term.history, ih]
  | tensor left right ihl ihr => simp [Term.provenance, Term.history, ihl, ihr]

theorem provenance_unmarked {S : ArchitectureSignature} {marked : S.Markers}
    (g : S.Generator) (unmarked : marked (S.output g) = none)
    (input : S.Occurrence (S.input g)) :
    (Term.operation g input).provenance marked = .operation g (input.provenance marked) := by
  simp [Term.provenance, normalizeOperation, unmarked]

theorem shared_suffix_preserves_provenance {S : ArchitectureSignature} {marked : S.Markers}
    (g : S.Generator) (unmarked : marked (S.output g) = none)
    (left right : S.Occurrence (S.input g))
    (different : left.provenance marked ≠ right.provenance marked) :
    (Term.operation g left).provenance marked ≠ (Term.operation g right).provenance marked := by
  rw [provenance_unmarked g unmarked, provenance_unmarked g unmarked]
  intro same
  exact different (ProducerHistory.operation.inj same).2

def histories (S : ArchitectureSignature) (catalog : S.Node → List (History S)) :
    Inputs S.Node S.object → List (History S)
  | .unit => [.unit]
  | .node n => catalog n
  | .tensor left right => (S.histories catalog left).flatMap fun l =>
    (S.histories catalog right).map fun r => .tensor l r

def rootHistories (S : ArchitectureSignature) (roots : List S.RootInstance) (_c : S.Cause)
    (n : S.Node) : List (History S) :=
  S.causes.flatMap fun d => if S.start d = n then
    (roots.filter fun root => root == S.origin d).map (ProducerHistory.cause d) else []

def expandHistories (S : ArchitectureSignature) (marked : S.Markers)
    (before : S.Node → List (History S)) (n : S.Node) : List (History S) :=
  S.generators.flatMap fun g => if S.output g = n then
    (S.histories before (S.input g)).map (S.normalizeOperation marked g) else []

/-- Bounded construction of a provenance basis from the single primitive graph.
Fuel is accepted as exact only with closure and every Cause's canonical origin. -/
def provenanceCatalog (S : ArchitectureSignature) (marked : S.Markers)
    (roots : List S.RootInstance) (c : S.Cause) : Nat → S.Node → List (History S)
  | 0, n => (S.rootHistories roots c n).eraseDups
  | fuel + 1, n =>
    let before := S.provenanceCatalog marked roots c fuel
    (before n ++ S.expandHistories marked before n).eraseDups

def ProvenanceClosed (S : ArchitectureSignature) (marked : S.Markers)
    (roots : List S.RootInstance) (fuel : Nat) : Prop :=
  ∀ c ∈ S.causes, ∀ g ∈ S.generators,
    ∀ input ∈ S.histories (S.provenanceCatalog marked roots c fuel) (S.input g),
      S.normalizeOperation marked g input ∈ S.provenanceCatalog marked roots c fuel (S.output g)

instance {S : ArchitectureSignature} (marked : S.Markers) (roots : List S.RootInstance) (fuel) :
    Decidable (S.ProvenanceClosed marked roots fuel) :=
  inferInstanceAs (Decidable (∀ c ∈ S.causes, ∀ g ∈ S.generators,
    ∀ input ∈ S.histories (S.provenanceCatalog marked roots c fuel) (S.input g),
      S.normalizeOperation marked g input ∈ S.provenanceCatalog marked roots c fuel (S.output g)))

/-- A finite candidate cache. Its entries are derived data, not names or
copies of architectural objects. Validity is mandatory at certification. -/
structure ProvenanceAnalysis (S : ArchitectureSignature) (_marked : S.Markers) where
  roots : List S.RootInstance
  entries : List (S.Cause × S.Node × History S)

def provenanceEntries (S : ArchitectureSignature) (marked : S.Markers)
    (roots : List S.RootInstance) (fuel : Nat) : List (S.Cause × S.Node × History S) :=
  S.causes.flatMap fun c => S.nodes.flatMap fun n =>
    (S.provenanceCatalog marked roots c fuel n).map fun key => (c, n, key)

/-- A single worklist layer over already cached data. The optional elaborator
normalizes each layer once instead of duplicating recursive lookups in types. -/
def extendProvenanceEntries (S : ArchitectureSignature) (marked : S.Markers)
    (before : List (S.Cause × S.Node × History S)) : List (S.Cause × S.Node × History S) :=
  let lookup (c : S.Cause) (n : S.Node) :=
    (before.filter fun entry => entry.1 == c && entry.2.1 == n).map fun entry => entry.2.2
  S.causes.flatMap fun c => S.nodes.flatMap fun n =>
    ((lookup c n ++ S.expandHistories marked (lookup c) n).eraseDups).map fun key => (c, n, key)

def decodedHistoryValid (S : ArchitectureSignature) (marked : S.Markers)
    (_c : S.Cause) (n : S.Node) (key : History S) : Bool :=
  match Term.decodeHistory S key (.node n) with
  | none => false
  | some t => decide t.RootCoherent && decide (t.provenance marked = key)

namespace ProvenanceAnalysis

def catalog {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) (c : S.Cause) (n : S.Node) : List (History S) :=
  ((analysis.entries.filter fun entry => entry.1 == c && entry.2.1 == n).map fun entry => entry.2.2).eraseDups

def Seeded {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) : Prop :=
  ∀ c ∈ S.causes, ∀ n ∈ S.nodes, ∀ key ∈ S.rootHistories analysis.roots c n,
    key ∈ analysis.catalog c n

def Closed {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) : Prop :=
  ∀ c ∈ S.causes, ∀ g ∈ S.generators,
    ∀ input ∈ S.histories (analysis.catalog c) (S.input g),
      S.normalizeOperation marked g input ∈ analysis.catalog c (S.output g)

def Realized {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) : Prop :=
  ∀ c ∈ S.causes, ∀ n ∈ S.nodes, ∀ key ∈ analysis.catalog c n,
    S.decodedHistoryValid marked c n key = true

def Checked {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) : Prop := analysis.Seeded ∧ analysis.Closed ∧ analysis.Realized

instance {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) : Decidable analysis.Seeded :=
  inferInstanceAs (Decidable (∀ c ∈ S.causes, ∀ n ∈ S.nodes,
    ∀ key ∈ S.rootHistories analysis.roots c n, key ∈ analysis.catalog c n))

instance {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) : Decidable analysis.Closed :=
  inferInstanceAs (Decidable (∀ c ∈ S.causes, ∀ g ∈ S.generators,
    ∀ input ∈ S.histories (analysis.catalog c) (S.input g),
      S.normalizeOperation marked g input ∈ analysis.catalog c (S.output g)))

instance {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) : Decidable analysis.Realized :=
  inferInstanceAs (Decidable (∀ c ∈ S.causes, ∀ n ∈ S.nodes,
    ∀ key ∈ analysis.catalog c n, S.decodedHistoryValid marked c n key = true))

instance {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) : Decidable analysis.Checked :=
  inferInstanceAs (Decidable (analysis.Seeded ∧ analysis.Closed ∧ analysis.Realized))

def Valid {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) : Prop :=
  (∀ c, S.origin c ∈ analysis.roots) ∧ analysis.Checked

/-- A finite structural check over every declared source factor, independent
of full input tuples and of their admissibility. -/
def SourcesPresent {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) (g : S.Generator) : Prop :=
  ∀ n ∈ (S.input g).nodes, (analysis.catalog (S.owner (S.output g)) n).isEmpty = false

instance {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) (g : S.Generator) : Decidable (analysis.SourcesPresent g) :=
  inferInstanceAs (Decidable (∀ n ∈ (S.input g).nodes,
    (analysis.catalog (S.owner (S.output g)) n).isEmpty = false))

theorem roots_in_catalog (S : ArchitectureSignature) (marked : S.Markers)
    (roots : List S.RootInstance) (c : S.Cause) (fuel : Nat) (n) (key)
    (seed : key ∈ S.rootHistories roots c n) :
    key ∈ S.provenanceCatalog marked roots c fuel n := by
  induction fuel with
  | zero => exact List.mem_eraseDups.mpr seed
  | succ fuel ih => exact List.mem_eraseDups.mpr (List.mem_append_left _ ih)

theorem complete {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) (verified : analysis.Valid) (c : S.Cause) {s}
    (t : S.Occurrence s) (localRoots : t.RootCoherent) :
    t.provenance marked ∈ S.histories (analysis.catalog c) s := by
  induction t with
  | unit => exact List.mem_cons_self
  | cause d root =>
    change root = S.origin d at localRoots
    apply verified.2.1 c (S.causes_complete c) (S.start d) (S.nodes_complete _)
    apply List.mem_flatMap.mpr
    refine ⟨d, S.causes_complete d, ?_⟩
    rw [ite_eq_left rfl]
    exact List.mem_map.mpr ⟨root, List.mem_filter.mpr
      ⟨localRoots.symm ▸ verified.1 d, by simpa using localRoots⟩, rfl⟩
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih =>
    exact verified.2.2.1 c (S.causes_complete c) g (S.generators_complete g) _ (ih localRoots)
  | tensor left right ihl ihr =>
    exact List.mem_flatMap.mpr ⟨_, ihl localRoots.1,
      List.mem_map.mpr ⟨_, ihr localRoots.2, rfl⟩⟩

theorem histories_sound {S : ArchitectureSignature} {marked : S.Markers}
    (catalog : S.Node → List (History S)) (_c : S.Cause)
    (sound : ∀ n key, key ∈ catalog n →
      ∃ t : S.Occurrence (.node n), t.RootCoherent ∧ t.provenance marked = key)
    (s : Inputs S.Node S.object) (key : History S) (member : key ∈ S.histories catalog s) :
    ∃ t : S.Occurrence s, t.RootCoherent ∧ t.provenance marked = key := by
  induction s generalizing key with
  | unit =>
    have same := List.mem_singleton.mp member
    exact ⟨.unit, trivial, same.symm⟩
  | node n => exact sound n key member
  | tensor left right ihl ihr =>
    obtain ⟨l, hl, supplied⟩ := List.mem_flatMap.mp member
    obtain ⟨r, hr, same⟩ := List.mem_map.mp supplied
    obtain ⟨lt, localLeft, keyLeft⟩ := ihl l hl
    obtain ⟨rt, localRight, keyRight⟩ := ihr r hr
    refine ⟨.tensor lt rt, ⟨localLeft, localRight⟩, ?_⟩
    change ProducerHistory.tensor (lt.provenance marked) (rt.provenance marked) = key
    rw [keyLeft, keyRight]
    exact same

theorem catalog_sound (S : ArchitectureSignature) (marked : S.Markers)
    (roots : List S.RootInstance) (c : S.Cause) (fuel : Nat) :
    ∀ n key, key ∈ S.provenanceCatalog marked roots c fuel n →
      ∃ t : S.Occurrence (.node n), t.RootCoherent ∧ t.provenance marked = key := by
  induction fuel with
  | zero =>
    intro n key member
    obtain ⟨d, _, supplied⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp member)
    split at supplied
    · rename_i source
      obtain ⟨root, rootMember, same⟩ := List.mem_map.mp supplied
      subst n
      exact ⟨.cause d root, by simpa [Term.RootCoherent] using (List.mem_filter.mp rootMember).2, same⟩
    · cases supplied
  | succ fuel ih =>
    intro n key member
    rcases List.mem_append.mp (List.mem_eraseDups.mp member) with old | new
    · exact ih n key old
    · obtain ⟨g, _, produced⟩ := List.mem_flatMap.mp new
      split at produced
      · rename_i target
        obtain ⟨input, inputMember, same⟩ := List.mem_map.mp produced
        obtain ⟨t, localRoots, keyInput⟩ := histories_sound _ c ih (S.input g) input inputMember
        subst n
        refine ⟨.operation g t, localRoots, ?_⟩
        change S.normalizeOperation marked g (t.provenance marked) = key
        rw [keyInput]
        exact same
      · cases produced

theorem sound {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) (verified : analysis.Valid) (c : S.Cause) (n key)
    (member : key ∈ analysis.catalog c n) :
    ∃ t : S.Occurrence (.node n), t.RootCoherent ∧ t.provenance marked = key := by
  have checked := verified.2.2.2 c (S.causes_complete c) n (S.nodes_complete n) key member
  cases decoded : Term.decodeHistory S key (.node n) with
  | none => simp [decodedHistoryValid, decoded] at checked
  | some t =>
    simp only [decodedHistoryValid, decoded, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact ⟨t, checked.1, checked.2⟩

end ProvenanceAnalysis

/-- Coordinates are automatically derived producer histories, never authored
unique VDP usages. Equal nodes may occur at arbitrarily many distinct positions. -/
abbrev effectCoordinates (S : ArchitectureSignature) {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) (c : S.Cause) : List (S.Node × History S) :=
  (S.effectNodes marked c).flatMap fun n => (analysis.catalog c n).map fun key => (n, key)

abbrev effectInputs (S : ArchitectureSignature) {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) (c : S.Cause) : Inputs S.Node S.object :=
  .ofNodes ((S.effectCoordinates analysis c).map Prod.fst)

def coordinateHistory {S : ArchitectureSignature} (coordinates : List (S.Node × History S)) :
    (Inputs.ofNodes (object := S.object) (coordinates.map Prod.fst)).Position → History S :=
  match coordinates with
  | [] => fun i => nomatch i
  | (_, key) :: rest => fun | .inl _ => key | .inr i => coordinateHistory rest i

theorem terminal_provenance_complete {S : ArchitectureSignature} {marked : S.Markers}
    (analysis : S.ProvenanceAnalysis marked) (verified : analysis.Valid) (c : S.Cause) (n)
    (terminal : n ∈ S.effectNodes marked c) (t : S.Occurrence (.node n))
    (localRoots : t.RootCoherent) : (n, t.provenance marked) ∈ S.effectCoordinates analysis c := by
  exact List.mem_flatMap.mpr ⟨n, terminal, List.mem_map.mpr ⟨_, analysis.complete verified c t localRoots, rfl⟩⟩

theorem coordinateHistory_complete {S : ArchitectureSignature}
    (coordinates : List (S.Node × History S)) (n : S.Node) (key : History S)
    (member : (n, key) ∈ coordinates) :
    ∃ i : (Inputs.ofNodes (object := S.object) (coordinates.map Prod.fst)).Position,
      (Inputs.ofNodes (object := S.object) (coordinates.map Prod.fst)).nodeAt i = n ∧
      coordinateHistory coordinates i = key := by
  induction coordinates with
  | nil => cases member
  | cons entry rest ih =>
    rcases List.mem_cons.mp member with same | tail
    · cases same
      exact ⟨.inl (), rfl, rfl⟩
    · obtain ⟨i, node, history⟩ := ih tail
      exact ⟨.inr i, node, history⟩

end ArchitectureSignature

namespace Expression

def supply {S : ArchitectureSignature} {X Y}
    (e : Expression S.generatorsInventory X Y) (input : S.Occurrence X) : S.Occurrence Y :=
  match e with
  | .identity _ => input
  | .step g before => .operation g (before.supply input)

def Unmarked {S : ArchitectureSignature} (marked : S.Markers) :
    {X Y : Inputs S.Node S.object} → Expression S.generatorsInventory X Y → Prop
  | _, _, .identity _ => True
  | _, _, .step g before => before.Unmarked marked ∧ marked (S.output g) = none

/-- Any finite shared suffix preserves provenance at unmarked boundaries.
The shared graph and each downstream Operation are declared only once. -/
theorem supply_preserves_provenance {S : ArchitectureSignature} (marked : S.Markers)
    {X Y} (e : Expression S.generatorsInventory X Y) (unmarked : e.Unmarked marked)
    (left right : S.Occurrence X)
    (different : left.provenance marked ≠ right.provenance marked) :
    (e.supply left).provenance marked ≠ (e.supply right).provenance marked := by
  induction e with
  | identity => exact different
  | step g before ih =>
    exact ArchitectureSignature.shared_suffix_preserves_provenance g unmarked.2 _ _
      (ih unmarked.1 left right different)

end Expression
end ArchiScript
