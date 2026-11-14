import ArchiScript.Expression

namespace ArchiScript

/-- Typed supplier structure on an Operation's source. Pairing here records
factor origins for analysis; it does not construct a diagonal Operation. -/
inductive Inputs (Node : Type) (object : Node → Partition.{0, 0}) where
  | unit
  | node (n : Node)
  | tensor (left right : Inputs Node object)

namespace Inputs

abbrev vdp {Node object} : Inputs Node object → Partition.{0, 0}
  | .unit => Partition.unit
  | .node n => object n
  | .tensor a b => a.vdp.tensor b.vdp

def nodes {Node object} : Inputs Node object → List Node
  | .unit => []
  | .node n => [n]
  | .tensor a b => a.nodes ++ b.nodes

/-- A position, rather than a nominal VDP, identifies a factor occurrence. -/
abbrev Position {Node object} : Inputs Node object → Type
  | .unit => Empty
  | .node _ => Unit
  | .tensor a b => Sum a.Position b.Position

abbrev nodeAt {Node object} (s : Inputs Node object) : s.Position → Node :=
  match s with
  | .unit => fun i => nomatch i
  | .node n => fun _ => n
  | .tensor a b => fun | .inl i => a.nodeAt i | .inr j => b.nodeAt j

abbrev coordinate {Node object} (s : Inputs Node object)
    (tuple : s.vdp.MemberIndex) : (i : s.Position) → (object (s.nodeAt i)).MemberIndex :=
  match s with
  | .unit => fun i => nomatch i
  | .node _ => fun _ => tuple
  | .tensor a b => fun | .inl i => a.coordinate tuple.1 i | .inr j => b.coordinate tuple.2 j

def ofNodes {Node object} : List Node → Inputs Node object
  | [] => .unit
  | n :: ns => .tensor (.node n) (ofNodes ns)

def assign {Node object} (values : (n : Node) → (object n).MemberIndex) :
    (s : Inputs Node object) → s.vdp.MemberIndex
  | .unit => ()
  | .node n => values n
  | .tensor a b => (a.assign values, b.assign values)

theorem coordinate_assign {Node object} (values : (n : Node) → (object n).MemberIndex)
    (s : Inputs Node object) (i : s.Position) : s.coordinate (s.assign values) i = values (s.nodeAt i) := by
  induction s with
  | unit => exact Empty.elim i
  | node n => rfl
  | tensor a b iha ihb =>
    cases i with
    | inl i => exact iha i
    | inr i => exact ihb i

end Inputs

/-- Heterogeneous closed inventories carry the proofs of every declared region
and split. They cannot register an unchecked coverage assertion. -/
structure DomainDeclaration where
  Value : Type
  domain : Subdomain Value

structure SplitDeclaration where
  Value : Type
  parent : Subdomain Value
  split : SemanticSplit parent

/-- The finite primitive declaration source. Occurrence histories and root
instances are deliberately not assumed finite. Cones are indexed by one Cause. -/
structure ArchitectureSignature where
  Node : Type
  nodeDecidableEq : DecidableEq Node
  nodes : List Node
  nodes_complete : ∀ n, n ∈ nodes
  nodes_nodup : nodes.Nodup
  object : Node → Partition.{0, 0}
  domains : List DomainDeclaration
  memberDeclared : ∀ n i, ⟨(object n).Carrier, (object n).members i⟩ ∈ domains
  splits : List SplitDeclaration
  Cause : Type
  causeDecidableEq : DecidableEq Cause
  causes : List Cause
  causes_complete : ∀ c, c ∈ causes
  causes_nodup : causes.Nodup
  RootInstance : Type
  rootDecidableEq : DecidableEq RootInstance
  origin : Cause → RootInstance
  start : Cause → Node
  owner : Node → Cause
  start_owner : ∀ c, owner (start c) = c
  Generator : Type
  generators : List Generator
  generators_complete : ∀ g, g ∈ generators
  input : Generator → Inputs Node object
  output : Generator → Node
  operation : (g : Generator) → Operation (input g).vdp (object (output g))
  localFactor : ∀ g, ∃ n ∈ (input g).nodes, owner n = owner (output g)

namespace ArchitectureSignature

instance (S : ArchitectureSignature) : DecidableEq S.Node := S.nodeDecidableEq
instance (S : ArchitectureSignature) : DecidableEq S.Cause := S.causeDecidableEq
instance (S : ArchitectureSignature) : DecidableEq S.RootInstance := S.rootDecidableEq

abbrev generatorsInventory (S : ArchitectureSignature) : Generators where
  Name := S.Generator
  names := S.generators
  complete := S.generators_complete
  Object := Inputs S.Node S.object
  object := Inputs.vdp
  source := S.input
  target := fun g => .node (S.output g)
  operation := S.operation

/-- Each root instance denotes one particular external occurrence. Shared
instances share a member assignment; different instances are not identified. -/
abbrev World (S : ArchitectureSignature) :=
  (c : S.Cause) → S.RootInstance → (S.object (S.start c)).MemberIndex

/-- Finite provenance syntax. Only the auxiliary cycle-witness instantiation
has holes; actual generated occurrences use the empty hole family. -/
inductive Term (S : ArchitectureSignature) (Hole : S.Node → Type) :
    Inputs S.Node S.object → Type 1 where
  | unit : Term S Hole .unit
  | cause (c : S.Cause) (root : S.RootInstance) : Term S Hole (.node (S.start c))
  | hole (n : S.Node) (value : Hole n) : Term S Hole (.node n)
  | operation (g : S.Generator) (input : Term S Hole (S.input g)) :
      Term S Hole (.node (S.output g))
  | tensor {a b} (left : Term S Hole a) (right : Term S Hole b) : Term S Hole (.tensor a b)

abbrev Occurrence (S : ArchitectureSignature) := S.Term (fun _ => Empty)

namespace Term

def holes {S : ArchitectureSignature} {Hole : S.Node → Type} {s : Inputs S.Node S.object} : S.Term Hole s → Nat
  | .unit | .cause .. => 0
  | .hole .. => 1
  | .operation _ input => input.holes
  | .tensor a b => a.holes + b.holes

def operations {S : ArchitectureSignature} {Hole : S.Node → Type} {s : Inputs S.Node S.object} : S.Term Hole s → Nat
  | .unit | .cause .. | .hole .. => 0
  | .operation _ input => input.operations + 1
  | .tensor a b => a.operations + b.operations

def supplier {S : ArchitectureSignature} {Hole : S.Node → Type} {s : Inputs S.Node S.object} (t : S.Term Hole s) :
    (i : s.Position) → S.Term Hole (.node (s.nodeAt i)) :=
  match t with
  | .unit => fun i => nomatch i
  | .cause c root => fun _ => .cause c root
  | .hole n h => fun _ => .hole n h
  | .operation g input => fun _ => .operation g input
  | .tensor a b => fun | .inl i => a.supplier i | .inr j => b.supplier j

theorem supplier_node {S : ArchitectureSignature} {Hole : S.Node → Type} {n}
    (t : S.Term Hole (.node n)) (i : Unit) : t.supplier i = t := by
  cases t <;> rfl

/-- Root membership is about the exact occurrence, not merely its VDP name. -/
def hasRoot {S : ArchitectureSignature} {Hole : S.Node → Type} {s : Inputs S.Node S.object} (c : S.Cause) (root : S.RootInstance) : S.Term Hole s → Prop
  | .unit | .hole .. => False
  | .cause d other => c = d ∧ root = other
  | .operation _ input => input.hasRoot c root
  | .tensor a b => a.hasRoot c root ∨ b.hasRoot c root

def onlyLocalRoot {S : ArchitectureSignature} {Hole : S.Node → Type}
    {s : Inputs S.Node S.object} (c : S.Cause) : S.Term Hole s → Prop
  | .unit | .hole .. => True
  | .cause d root => d = c → root = S.origin c
  | .operation _ input => input.onlyLocalRoot c
  | .tensor a b => a.onlyLocalRoot c ∧ b.onlyLocalRoot c

/-- A contextual cycle is an actual typed route with exactly one supplied
entry hole. Extra tensor suppliers are explicit in the witness. -/
structure CycleBoundary (S : ArchitectureSignature) (n : S.Node) where
  route : S.Term (fun k => PLift (n = k)) (.node n)
  oneEntry : route.holes = 1
  nontrivial : 0 < route.operations

end Term

/-- Natural ends and typed cyclic observation boundaries. Enumeration preserves
node occurrences, even when two nodes denote the same nominal VDP. -/
abbrev effectNodes (S : ArchitectureSignature)
    (marked : (n : S.Node) → Option (Term.CycleBoundary S n)) (c : S.Cause) : List S.Node :=
  S.nodes.filter fun n => S.owner n == c &&
    ((S.generators.any fun g => S.output g == n) &&
      !(S.generators.any fun g => S.owner (S.output g) == c && (S.input g).nodes.contains n)
      || (marked n).isSome)

abbrev effectInputs (S : ArchitectureSignature)
    (marked : (n : S.Node) → Option (Term.CycleBoundary S n)) (c : S.Cause) : Inputs S.Node S.object :=
  .ofNodes (S.effectNodes marked c)

/-- Derived supplier dependency, not categorical composition. In particular,
an edge through one tensor factor never asserts equality of its endpoints. -/
inductive Depends (S : ArchitectureSignature) : S.Node → S.Node → Prop where
  | refl (n) : Depends S n n
  | step (g) (n) (supplies : n ∈ (S.input g).nodes) : Depends S n (S.output g)
  | trans {n m k} : Depends S n m → Depends S m k → Depends S n k

end ArchitectureSignature

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
  effectContext : (c : signature.Cause) →
    signature.Occurrence (signature.effectInputs cyclicBoundary c) → signature.World → Prop
  admissibleEffect : (c : signature.Cause) →
    (signature.effectInputs cyclicBoundary c).vdp.MemberIndex → Prop

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
  t.hasRoot c (a.S.origin c) ∧ t.onlyLocalRoot c

/-- Derived actual uses belonging to the owning Cone. Exact root provenance
is required; a wholly external tensor is not an internal join of this Cone. -/
def isInputContext (a : DeclaredArchitecture) (g : a.S.Generator)
    (t : a.S.Occurrence (a.S.input g)) : Prop :=
  ∃ i, a.InCone (a.S.owner (a.S.output g)) (t.supplier i)

/-- Incoming images are obtained from each supplier before restricting the
current join. An orphan therefore cannot disappear by definition. -/
def incoming (a : DeclaredArchitecture) {s} (t : a.S.Occurrence s)
    (i : s.Position) (member : (a.S.object (s.nodeAt i)).MemberIndex) : Prop :=
  ∃ w, a.boundary w ∧ a.Evaluates w (t.supplier i) member

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

abbrev effect (a : DeclaredArchitecture) (c : a.S.Cause) := a.S.effectInputs a.cyclicBoundary c

def effectIncoming (a : DeclaredArchitecture) (c : a.S.Cause)
    (i : (a.effect c).Position) (member : (a.S.object ((a.effect c).nodeAt i)).MemberIndex) : Prop :=
  ∃ t : a.S.Occurrence (.node ((a.effect c).nodeAt i)),
    a.InCone c t ∧ ∃ w, a.boundary w ∧ a.Evaluates w t member

/-- All finite supplier derivations at the derived boundary occurrences, under
the explicitly declared full-tuple provenance context. Repeated visits to one
boundary enlarge this relation, not the number of tensor coordinates. -/
def reachEffect (a : DeclaredArchitecture) (c : a.S.Cause)
    (tuple : (a.effect c).vdp.MemberIndex) : Prop :=
  ∃ t : a.S.Occurrence (a.effect c),
    (∀ i, a.InCone c (t.supplier i)) ∧
    ∃ w, a.boundary w ∧ a.Evaluates w t tuple ∧ a.effectContext c t w

def ConeValid (a : DeclaredArchitecture) (c : a.S.Cause) : Prop :=
  a.S.effectNodes a.cyclicBoundary c ≠ [] ∧
  (∃ tuple, a.reachEffect c tuple) ∧
  (∀ tuple, a.reachEffect c tuple ↔ a.admissibleEffect c tuple) ∧
  (∀ i member, a.effectIncoming c i member ↔
    ∃ tuple, a.admissibleEffect c tuple ∧ (a.effect c).coordinate tuple i = member)

/-- Every declared local node must lead structurally to a genuine terminal
occurrence or an explicitly typed cycle boundary. This is a mandatory proof,
separate from optional universal generated-Expression/Cone coverage. -/
def BoundariesComplete (a : DeclaredArchitecture) : Prop :=
  ∀ c n, a.S.owner n = c →
    ∃ b ∈ a.S.effectNodes a.cyclicBoundary c, a.S.Depends n b

/-- Separate terminal-producing arrows cannot silently share one natural
boundary slot. A typed cyclic marker explicitly identifies the observation
whose repeated visits are aggregated; entry and feedback may share that slot. -/
def DistinctTerminalProducers (a : DeclaredArchitecture) : Prop :=
  ∀ c n, n ∈ a.S.effectNodes a.cyclicBoundary c → a.cyclicBoundary n = none →
    ∀ g h, a.S.output g = n → a.S.output h = n → g = h

theorem distinctTerminalProducers_of_injective (a : DeclaredArchitecture)
    (injective : ∀ g h, a.S.output g = a.S.output h → g = h) : a.DistinctTerminalProducers :=
  fun _ _ _ _ g h left right => injective g h (left.trans right.symm)

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
  inputs : ∀ g t, model.isInputContext g t → model.InputStatus g t
  cones : ∀ c, model.ConeValid c
  boundariesComplete : model.BoundariesComplete
  terminalOccurrencesFaithful : model.DistinctTerminalProducers

def CertifiedDeclaredArchitecture.coverageStatus (_ : CertifiedDeclaredArchitecture) : String :=
  "Global Cone/Expression coverage: NOT AUTOMATICALLY VERIFIED"

theorem CertifiedDeclaredArchitecture.hasCone (certified : CertifiedDeclaredArchitecture) :
    ∃ c, certified.model.ConeValid c := by
  obtain ⟨c⟩ := certified.causeNonempty
  exact ⟨c, certified.cones c⟩

end ArchiScript
