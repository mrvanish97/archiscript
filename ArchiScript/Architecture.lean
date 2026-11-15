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

theorem node_position {Node object} (s : Inputs Node object) {n : Node}
    (member : n ∈ s.nodes) : ∃ i : s.Position, s.nodeAt i = n := by
  induction s with
  | unit => cases member
  | node k =>
    have same : n = k := List.mem_singleton.mp member
    exact ⟨(), same.symm⟩
  | tensor left right ihl ihr =>
    rcases List.mem_append.mp member with hl | hr
    · obtain ⟨i, same⟩ := ihl hl
      exact ⟨.inl i, same⟩
    · obtain ⟨i, same⟩ := ihr hr
      exact ⟨.inr i, same⟩

theorem coordinate_ext {Node object} (s : Inputs Node object)
    (left right : s.vdp.MemberIndex) (same : ∀ i, s.coordinate left i = s.coordinate right i) :
    left = right := by
  induction s with
  | unit => exact Subsingleton.elim _ _
  | node n => exact same ()
  | tensor a b iha ihb =>
    exact Prod.ext (iha left.1 right.1 (fun i => same (.inl i)))
      (ihb left.2 right.2 (fun i => same (.inr i)))

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
  generatorDecidableEq : DecidableEq Generator
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
instance (S : ArchitectureSignature) : DecidableEq S.Generator := S.generatorDecidableEq

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

theorem rooted {S : ArchitectureSignature} {s} (t : S.Occurrence s) (i : s.Position) :
    ∃ root, t.hasRoot (S.owner (s.nodeAt i)) root := by
  induction t with
  | unit => exact Empty.elim i
  | cause c root =>
    refine ⟨root, ?_⟩
    change S.owner (S.start c) = c ∧ root = root
    exact ⟨S.start_owner c, rfl⟩
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih =>
    obtain ⟨n, member, own⟩ := S.localFactor g
    obtain ⟨position, same⟩ := (S.input g).node_position member
    obtain ⟨root, origin⟩ := ih position
    rw [same, own] at origin
    exact ⟨root, origin⟩
  | tensor left right ihl ihr =>
    cases i with
    | inl j => obtain ⟨root, origin⟩ := ihl j; exact ⟨root, Or.inl origin⟩
    | inr j => obtain ⟨root, origin⟩ := ihr j; exact ⟨root, Or.inr origin⟩

def localRootDecision {S : ArchitectureSignature} (c : S.Cause) :
    {s : Inputs S.Node S.object} → (t : S.Occurrence s) → Decidable (t.onlyLocalRoot c)
  | _, .unit => isTrue trivial
  | _, .cause d root => inferInstanceAs (Decidable (d = c → root = S.origin c))
  | _, .hole _ impossible => nomatch impossible
  | _, .operation _ input => localRootDecision c input
  | _, .tensor left right =>
    letI := localRootDecision c left
    letI := localRootDecision c right
    inferInstanceAs (Decidable (left.onlyLocalRoot c ∧ right.onlyLocalRoot c))

instance {S : ArchitectureSignature} {s} (c : S.Cause) (t : S.Occurrence s) :
    Decidable (t.onlyLocalRoot c) := localRootDecision c t

theorem local_root_identity {S : ArchitectureSignature} {s} (t : S.Occurrence s)
    (c : S.Cause) (root : S.RootInstance) (localRoots : t.onlyLocalRoot c)
    (origin : t.hasRoot c root) : root = S.origin c := by
  induction t with
  | unit => cases origin
  | cause d other =>
    obtain ⟨rfl, rfl⟩ := origin
    exact localRoots rfl
  | hole n impossible => exact Empty.elim impossible
  | operation g input ih => exact ih localRoots origin
  | tensor left right ihl ihr =>
    rcases origin with leftOrigin | rightOrigin
    · exact ihl localRoots.1 leftOrigin
    · exact ihr localRoots.2 rightOrigin

theorem owned_origin {S : ArchitectureSignature} {n} (t : S.Occurrence (.node n))
    (localRoots : t.onlyLocalRoot (S.owner n)) : t.hasRoot (S.owner n) (S.origin (S.owner n)) := by
  obtain ⟨root, origin⟩ := t.rooted ()
  have same := t.local_root_identity (S.owner n) root localRoots origin
  exact same ▸ origin

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

theorem effectNode_owner (S : ArchitectureSignature)
    (marked : (n : S.Node) → Option (Term.CycleBoundary S n))
    (c : S.Cause) (n : S.Node) (member : n ∈ S.effectNodes marked c) : S.owner n = c := by
  have selected := (List.mem_filter.mp member).2
  simp only [Bool.and_eq_true, beq_iff_eq] at selected
  exact selected.1

/-- Derived supplier dependency, not categorical composition. In particular,
an edge through one tensor factor never asserts equality of its endpoints. -/
inductive Depends (S : ArchitectureSignature) : S.Node → S.Node → Prop where
  | refl (n) : Depends S n n
  | step (g) (n) (supplies : n ∈ (S.input g).nodes) : Depends S n (S.output g)
  | trans {n m k} : Depends S n m → Depends S m k → Depends S n k

end ArchitectureSignature


end ArchiScript
