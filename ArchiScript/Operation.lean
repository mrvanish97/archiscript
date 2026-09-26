import ArchiScript.Partition

namespace ArchiScript

/-- An operation is exactly a partial function on semantic member indices. -/
structure Operation (X Y : Partition) where
  run : X.MemberIndex → Option Y.MemberIndex

namespace Operation

universe u

/-- Organizational responsibility, independent of source-code location. -/
abbrev ResponsibilityOwner := String

/-- A source identity uses repository, path, and optional symbol. Lines are navigation metadata. -/
structure SourceRef where
  repository : String
  path : String
  symbol : Option String := none
  startLine : Option Nat := none
  endLine : Option Nat := none
  revision : Option String := none
  deriving BEq, Repr

/-- Line ranges and revisions may change without changing the source identity. -/
def SourceRef.sameIdentity (a b : SourceRef) : Bool :=
  a.repository == b.repository && a.path == b.path && a.symbol == b.symbol

/-- References to conformance evidence are claims to inspect, not proofs. -/
inductive EvidenceKind where
  | test | staticAnalysis | formalProof | manualReview | runtimeTrace | externalContract
  deriving BEq, Repr

structure EvidenceRef where
  kind : EvidenceKind
  reference : String
  deriving BEq, Repr

/-- The primary site is where an implementation agent starts. -/
structure ImplementationBinding where
  primary : SourceRef
  supporting : List SourceRef := []
  evidence : List EvidenceRef := []
  deriving BEq, Repr

/-- A disposition records intent separately from verified source existence. -/
inductive ImplementationDisposition where
  | planned (binding : ImplementationBinding)
  | resolved (binding : ImplementationBinding)
  | external (reference : String)
  | intentionallyAbstract (reason : String)
  | unimplemented (reason : String)
  deriving BEq, Repr

def ImplementationDisposition.binding? : ImplementationDisposition → Option ImplementationBinding
  | .planned binding | .resolved binding => some binding
  | .external _ | .intentionallyAbstract _ | .unimplemented _ => none

instance (X Y : Partition) : CoeFun (Operation X Y) (fun _ => X.MemberIndex → Option Y.MemberIndex) :=
  ⟨Operation.run⟩

@[ext] theorem ext {X Y : Partition} {f g : Operation X Y} (h : ∀ m, f m = g m) : f = g := by
  cases f with
  | mk frun =>
    cases g with
    | mk grun =>
      congr
      funext m
      exact h m

def id (X : Partition) : Operation X X := ⟨fun m => some m⟩

/-- Right-to-left composition: `(g.comp f) m` first runs `f`, then `g`. -/
def comp {X Y Z : Partition} (g : Operation Y Z) (f : Operation X Y) : Operation X Z :=
  ⟨fun m => (f m).bind g.run⟩

@[simp] theorem id_apply (X : Partition) (m : X.MemberIndex) : id X m = some m := rfl

@[simp] theorem comp_apply {X Y Z : Partition} (g : Operation Y Z) (f : Operation X Y)
    (m : X.MemberIndex) : g.comp f m = (f m).bind g.run := rfl

@[simp] theorem id_comp {X Y : Partition} (f : Operation X Y) : (id Y).comp f = f := by
  ext m
  cases h : f m <;> simp [comp, id, h]

@[simp] theorem comp_id {X Y : Partition} (f : Operation X Y) : f.comp (id X) = f := by
  ext m
  simp [comp, id]

theorem comp_assoc {W X Y Z : Partition} (h : Operation Y Z) (g : Operation X Y)
    (f : Operation W X) : (h.comp g).comp f = h.comp (g.comp f) := by
  ext m
  cases hf : f m <;> simp [comp, hf]

/-- A typed witness that a source/target pair belongs to a partial map. -/
structure Branch {X Y : Partition} (op : Operation X Y) where
  source : X.MemberIndex
  target : Y.MemberIndex
  belongs : op source = some target

theorem Branch.in_operation {X Y : Partition} {op : Operation X Y} (b : Branch op) :
    op b.source = some b.target := b.belongs

/--
A typed operation declaration. Branch names are scoped here and resolve through
one function, so one declaration cannot assign conflicting branches to a name.
-/
structure Declaration where
  source : Partition.{u, u}
  target : Partition.{u, u}
  operation : Operation source target
  BranchName : Type u
  branchNameDecidableEq : DecidableEq BranchName
  branchNames : List BranchName
  branchNames_complete : ∀ name : BranchName, name ∈ branchNames
  branchNames_nodup : branchNames.Nodup
  branch : BranchName → Branch operation
  /-- Responsibility tags; these do not grant authority or assert effects. -/
  responsibilityOwners : List ResponsibilityOwner := []
  /-- `none` inherits operation responsibility; `some tags` replaces it. -/
  branchResponsibilityOwners : BranchName → Option (List ResponsibilityOwner) := fun _ => none
  /-- A default disposition; `none` leaves a branch without a disposition. -/
  implementation : Option ImplementationDisposition := none
  /-- `none` inherits the operation disposition; `some` overrides it. -/
  branchImplementation : BranchName → Option ImplementationDisposition := fun _ => none

instance (d : Declaration) : DecidableEq d.BranchName := d.branchNameDecidableEq

/-- An explicit empty override means unassigned; it does not inherit. -/
def Declaration.effectiveResponsibility (d : Declaration) (name : d.BranchName) :
    List ResponsibilityOwner :=
  (d.branchResponsibilityOwners name).getD d.responsibilityOwners

/-- A branch override takes precedence over the operation default. -/
def Declaration.effectiveImplementation (d : Declaration) (name : d.BranchName) :
    Option ImplementationDisposition :=
  (d.branchImplementation name).orElse fun _ => d.implementation

/--
A model-scoped declaration registry. `OperationName` is stable declaration
identity; aliases resolve the same name instead of constructing a fresh ID.
-/
structure Registry where
  OperationName : Type u
  operationNameDecidableEq : DecidableEq OperationName
  operationNames : List OperationName
  operationNames_complete : ∀ name : OperationName, name ∈ operationNames
  operationNames_nodup : operationNames.Nodup
  resolve : OperationName → Declaration

instance (R : Registry) : DecidableEq R.OperationName := R.operationNameDecidableEq

/-- Branch identity is exactly the dependent pair (operation identity, name). -/
structure BranchAddress (R : Registry) where
  operation : R.OperationName
  name : (R.resolve operation).BranchName

/-- Enumerate canonical addresses, including branches with missing metadata. -/
def Registry.branchAddresses (R : Registry) : List (BranchAddress R) :=
  R.operationNames.flatMap fun operation =>
    (R.resolve operation).branchNames.map fun name => ⟨operation, name⟩

def Registry.resolveBranch (R : Registry) (address : BranchAddress R) :
    Branch (R.resolve address.operation).operation :=
  (R.resolve address.operation).branch address.name

/-- Responsibility follows the canonical declaration, including through aliases. -/
def Registry.resolveBranchResponsibility (R : Registry) (address : BranchAddress R) :
    List ResponsibilityOwner :=
  (R.resolve address.operation).effectiveResponsibility address.name

/-- Resolve the one effective implementation disposition for a canonical branch. -/
def Registry.resolveBranchImplementation (R : Registry) (address : BranchAddress R) :
    Option ImplementationDisposition :=
  (R.resolve address.operation).effectiveImplementation address.name

def Registry.branchesWithoutResponsibility (R : Registry) : List (BranchAddress R) :=
  R.branchAddresses.filter fun address => (R.resolveBranchResponsibility address).isEmpty

def Registry.branchesWithoutImplementation (R : Registry) : List (BranchAddress R) :=
  R.branchAddresses.filter fun address => (R.resolveBranchImplementation address).isNone

/-- Reverse navigation from a declared primary or supporting source identity. -/
def Registry.branchesAt (R : Registry) (source : SourceRef) : List (BranchAddress R) :=
  R.branchAddresses.filter fun address =>
    match (R.resolveBranchImplementation address).bind ImplementationDisposition.binding? with
    | none => false
    | some binding =>
      binding.primary.sameIdentity source ||
        binding.supporting.any (fun candidate => candidate.sameIdentity source)

theorem BranchAddress.operation_eq {R : Registry} {a b : BranchAddress R}
    (h : a = b) : a.operation = b.operation := congrArg BranchAddress.operation h

end Operation
end ArchiScript
