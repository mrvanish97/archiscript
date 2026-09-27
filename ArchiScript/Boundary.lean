import ArchiScript.Operation

namespace ArchiScript

/-- An external assertion about values admitted at a boundary. Its presence
records trust; it does not prove that the named system enforces the claim. -/
structure ExternalBoundary where
  source : String
  scope : String
  claim : String
  revision : String
  identified : source ≠ "" ∧ scope ≠ "" ∧ claim ≠ "" ∧ revision ≠ ""
  deriving Repr

/-- Why this carrier, rather than a convenient subset, is the model's universe.
The derived case checks an exact modeled image over an upstream semantic member.
It does not assert that production code implements `emits`. -/
inductive CarrierOrigin : Type → Type 1 where
  | externalRoot {α : Type} (boundary : ExternalBoundary) : CarrierOrigin α
  | externalNarrowing {α β : Type} (upstream : CarrierOrigin β)
      (guarantee : ExternalBoundary) : CarrierOrigin α
  | internalOutput {α : Type} (producer : String) (source target : Partition)
      (operation : Operation source target)
      (sourceOrigin : CarrierOrigin source.Carrier)
      (sameCarrier : target.Carrier = α) : CarrierOrigin α
  | derived {α : Type} (upstreamId sourceMemberId : String)
      (upstream : SemanticPartition)
      (upstreamOrigin : CarrierOrigin upstream.partition.Carrier)
      (sourceMember : upstream.partition.MemberIndex)
      (emits : upstream.partition.Carrier → Option α)
      (emitsOnlySource : ∀ x y, emits x = some y →
        upstream.members sourceMember x)
      (coversCarrier : ∀ y : α, ∃ x, emits x = some y) : CarrierOrigin α

/-- Constructor closure concerns a carrier's internal values. It cannot
establish that an external boundary emits only values of this carrier. -/
structure CarrierClosure (α : Type u) where
  values : List α
  complete : ∀ x : α, x ∈ values

/-- A definition indexed by its exact Lean denotation. Composition cannot
describe a different predicate from the one used by `HasMembers`. The atomic
case is a Lean predicate, not a prose formula or a proof of external facts. -/
inductive DomainDerivation (α : Type u) : Domain α → Type (u + 1) where
  | predicate (meaning : Domain α) : DomainDerivation α meaning
  | opaque (reason : String) (identified : reason ≠ "")
      (meaning : Domain α) : DomainDerivation α meaning
  | intersection {a b : Domain α} (left : DomainDerivation α a)
      (right : DomainDerivation α b) :
      DomainDerivation α (fun x => a x ∧ b x)
  | union {a b : Domain α} (left : DomainDerivation α a)
      (right : DomainDerivation α b) :
      DomainDerivation α (fun x => a x ∨ b x)
  | relativeComplement {parent excluded : Domain α}
      (base : DomainDerivation α parent) (removed : DomainDerivation α excluded)
      (contained : ∀ x, excluded x → parent x) :
      DomainDerivation α (Domain.relativeComplement parent excluded contained)

def DomainDerivation.hasOpaque {meaning : Domain α}
    (definition : DomainDerivation α meaning) : Bool :=
  match definition with
  | .predicate _ => false
  | .opaque _ _ _ => true
  | .intersection left right | .union left right => left.hasOpaque || right.hasOpaque
  | .relativeComplement base removed _ => base.hasOpaque || removed.hasOpaque

structure SelectedMember (α : Type u) where
  meaning : Domain α
  definition : DomainDerivation α meaning

/-- A supporting subdomain may overlap other regions and need not be a VDP
member. Its base and containment are explicit even when meaning is opaque. -/
structure NamedSubdomain (α : Type u) where
  name : String
  base : Domain α
  meaning : Domain α
  contained : ∀ x, meaning x → base x
  definition : DomainDerivation α meaning

/-- Review/handoff evidence. Low-level partitions remain freely constructible;
this object records a carrier origin and the status of every selected member. -/
structure ArchitecturalPartition where
  partition : Partition
  carrierOrigin : CarrierOrigin partition.Carrier
  carrierClosure : Option (CarrierClosure partition.Carrier) := none
  selectedMembers : partition.MemberIndex → SelectedMember partition.Carrier
  supportingSubdomains : List (NamedSubdomain partition.Carrier) := []
  hasMembers : partition.HasMembers (fun i => (selectedMembers i).meaning)

/-- A reviewable operation carries architectural evidence for both endpoints.
This does not prove runtime value selection or implementation conformance. -/
structure ArchitecturalOperation where
  source : ArchitecturalPartition
  target : ArchitecturalPartition
  operation : Operation source.partition target.partition

/-- The handoff container cannot list an operation without endpoint evidence.
Registries and presentation projections can carry additional metadata. -/
structure Architecture where
  operations : List ArchitecturalOperation
  standalonePartitions : List ArchitecturalPartition := []

def ArchitecturalPartition.opaqueMembers (P : ArchitecturalPartition) :
    List P.partition.MemberIndex :=
  P.partition.memberIndices.filter fun i =>
    (P.selectedMembers i).definition.hasOpaque

def ArchitecturalPartition.opaqueSupportingSubdomains (P : ArchitecturalPartition) :
    List String :=
  (P.supportingSubdomains.filter fun s =>
    s.definition.hasOpaque).map (·.name)

end ArchiScript
