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
Carrier origin is a boundary statement. It does not model computation or a
value-producing dataflow between carriers. Operations relate VDP members only. -/
inductive CarrierOrigin : Type → Type 1 where
  | externalRoot {α : Type} (boundary : ExternalBoundary) : CarrierOrigin α
  | externalNarrowing {α β : Type} (upstream : CarrierOrigin β)
      (guarantee : ExternalBoundary) : CarrierOrigin α
  | architecturalDomain {α : Type} (identity : String)
      (identified : identity ≠ "") : CarrierOrigin α

/-- Constructor closure concerns a carrier's internal values. It cannot
establish that an external boundary emits only values of this carrier. -/
structure CarrierClosure (α : Type u) where
  values : List α
  complete : ∀ x : α, x ∈ values

structure SelectedMember (α : Type u) where
  meaning : Domain α
  definition : DomainDerivation α meaning

abbrev NamedSubdomain := Subdomain

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

def ArchitecturalPartition.opaqueMembers (P : ArchitecturalPartition)
    [MemberEnumeration P.partition.MemberIndex] :
    List P.partition.MemberIndex :=
  P.partition.memberIndices.filter fun i =>
    (P.selectedMembers i).definition.hasOpaque

def ArchitecturalPartition.opaqueSupportingSubdomains (P : ArchitecturalPartition) :
    List String :=
  (P.supportingSubdomains.filter fun s =>
    s.definition.hasOpaque).map (·.name)

end ArchiScript
