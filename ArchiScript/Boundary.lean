import ArchiScript.Partition

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
inductive CarrierProvenance : Type → Type 1 where
  | externalRoot {α : Type} (boundary : ExternalBoundary) : CarrierProvenance α
  | externalNarrowing {α : Type} (guarantee : ExternalBoundary) : CarrierProvenance α
  | derived {α : Type} (upstreamId sourceMemberId : String) (upstream : SemanticPartition)
      (upstreamProvenance : CarrierProvenance upstream.partition.Carrier)
      (sourceMember : upstream.partition.MemberIndex)
      (emits : upstream.partition.Carrier → Option α)
      (emitsOnlySource : ∀ x y, emits x = some y →
        upstream.members sourceMember x)
      (coversCarrier : ∀ y : α, ∃ x, emits x = some y) : CarrierProvenance α
  | closedConstructors {α : Type} (values : List α)
      (complete : ∀ x : α, x ∈ values) : CarrierProvenance α

/-- A named semantic region. An opaque definition has an extension, but no
formula available for deduction or inspection. The author must supply a reason
so the weaker evidence remains visible in review. -/
inductive SubdomainDefinition where
  | formula (description : String)
  | opaque (reason : String)
  deriving Repr

structure SelectedMember (α : Type u) where
  meaning : Domain α
  definition : SubdomainDefinition

/-- A supporting subdomain may overlap other regions and need not be a VDP
member. Its base and containment are explicit even when meaning is opaque. -/
structure NamedSubdomain (α : Type u) where
  name : String
  base : Domain α
  meaning : Domain α
  contained : ∀ x, meaning x → base x
  definition : SubdomainDefinition

/-- Review/handoff evidence. Low-level partitions remain freely constructible;
this object records a carrier origin and the status of every selected member. -/
structure ArchitecturalPartition where
  partition : Partition
  carrierProvenance : CarrierProvenance partition.Carrier
  selectedMembers : partition.MemberIndex → SelectedMember partition.Carrier
  supportingSubdomains : List (NamedSubdomain partition.Carrier) := []
  hasMembers : partition.HasMembers (fun i => (selectedMembers i).meaning)

def ArchitecturalPartition.opaqueMembers (P : ArchitecturalPartition) :
    List P.partition.MemberIndex :=
  P.partition.memberIndices.filter fun i =>
    match (P.selectedMembers i).definition with
    | .opaque _ => true
    | .formula _ => false

def ArchitecturalPartition.opaqueSupportingSubdomains (P : ArchitecturalPartition) :
    List String :=
  (P.supportingSubdomains.filter fun s =>
    match s.definition with
    | .opaque _ => true
    | .formula _ => false).map (·.name)

end ArchiScript
