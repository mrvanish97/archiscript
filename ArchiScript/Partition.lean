import Std

namespace ArchiScript

/-- A value domain is a predicate. It need not be a partition. -/
abbrev Domain (α : Type u) := α → Prop

namespace Domain

def complement (s : Domain α) : Domain α := fun x => ¬ s x

/-- The remainder of a subdomain inside its explicitly justified parent. -/
def relativeComplement (parent excluded : Domain α)
    (_contained : ∀ x, excluded x → parent x) : Domain α :=
  fun x => parent x ∧ ¬ excluded x

theorem mem_complement_iff (s : Domain α) (x : α) : complement s x ↔ ¬ s x := Iff.rfl

theorem cover_complement (s : Domain α) (x : α) : s x ∨ complement s x :=
  Classical.em (s x)

theorem disjoint_complement (s : Domain α) (x : α) : ¬ (s x ∧ complement s x) :=
  fun h => h.2 h.1

end Domain

/--
A partition (VDP) is a nonempty carrier classified by finitely many abstract
member indices. `member_inhabited` rules out unused indices. The semantic
member is the classifier fiber, not its index.
-/
structure Partition where
  Carrier : Type u
  MemberIndex : Type v
  carrierNonempty : Nonempty Carrier
  memberIndexDecidableEq : DecidableEq MemberIndex
  memberIndices : List MemberIndex
  memberIndices_complete : ∀ i, i ∈ memberIndices
  classify : Carrier → MemberIndex
  member_inhabited : ∀ i, ∃ x, classify x = i

namespace Partition

instance (P : Partition) : Nonempty P.Carrier := P.carrierNonempty
instance (P : Partition) : DecidableEq P.MemberIndex := P.memberIndexDecidableEq

/-- The actual semantic subdomain represented by a member index. -/
def member (P : Partition) (i : P.MemberIndex) : Domain P.Carrier :=
  fun x => P.classify x = i

/--
The selected semantic regions agree with the classifier's actual members.
Supporting subdomains may overlap or be grouped into one selected region.
This proposition is separate from the partition's data and identity.
-/
def Realizes (P : Partition) (regions : P.MemberIndex → Domain P.Carrier) : Prop :=
  ∀ i x, P.member i x ↔ regions i x

theorem self_member (P : Partition) (i : P.MemberIndex) (x : P.Carrier) :
    P.member i x ↔ P.classify x = i := Iff.rfl

theorem coverage (P : Partition) (x : P.Carrier) : ∃ i, P.member i x :=
  ⟨P.classify x, rfl⟩

theorem disjoint (P : Partition) {i j : P.MemberIndex} (hne : i ≠ j) (x : P.Carrier) :
    ¬ (P.member i x ∧ P.member j x) := by
  intro h
  exact hne (h.1.symm.trans h.2)

theorem member_nonempty (P : Partition) (i : P.MemberIndex) : ∃ x, P.member i x :=
  P.member_inhabited i

/-- A carrier value tagged with proof of its unique semantic member. -/
abbrev Total (P : Partition) := Sigma fun i : P.MemberIndex => {x : P.Carrier // P.member i x}

def erase (P : Partition) : P.Total → P.Carrier := fun t => t.2.1

/-- Minimal isomorphism data, kept independent of external libraries. -/
structure Iso (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

theorem Iso.injective (e : Iso α β) {x y : α} (h : e.toFun x = e.toFun y) : x = y := by
  rw [← e.left_inv x, ← e.left_inv y, h]

def totalIso (P : Partition) : Iso P.Total P.Carrier where
  toFun := P.erase
  invFun := fun x => ⟨P.classify x, ⟨x, rfl⟩⟩
  left_inv := by
    intro t
    rcases t with ⟨m, ⟨x, hx⟩⟩
    simp only [erase]
    cases hx
    rfl
  right_inv := by intro x; rfl

/-- Isomorphism may transport values to a different carrier; it is not equality. -/
structure PartitionIso (P Q : Partition) where
  carrier : Iso P.Carrier Q.Carrier
  memberIndex : Iso P.MemberIndex Q.MemberIndex
  classify_commutes : ∀ x, Q.classify (carrier.toFun x) = memberIndex.toFun (P.classify x)

theorem partitionIso_preserves_member {P Q : Partition} (r : PartitionIso P Q)
    (i : P.MemberIndex) (x : P.Carrier) :
    P.member i x ↔ Q.member (r.memberIndex.toFun i) (r.carrier.toFun x) := by
  simp only [member]
  rw [r.classify_commutes]
  constructor
  · intro h
    exact congrArg r.memberIndex.toFun h
  · intro h
    exact r.memberIndex.injective h

/--
Pure relabeling keeps the carrier type and every carrier value fixed. The
equality field is only a type transport, never an arbitrary carrier bijection.
-/
structure Relabeling (P Q : Partition) where
  sameCarrier : P.Carrier = Q.Carrier
  memberIndex : Iso P.MemberIndex Q.MemberIndex
  classify_commutes : ∀ x,
    Q.classify (sameCarrier ▸ x) = memberIndex.toFun (P.classify x)

theorem relabeling_preserves_member {P Q : Partition} (r : Relabeling P Q)
    (i : P.MemberIndex) (x : P.Carrier) :
    P.member i x ↔ Q.member (r.memberIndex.toFun i) (r.sameCarrier ▸ x) := by
  simp only [member]
  rw [r.classify_commutes]
  constructor
  · exact fun h => congrArg r.memberIndex.toFun h
  · exact fun h => r.memberIndex.injective h

end Partition
end ArchiScript
