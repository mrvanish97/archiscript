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

/-- Independent aggregation: every pair of carrier values and every pair of
members remains present, including when both factors are the same VDP. -/
def tensor (P Q : Partition) : Partition where
  Carrier := P.Carrier × Q.Carrier
  MemberIndex := P.MemberIndex × Q.MemberIndex
  carrierNonempty := ⟨Classical.choice P.carrierNonempty, Classical.choice Q.carrierNonempty⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := P.memberIndices.flatMap fun i => Q.memberIndices.map fun j => (i, j)
  memberIndices_complete := by
    intro ⟨i, j⟩
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨i, P.memberIndices_complete i, j, Q.memberIndices_complete j, rfl⟩
  classify := fun xy => (P.classify xy.1, Q.classify xy.2)
  member_inhabited := by
    intro ⟨i, j⟩
    obtain ⟨x, hx⟩ := P.member_inhabited i
    obtain ⟨y, hy⟩ := Q.member_inhabited j
    exact ⟨(x, y), Prod.ext hx hy⟩

/-- The tensor unit has one value and one semantic member. -/
def unit : Partition where
  Carrier := Unit
  MemberIndex := Unit
  carrierNonempty := ⟨()⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [()]
  memberIndices_complete := by intro i; cases i; simp
  classify := fun _ => ()
  member_inhabited := by intro i; cases i; exact ⟨(), rfl⟩

/-- The actual semantic subdomain represented by a member index. -/
def member (P : Partition) (i : P.MemberIndex) : Domain P.Carrier :=
  fun x => P.classify x = i

@[simp] theorem tensor_member_iff (P Q : Partition)
    (i : P.MemberIndex) (j : Q.MemberIndex)
    (x : P.Carrier) (y : Q.Carrier) :
    (P.tensor Q).member (i, j) (x, y) ↔ P.member i x ∧ Q.member j y := by
  simp only [member, tensor, Prod.mk.injEq]

@[simp] theorem tensor_classify (P Q : Partition) (x : P.Carrier) (y : Q.Carrier) :
    (P.tensor Q).classify (x, y) = (P.classify x, Q.classify y) := rfl

/--
The selected semantic members agree with the classifier's actual fibers.
Supporting subdomains may overlap or be grouped into one selected member.
The member predicates must be stated independently for this to provide
semantic evidence; Lean cannot enforce that authoring discipline.
-/
def HasMembers (P : Partition) (members : P.MemberIndex → Domain P.Carrier) : Prop :=
  ∀ i x, P.member i x ↔ members i x

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

namespace PartitionIso

def refl (P : Partition) : PartitionIso P P where
  carrier := {
    toFun := id
    invFun := id
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
  }
  memberIndex := {
    toFun := id
    invFun := id
    left_inv := by intro i; rfl
    right_inv := by intro i; rfl
  }
  classify_commutes := by intro x; rfl

def symm {P Q : Partition} (e : PartitionIso P Q) : PartitionIso Q P where
  carrier := {
    toFun := e.carrier.invFun
    invFun := e.carrier.toFun
    left_inv := e.carrier.right_inv
    right_inv := e.carrier.left_inv
  }
  memberIndex := {
    toFun := e.memberIndex.invFun
    invFun := e.memberIndex.toFun
    left_inv := e.memberIndex.right_inv
    right_inv := e.memberIndex.left_inv
  }
  classify_commutes := by
    intro y
    apply e.memberIndex.injective
    change
      e.memberIndex.toFun (P.classify (e.carrier.invFun y)) =
        e.memberIndex.toFun (e.memberIndex.invFun (Q.classify y))
    rw [← e.classify_commutes (e.carrier.invFun y)]

end PartitionIso

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

/-- A partition accompanied by its stated semantic members and correspondence proof.
This review and handoff object does not change the identity of its partition. -/
structure SemanticPartition where
  partition : Partition
  members : partition.MemberIndex → Domain partition.Carrier
  hasMembers : partition.HasMembers members

namespace SemanticPartition

/-- Product members inherit their independently stated meanings from the two
factors; no product predicate needs to be supplied by an author. -/
def tensor (P Q : SemanticPartition) : SemanticPartition where
  partition := P.partition.tensor Q.partition
  members := fun ij xy => P.members ij.1 xy.1 ∧ Q.members ij.2 xy.2
  hasMembers := by
    intro ⟨i, j⟩ ⟨x, y⟩
    rw [Partition.tensor_member_iff]
    exact and_congr (P.hasMembers i x) (Q.hasMembers j y)

def unit : SemanticPartition where
  partition := Partition.unit
  members := fun _ _ => True
  hasMembers := by intro i x; cases i; cases x; simp [Partition.member, Partition.unit]

/-- The stated semantic members cover every value of the declared carrier. -/
theorem members_cover (S : SemanticPartition) (x : S.partition.Carrier) :
    ∃ i, S.members i x := by
  obtain ⟨i, hi⟩ := S.partition.coverage x
  exact ⟨i, (S.hasMembers i x).mp hi⟩

/-- Every selected semantic member has at least one carrier value. -/
theorem member_nonempty (S : SemanticPartition) (i : S.partition.MemberIndex) :
    ∃ x, S.members i x := by
  obtain ⟨x, hx⟩ := S.partition.member_nonempty i
  exact ⟨x, (S.hasMembers i x).mp hx⟩

/-- Distinct selected semantic members cannot share a carrier value. -/
theorem members_disjoint (S : SemanticPartition)
    {i j : S.partition.MemberIndex} (different : i ≠ j)
    (x : S.partition.Carrier) : ¬ (S.members i x ∧ S.members j x) := by
  intro h
  exact S.partition.disjoint different x
    ⟨(S.hasMembers i x).mpr h.1, (S.hasMembers j x).mpr h.2⟩

end SemanticPartition

end ArchiScript
