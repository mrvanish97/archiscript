import ArchiScript.Subdomain

namespace ArchiScript

/--
Computable enumeration for algorithms and presentation. Its order is not part
of a VDP's identity; unlike the proof of finiteness, this is executable data.
-/
class MemberEnumeration (α : Type v) where
  indices : List α
  complete : ∀ i : α, i ∈ indices

namespace MemberEnumeration

instance : MemberEnumeration Bool where
  indices := [false, true]
  complete := by intro i; cases i <;> simp

instance : MemberEnumeration Unit where
  indices := [()]
  complete := by intro i; cases i; simp

instance [MemberEnumeration α] [MemberEnumeration β] :
    MemberEnumeration (α × β) where
  indices := (MemberEnumeration.indices (α := α)).flatMap fun a =>
    (MemberEnumeration.indices (α := β)).map fun b => (a, b)
  complete := by
    intro ⟨a, b⟩
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨a, MemberEnumeration.complete a, b, MemberEnumeration.complete b, rfl⟩

instance [MemberEnumeration α] [MemberEnumeration β] :
    MemberEnumeration (Sum α β) where
  indices := (MemberEnumeration.indices (α := α)).map Sum.inl ++
    (MemberEnumeration.indices (α := β)).map Sum.inr
  complete := by
    intro i
    cases i with
    | inl a =>
        simp only [List.mem_append, List.mem_map]
        exact Or.inl ⟨a, MemberEnumeration.complete a, rfl⟩
    | inr b =>
        simp only [List.mem_append, List.mem_map]
        exact Or.inr ⟨b, MemberEnumeration.complete b, rfl⟩

end MemberEnumeration


/-- A VDP is a finite, nonempty family of declared semantic Subdomains
partitioning the whole carrier. No classifier is accepted as its definition. -/
structure Partition where
  Carrier : Type u
  MemberIndex : Type v
  memberIndexDecidableEq : DecidableEq MemberIndex
  memberIndexFinite : ∃ indices : List MemberIndex, ∀ i, i ∈ indices
  memberIndexNonempty : Nonempty MemberIndex
  members : MemberIndex → Subdomain Carrier
  coverage : ∀ x, ∃ i, (members i).meaning x
  disjoint : ∀ {i j}, i ≠ j → ∀ x, ¬ ((members i).meaning x ∧ (members j).meaning x)

set_option linter.checkUnivs false in
/-- Preferred mathematical name; `Partition` remains the algebra's spelling. -/
abbrev VDP := Partition

namespace Partition

/-- A genuinely closed finite carrier may use constructor equality as its
semantic regions. The exhaustive carrier enumeration is required evidence. -/
abbrev closed (α : Type u) [DecidableEq α] (name : String)
    (finite : ∃ xs : List α, ∀ x, x ∈ xs) (inhabited : Nonempty α) : Partition where
  Carrier := α
  MemberIndex := α
  memberIndexDecidableEq := inferInstance
  memberIndexFinite := finite
  memberIndexNonempty := inhabited
  members := fun i => Subdomain.root name (fun x => x = i) ⟨i, rfl⟩ (.predicate _)
  coverage := fun x => ⟨x, rfl⟩
  disjoint := by
    intro i j different x h
    exact different (h.1.symm.trans h.2)

/-- Reuse all the evidence of a declared split of the entire carrier type. -/
abbrev ofSplit {parent : Subdomain α} (s : SemanticSplit parent)
    (entire : ∀ x, parent.meaning x) : Partition where
  Carrier := α
  MemberIndex := s.Index
  memberIndexDecidableEq := s.indexDecidableEq
  memberIndexFinite := ⟨s.indices, s.indices_complete⟩
  memberIndexNonempty := s.indexNonempty
  members := s.children
  coverage := fun x => s.covers x (entire x)
  disjoint := fun h x => s.disjoint _ _ h x

instance (P : Partition) : DecidableEq P.MemberIndex := P.memberIndexDecidableEq
instance (P : Partition) : Nonempty P.MemberIndex := P.memberIndexNonempty

def member (P : Partition) (i : P.MemberIndex) : Domain P.Carrier :=
  (P.members i).meaning

theorem member_nonempty (P : Partition) (i : P.MemberIndex) : ∃ x, P.member i x :=
  (P.members i).nonempty

theorem carrierNonempty (P : Partition) : Nonempty P.Carrier := by
  obtain ⟨i⟩ := P.memberIndexNonempty
  obtain ⟨x, _⟩ := P.member_nonempty i
  exact ⟨x⟩

instance (P : Partition) : Nonempty P.Carrier := P.carrierNonempty

def memberIndices (P : Partition) [MemberEnumeration P.MemberIndex] : List P.MemberIndex :=
  MemberEnumeration.indices

theorem memberIndices_complete (P : Partition) [MemberEnumeration P.MemberIndex]
    (i : P.MemberIndex) : i ∈ P.memberIndices := MemberEnumeration.complete i

theorem member_unique (P : Partition) {i j : P.MemberIndex} {x : P.Carrier}
    (hi : P.member i x) (hj : P.member j x) : i = j := by
  by_cases h : i = j
  · exact h
  · exact False.elim (P.disjoint h x ⟨hi, hj⟩)

/-- Optional classical lookup, derived only after semantic coverage is proved. -/
noncomputable def classify (P : Partition) (x : P.Carrier) : P.MemberIndex :=
  Classical.choose (P.coverage x)

theorem classify_spec (P : Partition) (x : P.Carrier) : P.member (P.classify x) x :=
  Classical.choose_spec (P.coverage x)

theorem self_member (P : Partition) (i : P.MemberIndex) (x : P.Carrier) :
    P.member i x ↔ P.classify x = i := by
  constructor
  · exact fun h => P.member_unique (P.classify_spec x) h
  · intro h
    rw [← h]
    exact P.classify_spec x

/-- Executable lookup requires separate decidability evidence. The witness is
checked against the primary members, not used to define them. -/
def lookup (P : Partition) [MemberEnumeration P.MemberIndex] (x : P.Carrier)
    [DecidablePred (fun i => P.member i x)] : Option P.MemberIndex :=
  P.memberIndices.find? (fun i => decide (P.member i x))

def HasMembers (P : Partition) (meanings : P.MemberIndex → Domain P.Carrier) : Prop :=
  ∀ i x, P.member i x ↔ meanings i x

abbrev tensor (P Q : Partition) : Partition where
  Carrier := P.Carrier × Q.Carrier
  MemberIndex := P.MemberIndex × Q.MemberIndex
  memberIndexDecidableEq := inferInstance
  memberIndexFinite := by
    obtain ⟨is, his⟩ := P.memberIndexFinite
    obtain ⟨js, hjs⟩ := Q.memberIndexFinite
    refine ⟨is.flatMap (fun i => js.map fun j => (i, j)), ?_⟩
    intro ⟨i, j⟩
    exact List.mem_flatMap.mpr ⟨i, his i, List.mem_map.mpr ⟨j, hjs j, rfl⟩⟩
  memberIndexNonempty := inferInstance
  members := fun ij => Subdomain.root
    ((P.members ij.1).name ++ " ⊗ " ++ (Q.members ij.2).name)
    (fun xy => P.member ij.1 xy.1 ∧ Q.member ij.2 xy.2)
    (by
      obtain ⟨x, hx⟩ := P.member_nonempty ij.1
      obtain ⟨y, hy⟩ := Q.member_nonempty ij.2
      exact ⟨(x, y), hx, hy⟩)
    (.predicate _)
  coverage := by
    intro ⟨x, y⟩
    obtain ⟨i, hi⟩ := P.coverage x
    obtain ⟨j, hj⟩ := Q.coverage y
    exact ⟨(i, j), hi, hj⟩
  disjoint := by
    intro ⟨i, j⟩ ⟨k, l⟩ hne ⟨x, y⟩ h
    exact hne (Prod.ext (P.member_unique h.1.1 h.2.1) (Q.member_unique h.1.2 h.2.2))

abbrev unit : Partition where
  Carrier := Unit
  MemberIndex := Unit
  memberIndexDecidableEq := inferInstance
  memberIndexFinite := ⟨[()], by intro i; cases i; simp⟩
  memberIndexNonempty := ⟨()⟩
  members := fun _ => Subdomain.root "Unit" (fun _ => True) ⟨(), trivial⟩ (.predicate _)
  coverage := fun _ => ⟨(), trivial⟩
  disjoint := by intro i j h; exact False.elim (h (Subsingleton.elim _ _))

@[simp] theorem tensor_member_iff (P Q : Partition)
    (i : P.MemberIndex) (j : Q.MemberIndex) (x : P.Carrier) (y : Q.Carrier) :
    (P.tensor Q).member (i, j) (x, y) ↔ P.member i x ∧ Q.member j y := Iff.rfl

@[simp] theorem tensor_classify (P Q : Partition) (x : P.Carrier) (y : Q.Carrier) :
    (P.tensor Q).classify (x, y) = (P.classify x, Q.classify y) :=
  ((P.tensor Q).self_member _ _).mp ⟨P.classify_spec x, Q.classify_spec y⟩

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

noncomputable def totalIso (P : Partition) : Iso P.Total P.Carrier where
  toFun := P.erase
  invFun := fun x => ⟨P.classify x, ⟨x, P.classify_spec x⟩⟩
  left_inv := by
    intro ⟨i, x, hx⟩
    have h := (P.self_member i x).mp hx
    cases h
    rfl
  right_inv := fun _ => rfl

/-- Carrier and index isomorphisms must preserve the declared semantic regions. -/
structure PartitionIso (P Q : Partition) where
  carrier : Iso P.Carrier Q.Carrier
  memberIndex : Iso P.MemberIndex Q.MemberIndex
  preserves : ∀ i x, P.member i x ↔ Q.member (memberIndex.toFun i) (carrier.toFun x)

namespace PartitionIso

theorem classify_commutes {P Q : Partition} (e : PartitionIso P Q) (x : P.Carrier) :
    Q.classify (e.carrier.toFun x) = e.memberIndex.toFun (P.classify x) :=
  (Q.self_member _ _).mp ((e.preserves _ _).mp (P.classify_spec x))

def refl (P : Partition) : PartitionIso P P where
  carrier := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  memberIndex := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  preserves := fun _ _ => Iff.rfl

def symm {P Q : Partition} (e : PartitionIso P Q) : PartitionIso Q P where
  carrier := ⟨e.carrier.invFun, e.carrier.toFun, e.carrier.right_inv, e.carrier.left_inv⟩
  memberIndex := ⟨e.memberIndex.invFun, e.memberIndex.toFun,
    e.memberIndex.right_inv, e.memberIndex.left_inv⟩
  preserves := by
    intro j y
    have h := e.preserves (e.memberIndex.invFun j) (e.carrier.invFun y)
    rw [e.memberIndex.right_inv, e.carrier.right_inv] at h
    exact h.symm

def trans {P Q R : Partition} (e : PartitionIso P Q)
    (f : PartitionIso Q R) : PartitionIso P R where
  carrier := {
    toFun := fun x => f.carrier.toFun (e.carrier.toFun x)
    invFun := fun z => e.carrier.invFun (f.carrier.invFun z)
    left_inv := by intro x; rw [f.carrier.left_inv, e.carrier.left_inv]
    right_inv := by intro z; rw [e.carrier.right_inv, f.carrier.right_inv]
  }
  memberIndex := {
    toFun := fun i => f.memberIndex.toFun (e.memberIndex.toFun i)
    invFun := fun k => e.memberIndex.invFun (f.memberIndex.invFun k)
    left_inv := by intro i; rw [f.memberIndex.left_inv, e.memberIndex.left_inv]
    right_inv := by intro k; rw [e.memberIndex.right_inv, f.memberIndex.right_inv]
  }
  preserves := fun i x => (e.preserves i x).trans (f.preserves _ _)

end PartitionIso

theorem partitionIso_preserves_member {P Q : Partition} (e : PartitionIso P Q)
    (i : P.MemberIndex) (x : P.Carrier) :
    P.member i x ↔ Q.member (e.memberIndex.toFun i) (e.carrier.toFun x) := e.preserves i x

structure Relabeling (P Q : Partition) where
  sameCarrier : P.Carrier = Q.Carrier
  memberIndex : Iso P.MemberIndex Q.MemberIndex
  preserves : ∀ i x, P.member i x ↔ Q.member (memberIndex.toFun i) (sameCarrier ▸ x)

theorem relabeling_preserves_member {P Q : Partition} (r : Relabeling P Q)
    (i : P.MemberIndex) (x : P.Carrier) :
    P.member i x ↔ Q.member (r.memberIndex.toFun i) (r.sameCarrier ▸ x) := r.preserves i x

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
abbrev tensor (P Q : SemanticPartition) : SemanticPartition where
  partition := P.partition.tensor Q.partition
  members := fun ij xy => P.members ij.1 xy.1 ∧ Q.members ij.2 xy.2
  hasMembers := by
    intro ⟨i, j⟩ ⟨x, y⟩
    rw [Partition.tensor_member_iff]
    exact and_congr (P.hasMembers i x) (Q.hasMembers j y)

def unit : SemanticPartition where
  partition := Partition.unit
  members := fun _ _ => True
  hasMembers := by intro i x; rfl

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
