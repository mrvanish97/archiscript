import ArchiScript.Operation

namespace ArchiScript

namespace Partition

/--
The categorical coproduct of two VDPs. The carrier is a tagged sum and the
member family preserves the tag and the original member identity.

This construction is exhaustive only relative to the sum carrier. It is not
evidence that the two summands exhaust an independently supplied external
boundary.
-/
def coprod (P Q : Partition) : Partition where
  Carrier := Sum P.Carrier Q.Carrier
  MemberIndex := Sum P.MemberIndex Q.MemberIndex
  carrierNonempty := ⟨Sum.inl (Classical.choice P.carrierNonempty)⟩
  memberIndexDecidableEq := inferInstance
  memberIndices :=
    P.memberIndices.map Sum.inl ++ Q.memberIndices.map Sum.inr
  memberIndices_complete := by
    intro i
    cases i with
    | inl i =>
      simp only [List.mem_append, List.mem_map]
      exact Or.inl ⟨i, P.memberIndices_complete i, rfl⟩
    | inr j =>
      simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨j, Q.memberIndices_complete j, rfl⟩
  classify
    | .inl x => .inl (P.classify x)
    | .inr y => .inr (Q.classify y)
  member_inhabited
    | .inl i =>
      let ⟨x, hx⟩ := P.member_inhabited i
      ⟨.inl x, congrArg Sum.inl hx⟩
    | .inr j =>
      let ⟨y, hy⟩ := Q.member_inhabited j
      ⟨.inr y, congrArg Sum.inr hy⟩

@[simp] theorem coprod_classify_inl (P Q : Partition) (x : P.Carrier) :
    (P.coprod Q).classify (.inl x) = .inl (P.classify x) := rfl

@[simp] theorem coprod_classify_inr (P Q : Partition) (y : Q.Carrier) :
    (P.coprod Q).classify (.inr y) = .inr (Q.classify y) := rfl

end Partition

namespace SemanticPartition

/-- Semantic meanings lift losslessly through a tagged coproduct. -/
def coprod (P Q : SemanticPartition) : SemanticPartition where
  partition := P.partition.coprod Q.partition
  members
    | .inl i, .inl x => P.members i x
    | .inl _, .inr _ => False
    | .inr _, .inl _ => False
    | .inr j, .inr y => Q.members j y
  hasMembers := by
    intro ij xy
    cases ij with
    | inl i =>
      cases xy with
      | inl x =>
        exact P.hasMembers i x
      | inr y =>
        simp [Partition.member, Partition.coprod]
    | inr j =>
      cases xy with
      | inl x =>
        simp [Partition.member, Partition.coprod]
      | inr y =>
        exact Q.hasMembers j y

end SemanticPartition

namespace Operation

/-- Canonical left coproduct injection. -/
def coprodInl (P Q : Partition) : Operation P (P.coprod Q) :=
  ⟨fun i => some (.inl i)⟩

/-- Canonical right coproduct injection. -/
def coprodInr (P Q : Partition) : Operation Q (P.coprod Q) :=
  ⟨fun j => some (.inr j)⟩

/--
Copairing of two partial member maps. This is the mediating morphism in the
coproduct universal property.
-/
def copair {P Q R : Partition} (f : Operation P R) (g : Operation Q R) :
    Operation (P.coprod Q) R :=
  ⟨fun
    | .inl i => f i
    | .inr j => g j⟩

@[simp] theorem copair_inl {P Q R : Partition} (f : Operation P R) (g : Operation Q R) :
    (copair f g).comp (coprodInl P Q) = f := by
  ext i
  rfl

@[simp] theorem copair_inr {P Q R : Partition} (f : Operation P R) (g : Operation Q R) :
    (copair f g).comp (coprodInr P Q) = g := by
  ext j
  rfl

/-- The coproduct mediating operation is unique. -/
theorem copair_unique {P Q R : Partition}
    (f : Operation P R) (g : Operation Q R)
    (h : Operation (P.coprod Q) R)
    (left : h.comp (coprodInl P Q) = f)
    (right : h.comp (coprodInr P Q) = g) :
    h = copair f g := by
  ext ij
  cases ij with
  | inl i =>
    have hi := congrArg (fun op : Operation P R => op i) left
    simpa [comp, coprodInl, copair] using hi
  | inr j =>
    have hj := congrArg (fun op : Operation Q R => op j) right
    simpa [comp, coprodInr, copair] using hj

/-- Map two independent partial operations over the tagged alternatives. -/
def coprodMap
    {P P' Q Q' : Partition}
    (f : Operation P P') (g : Operation Q Q') :
    Operation (P.coprod Q) (P'.coprod Q') :=
  ⟨fun
    | .inl i => (f i).map Sum.inl
    | .inr j => (g j).map Sum.inr⟩

@[simp] theorem coprodMap_id (P Q : Partition) :
    coprodMap (id P) (id Q) = id (P.coprod Q) := by
  ext ij
  cases ij <;> rfl

theorem coprodMap_comp
    {P P' P'' Q Q' Q'' : Partition}
    (f₁ : Operation P P') (f₂ : Operation P' P'')
    (g₁ : Operation Q Q') (g₂ : Operation Q' Q'') :
    coprodMap (f₂.comp f₁) (g₂.comp g₁) =
      (coprodMap f₂ g₂).comp (coprodMap f₁ g₁) := by
  ext ij
  cases ij with
  | inl i =>
    cases h₁ : f₁ i <;> simp [coprodMap, comp, h₁, Option.bind]
  | inr j =>
    cases h₁ : g₁ j <;> simp [coprodMap, comp, h₁, Option.bind]

end Operation

end ArchiScript
