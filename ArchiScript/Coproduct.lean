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
def coproduct (P Q : Partition) : Partition where
  Carrier := Sum P.Carrier Q.Carrier
  MemberIndex := Sum P.MemberIndex Q.MemberIndex
  carrierNonempty := ⟨Sum.inl (Classical.choice P.carrierNonempty)⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := P.memberIndices.map Sum.inl ++ Q.memberIndices.map Sum.inr
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
  member_inhabited := by
    intro ij
    cases ij with
    | inl i =>
      rcases P.member_inhabited i with ⟨x, hx⟩
      exact ⟨.inl x, congrArg Sum.inl hx⟩
    | inr j =>
      rcases Q.member_inhabited j with ⟨y, hy⟩
      exact ⟨.inr y, congrArg Sum.inr hy⟩

@[simp] theorem coproduct_classify_inl (P Q : Partition) (x : P.Carrier) :
    (P.coproduct Q).classify (.inl x) = .inl (P.classify x) := rfl

@[simp] theorem coproduct_classify_inr (P Q : Partition) (y : Q.Carrier) :
    (P.coproduct Q).classify (.inr y) = .inr (Q.classify y) := rfl

@[simp] theorem coproduct_member_inl_iff (P Q : Partition)
    (i : P.MemberIndex) (x : P.Carrier) :
    (P.coproduct Q).member (.inl i) (.inl x) ↔ P.member i x := by
  simp [member, coproduct]

@[simp] theorem coproduct_member_inr_iff (P Q : Partition)
    (j : Q.MemberIndex) (y : Q.Carrier) :
    (P.coproduct Q).member (.inr j) (.inr y) ↔ Q.member j y := by
  simp [member, coproduct]

end Partition

namespace SemanticPartition

/-- Semantic meanings lift losslessly through a tagged coproduct. -/
def coproduct (P Q : SemanticPartition) : SemanticPartition where
  partition := P.partition.coproduct Q.partition
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
        simpa [Partition.member, Partition.coproduct] using P.hasMembers i x
      | inr y =>
        simp [Partition.member, Partition.coproduct]
    | inr j =>
      cases xy with
      | inl x =>
        simp [Partition.member, Partition.coproduct]
      | inr y =>
        simpa [Partition.member, Partition.coproduct] using Q.hasMembers j y

end SemanticPartition

namespace Operation

/-- Canonical left coproduct injection. -/
def coproductInl (P Q : Partition) : Operation P (P.coproduct Q) :=
  ⟨fun i => some (.inl i)⟩

/-- Canonical right coproduct injection. -/
def coproductInr (P Q : Partition) : Operation Q (P.coproduct Q) :=
  ⟨fun j => some (.inr j)⟩

/--
Copairing of two partial member maps. This is the mediating morphism in the
coproduct universal property.
-/
def copair {P Q R : Partition} (f : Operation P R) (g : Operation Q R) :
    Operation (P.coproduct Q) R :=
  ⟨fun
    | .inl i => f i
    | .inr j => g j⟩

@[simp] theorem copair_inl {P Q R : Partition} (f : Operation P R) (g : Operation Q R) :
    (copair f g).comp (coproductInl P Q) = f := by
  ext i
  rfl

@[simp] theorem copair_inr {P Q R : Partition} (f : Operation P R) (g : Operation Q R) :
    (copair f g).comp (coproductInr P Q) = g := by
  ext j
  rfl

/-- The coproduct mediating operation is unique. -/
theorem copair_unique {P Q R : Partition}
    (f : Operation P R) (g : Operation Q R)
    (h : Operation (P.coproduct Q) R)
    (left : h.comp (coproductInl P Q) = f)
    (right : h.comp (coproductInr P Q) = g) :
    h = copair f g := by
  apply Operation.ext
  intro ij
  cases ij with
  | inl i =>
    have hi := congrArg (fun op : Operation P R => op i) left
    change h (.inl i) = f i at hi
    exact hi
  | inr j =>
    have hj := congrArg (fun op : Operation Q R => op j) right
    change h (.inr j) = g j at hj
    exact hj

/-- Map two partial operations over tagged alternatives. -/
def coproductMap
    {P P' Q Q' : Partition}
    (f : Operation P P') (g : Operation Q Q') :
    Operation (P.coproduct Q) (P'.coproduct Q') :=
  ⟨fun
    | .inl i => (f i).map Sum.inl
    | .inr j => (g j).map Sum.inr⟩

@[simp] theorem coproductMap_id (P Q : Partition) :
    coproductMap (id P) (id Q) = id (P.coproduct Q) := by
  ext ij
  cases ij <;> rfl

theorem coproductMap_comp
    {P P' P'' Q Q' Q'' : Partition}
    (f₁ : Operation P P') (f₂ : Operation P' P'')
    (g₁ : Operation Q Q') (g₂ : Operation Q' Q'') :
    coproductMap (f₂.comp f₁) (g₂.comp g₁) =
      (coproductMap f₂ g₂).comp (coproductMap f₁ g₁) := by
  apply Operation.ext
  intro ij
  cases ij with
  | inl i =>
    simp only [coproductMap, comp_apply]
    cases h₁ : f₁ i <;> rfl
  | inr j =>
    simp only [coproductMap, comp_apply]
    cases h₁ : g₁ j <;> rfl

end Operation

end ArchiScript