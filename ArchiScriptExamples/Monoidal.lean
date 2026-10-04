import ArchiScript

namespace ArchiScriptExamples.Monoidal
open ArchiScript

/-- A small VDP with semantic members stated separately from its classifier. -/
def bit : Partition where
  Carrier := Bool
  MemberIndex := Bool
  carrierNonempty := ⟨false⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [false, true]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def bitMembers : Bool → Domain Bool
  | false => fun x => x = false
  | true => fun x => x = true

def semanticBit : SemanticPartition where
  partition := bit
  members := bitMembers
  hasMembers := by
    intro i x
    cases i <;> cases x <;>
      simp [Partition.member, bit, bitMembers]

/-- Four full product members, including both off-diagonal combinations. -/
def pair := semanticBit.tensor semanticBit

example (i j x y : Bool) :
    pair.members (i, j) (x, y) ↔ bitMembers i x ∧ bitMembers j y := Iff.rfl

#guard (bit.tensor bit).memberIndices.length == 4
#guard (bit.tensor bit).classify (false, true) == (false, true)
#guard (bit.tensor bit).classify (true, false) == (true, false)

/-- One operation can have two branches without introducing concurrency. -/
def flip : Operation bit bit := ⟨fun i => some (!i)⟩
def keepTrue : Operation bit bit := ⟨fun | false => none | true => some true⟩

/-- These two separately declared arrows have independent source slots. Their
joint operation is algebraic aggregation; runtime concurrency is unknown. -/
def independent := flip.tensor keepTrue

#guard independent (false, true) == some (true, true)
#guard independent (false, false) == none

example : (Operation.id bit).tensor (Operation.id bit) = Operation.id (bit.tensor bit) :=
  Operation.tensor_id bit bit

example : (flip.comp keepTrue).tensor (keepTrue.comp flip) =
    (flip.tensor keepTrue).comp (keepTrue.tensor flip) :=
  Operation.tensor_comp keepTrue flip flip keepTrue

example : (Operation.associatorInv bit bit bit).comp
    (Operation.associator bit bit bit) = Operation.id ((bit.tensor bit).tensor bit) :=
  Operation.associator_left_inv bit bit bit

-- Account(A) ⊗ Payment(B) is valid mathematics. A reviewer must establish why
-- those independently classified factors are considered together. The tensor
-- construction itself does not assert an account/payment relationship.

end ArchiScriptExamples.Monoidal
