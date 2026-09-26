import ArchiScript.Partition

open ArchiScript

inductive Two where | left | right deriving DecidableEq

-- Expected failure: a single-value classifier cannot inhabit both members.
def impossiblePartition : Partition where
  Carrier := Unit
  MemberIndex := Two
  carrierNonempty := ⟨()⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.left, .right]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := fun _ => .left
  member_inhabited
    | .left => ⟨(), rfl⟩
    | .right => ⟨(), rfl⟩
