import ArchiScript.Partition

open ArchiScript

inductive Two where | left | right deriving DecidableEq

-- Expected failure: a single-value classifier cannot inhabit both members.
instance : MemberEnumeration Two where
  indices := [.left, .right]
  complete := by intro i; cases i <;> simp

def impossiblePartition : Partition where
  Carrier := Unit
  MemberIndex := Two
  carrierNonempty := ⟨()⟩
  memberIndexDecidableEq := inferInstance
  memberIndexFinite := ⟨[.left, .right], by intro i; cases i <;> simp⟩
  classify := fun _ => .left
  member_inhabited
    | .left => ⟨(), rfl⟩
    | .right => ⟨(), rfl⟩
