-- EXPECT: Fields missing: `coverage`
import ArchiScriptExamples.SimpleCone
open ArchiScript ArchiScriptExamples.SimpleCone
def unfinished : VDP where
  Carrier := Bool
  MemberIndex := Bool
  memberIndexDecidableEq := inferInstance
  memberIndexFinite := ⟨[false, true], by intro b; cases b <;> simp⟩
  memberIndexNonempty := ⟨false⟩
  members := bit.members
  disjoint := bit.disjoint
