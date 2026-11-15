-- EXPECT: Tactic `rfl` failed
import ArchiScript.Partition
open ArchiScript
def trueOnly : VDP where
  Carrier := Bool
  MemberIndex := Unit
  memberIndexDecidableEq := inferInstance
  memberIndexFinite := ⟨[()], by intro u; cases u; simp⟩
  memberIndexNonempty := ⟨()⟩
  members := fun _ => Subdomain.root "True" (fun b => b = true) ⟨true, rfl⟩ (.predicate _)
  coverage := by intro b; exact ⟨(), by rfl⟩
  disjoint := by intro i j h; exact False.elim (h (Subsingleton.elim _ _))
