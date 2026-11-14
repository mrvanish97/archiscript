-- EXPECT: Tactic `contradiction` failed
import ArchiScript.Partition
open ArchiScript
def impossibleMember : Subdomain Unit :=
  .root "empty" (fun _ => False) (by exact ⟨(), by contradiction⟩) (.predicate _)
