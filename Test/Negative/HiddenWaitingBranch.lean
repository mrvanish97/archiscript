-- EXPECT: Tactic `rfl` failed
-- ONLY_ERROR: Tactic `rfl` failed
import ArchiScript.Operation

namespace HiddenWaitingBranch
open ArchiScript

-- One coarse Waiting member and two genuinely different output members.
abbrev waiting : VDP := Partition.unit
abbrev result : VDP := Partition.closed Bool "Result"
  ⟨[false, true], by intro b; cases b <;> simp⟩ ⟨false⟩

def decide : Operation waiting result := ⟨fun _ => some true⟩

def successBranch : Operation.Branch decide where
  source := ()
  target := true
  belongs := rfl

-- This attempts a second output from the SAME Operation and source member.
-- Two separately declared outgoing Operations would not be this error.
def timeoutBranch : Operation.Branch decide where
  source := ()
  target := false
  belongs := by rfl

end HiddenWaitingBranch
