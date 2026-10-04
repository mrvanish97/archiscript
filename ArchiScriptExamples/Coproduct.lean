import ArchiScript.Coproduct

namespace ArchiScriptExamples.Coproduct
open ArchiScript

/--
Coproduct is used here because the architecture has two design-time entry
channels with different carriers: browser calls and CLI invocations. The
software topology declares that the dispatcher has exactly these two input
channels. The coproduct does not classify runtime-discovered alternatives
inside either channel.
-/
structure BrowserCall where
  path : String
  deriving DecidableEq

structure CliInvocation where
  args : List String
  deriving DecidableEq

inductive BrowserMember where
  | root
  | otherPath
  deriving DecidableEq

inductive CliMember where
  | empty
  | nonempty
  deriving DecidableEq

inductive EntryDisposition where
  | accept
  | reject
  deriving DecidableEq

def browserPartition : Partition where
  Carrier := BrowserCall
  MemberIndex := BrowserMember
  carrierNonempty := ⟨⟨"/"⟩⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.root, .otherPath]
  memberIndices_complete := by intro i; cases i <;> simp
  classify call := if call.path = "/" then .root else .otherPath
  member_inhabited
    | .root => ⟨⟨"/"⟩, by simp⟩
    | .otherPath => ⟨⟨"/health"⟩, by simp⟩

def cliPartition : Partition where
  Carrier := CliInvocation
  MemberIndex := CliMember
  carrierNonempty := ⟨⟨[]⟩⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.empty, .nonempty]
  memberIndices_complete := by intro i; cases i <;> simp
  classify invocation := if invocation.args = [] then .empty else .nonempty
  member_inhabited
    | .empty => ⟨⟨[]⟩, by simp⟩
    | .nonempty => ⟨⟨["status"]⟩, by simp⟩

def dispositionPartition : Partition where
  Carrier := EntryDisposition
  MemberIndex := EntryDisposition
  carrierNonempty := ⟨.accept⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.accept, .reject]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/--
The dispatcher input is a lossless structural OR of two already established
architectural entry channels.
-/
def entryPartition : Partition :=
  browserPartition.coproduct cliPartition

def handleBrowser : Operation browserPartition dispositionPartition where
  run
    | .root => some .accept
    | .otherPath => some .reject

def handleCli : Operation cliPartition dispositionPartition where
  run
    | .empty => some .reject
    | .nonempty => some .accept

def handleEntry : Operation entryPartition dispositionPartition :=
  Operation.copair handleBrowser handleCli

end ArchiScriptExamples.Coproduct