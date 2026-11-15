import ArchiScriptExamples.ProofSupport
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

instance : MemberEnumeration BrowserMember where
  indices := [.root, .otherPath]
  complete := by intro i; cases i <;> simp

def browserPartitionRegions : BrowserMember → Domain BrowserCall
  | .root => fun x => x.path = "/"
  | .otherPath => fun x => x.path ≠ "/"

def browserPartitionLookup (call : BrowserCall) : BrowserMember := if call.path = "/" then .root else .otherPath

theorem browserPartitionLookup_correct : ∀ i x, browserPartitionLookup x = i ↔ browserPartitionRegions i x := by
  intro i x
  cases i <;> by_cases h : x.path = "/" <;> simp [browserPartitionLookup, browserPartitionRegions, h]

theorem browserPartitionLookup_inhabited : ∀ i : BrowserMember, ∃ x : BrowserCall, browserPartitionLookup x = i := fun
    | .root => ⟨⟨"/"⟩, by simp [browserPartitionLookup]⟩
    | .otherPath => ⟨⟨"/health"⟩, by simp [browserPartitionLookup]⟩

abbrev browserPartition : Partition :=
  partitionOfRegions BrowserCall BrowserMember "browserPartition" browserPartitionRegions
    (⟨[.root, .otherPath], by intro i; cases i <;> simp⟩) browserPartitionLookup browserPartitionLookup_correct
    (by
      intro i
      obtain ⟨x, hx⟩ := browserPartitionLookup_inhabited i
      exact ⟨x, (browserPartitionLookup_correct i x).mp hx⟩)
    ⟨.root⟩

instance : MemberEnumeration CliMember where
  indices := [.empty, .nonempty]
  complete := by intro i; cases i <;> simp

def cliPartitionRegions : CliMember → Domain CliInvocation
  | .empty => fun x => x.args = []
  | .nonempty => fun x => x.args ≠ []

def cliPartitionLookup (invocation : CliInvocation) : CliMember := if invocation.args = [] then .empty else .nonempty

theorem cliPartitionLookup_correct : ∀ i x, cliPartitionLookup x = i ↔ cliPartitionRegions i x := by
  intro i x
  cases i <;> by_cases h : x.args = [] <;> simp [cliPartitionLookup, cliPartitionRegions, h]

theorem cliPartitionLookup_inhabited : ∀ i : CliMember, ∃ x : CliInvocation, cliPartitionLookup x = i := fun
    | .empty => ⟨⟨[]⟩, by simp [cliPartitionLookup]⟩
    | .nonempty => ⟨⟨["status"]⟩, by simp [cliPartitionLookup]⟩

abbrev cliPartition : Partition :=
  partitionOfRegions CliInvocation CliMember "cliPartition" cliPartitionRegions
    (⟨[.empty, .nonempty], by intro i; cases i <;> simp⟩) cliPartitionLookup cliPartitionLookup_correct
    (by
      intro i
      obtain ⟨x, hx⟩ := cliPartitionLookup_inhabited i
      exact ⟨x, (cliPartitionLookup_correct i x).mp hx⟩)
    ⟨.empty⟩

instance : MemberEnumeration EntryDisposition where
  indices := [.accept, .reject]
  complete := by intro i; cases i <;> simp

abbrev dispositionPartition : Partition :=
  Partition.closed EntryDisposition "EntryDisposition"
    (⟨[.accept, .reject], by intro i; cases i <;> simp⟩) (⟨.accept⟩)

/--
The dispatcher input is a lossless structural OR of two already established
architectural entry channels.
-/
abbrev entryPartition : Partition :=
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