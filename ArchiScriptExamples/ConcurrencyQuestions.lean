import ArchiScript

/-!
Topology examples that should trigger concurrency review questions without
overclaiming runtime concurrency semantics.

The key distinction is between:
* alternative members of one Operation (not independent arrows), and
* distinct operations whose sources exist independently.

A fan-in from independent sources is a review boundary. A cycle is a sequential
feedback path. Neither shape alone proves a race or deadlock.
-/
namespace ArchiScriptExamples.ConcurrencyQuestions
open ArchiScript

inductive ManualTrigger where
  | reconcile
  | force
  deriving DecidableEq, Repr

def manualTriggerPartition : Partition where
  Carrier := ManualTrigger
  MemberIndex := ManualTrigger
  carrierNonempty := ⟨.reconcile⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.reconcile, .force]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def manualTriggerSemantic : SemanticPartition where
  partition := manualTriggerPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

inductive TimerTrigger where
  | due
  deriving DecidableEq, Repr

def timerTriggerPartition : Partition where
  Carrier := TimerTrigger
  MemberIndex := TimerTrigger
  carrierNonempty := ⟨.due⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.due]
  memberIndices_complete := by intro i; cases i; simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def timerTriggerSemantic : SemanticPartition where
  partition := timerTriggerPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

/-- Optional product view showing that the trigger classifications are
independent semantic slots. This does not claim simultaneous runtime arrival. -/
def independentTriggerSpace : SemanticPartition :=
  manualTriggerSemantic.tensor timerTriggerSemantic

inductive ReconcileMode where
  | normal
  | forced
  deriving DecidableEq, Repr

def reconcileModePartition : Partition where
  Carrier := ReconcileMode
  MemberIndex := ReconcileMode
  carrierNonempty := ⟨.normal⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.normal, .forced]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def reconcileModeSemantic : SemanticPartition where
  partition := reconcileModePartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

/-- First independent source into the common reconcile VDP. -/
def fromManual : Operation manualTriggerPartition reconcileModePartition where
  run
    | .reconcile => some .normal
    | .force => some .forced

/-- Second independent source into the same reconcile VDP. -/
def fromTimer : Operation timerTriggerPartition reconcileModePartition where
  run
    | .due => some .normal

inductive ReconcileNext where
  | stable
  | retry
  deriving DecidableEq, Repr

def reconcileNextPartition : Partition where
  Carrier := ReconcileNext
  MemberIndex := ReconcileNext
  carrierNonempty := ⟨.stable⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.stable, .retry]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def reconcileNextSemantic : SemanticPartition where
  partition := reconcileNextPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

/-- Ordinary sequential transition inside the reconcile loop. -/
def evaluateReconcile :
    Operation reconcileModePartition reconcileNextPartition where
  run
    | .normal => some .retry
    | .forced => some .stable

/-- Partial feedback edge. The cycle is a retry loop, not a concurrency proof. -/
def retry :
    Operation reconcileNextPartition reconcileModePartition where
  run
    | .stable => none
    | .retry => some .normal

private def manualArchitecture : ArchitecturalPartition where
  partition := manualTriggerPartition
  carrierOrigin := .architecturalDomain
    "ConcurrencyQuestions.ManualTrigger" (by decide)
  selectedMembers := fun i => {
    meaning := fun x => x = i
    definition := .predicate (fun x => x = i)
  }
  hasMembers := by intro i x; rfl

private def timerArchitecture : ArchitecturalPartition where
  partition := timerTriggerPartition
  carrierOrigin := .architecturalDomain
    "ConcurrencyQuestions.TimerTrigger" (by decide)
  selectedMembers := fun i => {
    meaning := fun x => x = i
    definition := .predicate (fun x => x = i)
  }
  hasMembers := by intro i x; rfl

private def modeArchitecture : ArchitecturalPartition where
  partition := reconcileModePartition
  carrierOrigin := .architecturalDomain
    "ConcurrencyQuestions.ReconcileMode" (by decide)
  selectedMembers := fun i => {
    meaning := fun x => x = i
    definition := .predicate (fun x => x = i)
  }
  hasMembers := by intro i x; rfl

private def nextArchitecture : ArchitecturalPartition where
  partition := reconcileNextPartition
  carrierOrigin := .architecturalDomain
    "ConcurrencyQuestions.ReconcileNext" (by decide)
  selectedMembers := fun i => {
    meaning := fun x => x = i
    definition := .predicate (fun x => x = i)
  }
  hasMembers := by intro i x; rfl

/-- This Architecture intentionally contains both independent fan-in and a cycle. -/
def architecture : Architecture where
  operations := [
    ⟨manualArchitecture, modeArchitecture, fromManual⟩,
    ⟨timerArchitecture, modeArchitecture, fromTimer⟩,
    ⟨modeArchitecture, nextArchitecture, evaluateReconcile⟩,
    ⟨nextArchitecture, modeArchitecture, retry⟩
  ]

#guard independentTriggerSpace.partition.memberIndices.length == 2
#guard fromManual .reconcile == some .normal
#guard fromManual .force == some .forced
#guard fromTimer .due == some .normal
#guard evaluateReconcile .normal == some .retry
#guard retry .retry == some .normal
#guard retry .stable == none
#guard architecture.operations.length == 4

end ArchiScriptExamples.ConcurrencyQuestions
