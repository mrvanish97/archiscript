import ArchiScript.Operation

namespace ArchiScript.Examples.PaymentWebhook
open ArchiScript

/-- The receipt decision depends on the event and a ledger observation. -/
structure Input where
  eventId : String
  status : String
  alreadyRecorded : Bool
  deriving Repr

inductive InputMember where
  | malformed | unsupported | failed | firstSuccess | duplicateSuccess
  deriving DecidableEq, Repr

def inputPartition : Partition where
  Carrier := Input
  MemberIndex := InputMember
  carrierNonempty := ⟨⟨"", "success", false⟩⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.malformed, .unsupported, .failed, .firstSuccess, .duplicateSuccess]
  memberIndices_complete := by intro i; cases i <;> simp
  classify x :=
    if x.eventId = "" then .malformed
    else if x.status = "success" then
      if x.alreadyRecorded then .duplicateSuccess else .firstSuccess
    else if x.status = "failed" then .failed
    else .unsupported
  member_inhabited
    | .malformed => ⟨⟨"", "success", false⟩, rfl⟩
    | .unsupported => ⟨⟨"p1", "pending", false⟩, rfl⟩
    | .failed => ⟨⟨"p1", "failed", false⟩, rfl⟩
    | .firstSuccess => ⟨⟨"p1", "success", false⟩, rfl⟩
    | .duplicateSuccess => ⟨⟨"p1", "success", true⟩, rfl⟩

/-- These meanings are stated separately from the classifier above. -/
def inputRegions : InputMember → Domain Input
  | .malformed => fun x => x.eventId = ""
  | .unsupported => fun x => x.eventId ≠ "" ∧ x.status ≠ "success" ∧ x.status ≠ "failed"
  | .failed => fun x => x.eventId ≠ "" ∧ x.status = "failed"
  | .firstSuccess => fun x => x.eventId ≠ "" ∧ x.status = "success" ∧ x.alreadyRecorded = false
  | .duplicateSuccess => fun x => x.eventId ≠ "" ∧ x.status = "success" ∧ x.alreadyRecorded = true

theorem inputPartition_realizes_regions : inputPartition.Realizes inputRegions := by
  intro i x
  cases i <;> cases x with
  | mk eventId status alreadyRecorded =>
    by_cases hId : eventId = "" <;>
    by_cases hSuccess : status = "success" <;>
    by_cases hFailed : status = "failed" <;>
    cases alreadyRecorded <;>
    simp [Partition.member, inputPartition, inputRegions, hId, hSuccess, hFailed] at *

inductive Decision where
  | reject | ignore | recordFailure | fulfill | acknowledgeDuplicate
  deriving DecidableEq, Repr

def decisionPartition : Partition where
  Carrier := Decision
  MemberIndex := Decision
  carrierNonempty := ⟨.reject⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.reject, .ignore, .recordFailure, .fulfill, .acknowledgeDuplicate]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/-- A member-level decision, not a value-level handler or a database write. -/
def decide : Operation inputPartition decisionPartition where
  run
    | .malformed => some .reject
    | .unsupported => some .ignore
    | .failed => some .recordFailure
    | .firstSuccess => some .fulfill
    | .duplicateSuccess => some .acknowledgeDuplicate

inductive LedgerCommand where
  | recordFailure | recordAndQueueFulfillment
  deriving DecidableEq, Repr

def ledgerCommandPartition : Partition where
  Carrier := LedgerCommand
  MemberIndex := LedgerCommand
  carrierNonempty := ⟨.recordFailure⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.recordFailure, .recordAndQueueFulfillment]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/-- `none` means there is no ledger-command mapping for this decision. -/
def requestLedgerCommand : Operation decisionPartition ledgerCommandPartition where
  run
    | .recordFailure => some .recordFailure
    | .fulfill => some .recordAndQueueFulfillment
    | .reject | .ignore | .acknowledgeDuplicate => none

theorem first_success_requests_fulfillment :
    (requestLedgerCommand.comp decide) .firstSuccess =
      some .recordAndQueueFulfillment := rfl

theorem duplicate_requests_no_ledger_command :
    (requestLedgerCommand.comp decide) .duplicateSuccess = none := rfl

theorem same_event_different_ledger_member :
    inputPartition.classify ⟨"p1", "success", false⟩ = .firstSuccess ∧
    inputPartition.classify ⟨"p1", "success", true⟩ = .duplicateSuccess := by
  constructor <;> rfl

end ArchiScript.Examples.PaymentWebhook
