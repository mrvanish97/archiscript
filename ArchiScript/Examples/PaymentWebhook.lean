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

/-- Human descriptions live beside their predicates; the descriptions are review text. -/
structure InputRegion where
  predicate : Domain Input
  description : String

/-- These meanings are stated separately from the classifier above. -/
def inputRegion : InputMember → InputRegion
  | .malformed => ⟨fun x => x.eventId = "", "eventId is empty, regardless of status or ledger observation"⟩
  | .unsupported => ⟨fun x => x.eventId ≠ "" ∧ x.status ≠ "success" ∧ x.status ≠ "failed",
      "eventId is present; status is neither success nor failed"⟩
  | .failed => ⟨fun x => x.eventId ≠ "" ∧ x.status = "failed",
      "eventId is present; status is failed"⟩
  | .firstSuccess => ⟨fun x => x.eventId ≠ "" ∧ x.status = "success" ∧ x.alreadyRecorded = false,
      "eventId is present; status is success; ledger observation is false"⟩
  | .duplicateSuccess => ⟨fun x => x.eventId ≠ "" ∧ x.status = "success" ∧ x.alreadyRecorded = true,
      "eventId is present; status is success; ledger observation is true"⟩

def inputRegions (member : InputMember) : Domain Input := (inputRegion member).predicate

theorem inputPartition_realizes_regions : inputPartition.Realizes inputRegions := by
  intro i x
  cases i <;> cases x with
  | mk eventId status alreadyRecorded =>
    by_cases hId : eventId = "" <;>
    by_cases hSuccess : status = "success" <;>
    by_cases hFailed : status = "failed" <;>
    cases alreadyRecorded <;>
    simp [Partition.member, inputPartition, inputRegions, inputRegion,
      hId, hSuccess, hFailed] at *

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

inductive OperationName where
  | decide | requestLedgerCommand
  deriving DecidableEq, Repr

inductive DecideBranch where
  | malformed | unsupported | failed | firstSuccess | duplicateSuccess
  deriving DecidableEq, Repr

inductive LedgerBranch where
  | recordFailure | fulfill
  deriving DecidableEq, Repr

private def code (symbol : String) : Operation.SourceRef :=
  { repository := "archiscript", path := "examples/payment-webhook.mjs", symbol := some symbol }

def decideDeclaration : Operation.Declaration where
  source := inputPartition
  target := decisionPartition
  operation := decide
  BranchName := DecideBranch
  branchNameDecidableEq := inferInstance
  branchNames := [.malformed, .unsupported, .failed, .firstSuccess, .duplicateSuccess]
  branchNames_complete := by intro name; cases name <;> simp
  branchNames_nodup := by decide
  branch
    | .malformed => ⟨.malformed, .reject, rfl⟩
    | .unsupported => ⟨.unsupported, .ignore, rfl⟩
    | .failed => ⟨.failed, .recordFailure, rfl⟩
    | .firstSuccess => ⟨.firstSuccess, .fulfill, rfl⟩
    | .duplicateSuccess => ⟨.duplicateSuccess, .acknowledgeDuplicate, rfl⟩
  responsibilityOwners := ["payments-webhooks"]
  implementation := some (.resolved {
    primary := code "decide"
    supporting := [code "handleWebhook"]
    evidence := [{ kind := .test, reference := "all declared input members map to their checked decisions" }]
  })
  branchImplementation
    | .firstSuccess => some (.resolved {
        primary := code "decide"
        supporting := [code "handleWebhook"]
        evidence := [{ kind := .test, reference := "first success records payment and enqueues fulfillment" }]
      })
    | .duplicateSuccess => some (.resolved {
        primary := code "decide"
        supporting := [code "handleWebhook"]
        evidence := [{ kind := .test, reference := "duplicate success acknowledges without ledger or queue effects" }]
      })
    | _ => none

def ledgerDeclaration : Operation.Declaration where
  source := decisionPartition
  target := ledgerCommandPartition
  operation := requestLedgerCommand
  BranchName := LedgerBranch
  branchNameDecidableEq := inferInstance
  branchNames := [.recordFailure, .fulfill]
  branchNames_complete := by intro name; cases name <;> simp
  branchNames_nodup := by decide
  branch
    | .recordFailure => ⟨.recordFailure, .recordFailure, rfl⟩
    | .fulfill => ⟨.fulfill, .recordAndQueueFulfillment, rfl⟩
  responsibilityOwners := ["payments-ledger"]
  implementation := some (.resolved {
    primary := code "requestLedgerCommand"
    supporting := [code "handleWebhook"]
    evidence := [{ kind := .test, reference := "first success records payment and enqueues fulfillment" }]
  })

def operationRegistry : Operation.Registry where
  OperationName := OperationName
  operationNameDecidableEq := inferInstance
  operationNames := [.decide, .requestLedgerCommand]
  operationNames_complete := by intro name; cases name <;> simp
  operationNames_nodup := by decide
  resolve
    | .decide => decideDeclaration
    | .requestLedgerCommand => ledgerDeclaration

def duplicateSuccessBranch : Operation.BranchAddress operationRegistry :=
  ⟨.decide, .duplicateSuccess⟩

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
