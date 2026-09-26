import ArchiScript.Examples.PaymentWebhook

namespace ArchiScript.Examples.PaymentWebhookNetwork
open ArchiScript

/-- The response obligation to the provider, not an HTTP write. -/
inductive ProviderResponse where
  | rejectRequest | acknowledge
  deriving DecidableEq, Repr

def responsePartition : Partition where
  Carrier := ProviderResponse
  MemberIndex := ProviderResponse
  carrierNonempty := ⟨.acknowledge⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.rejectRequest, .acknowledge]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/-- Audit categories are intent to record, not evidence that a record exists. -/
inductive AuditIntent where
  | invalidDelivery | unsupportedDelivery | paymentFailed
  | firstSuccess | duplicateSuccess
  deriving DecidableEq, Repr

def auditPartition : Partition where
  Carrier := AuditIntent
  MemberIndex := AuditIntent
  carrierNonempty := ⟨.invalidDelivery⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.invalidDelivery, .unsupportedDelivery, .paymentFailed,
                    .firstSuccess, .duplicateSuccess]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/-- A possible customer notification, not proof that a message was sent. -/
inductive NotificationIntent where
  | paymentFailure | successReceipt
  deriving DecidableEq, Repr

def notificationPartition : Partition where
  Carrier := NotificationIntent
  MemberIndex := NotificationIntent
  carrierNonempty := ⟨.paymentFailure⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.paymentFailure, .successReceipt]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/-- The fulfillment boundary has one request kind in this scoped example. -/
inductive FulfillmentRequest where
  | enqueue
  deriving DecidableEq, Repr

def fulfillmentPartition : Partition where
  Carrier := FulfillmentRequest
  MemberIndex := FulfillmentRequest
  carrierNonempty := ⟨.enqueue⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.enqueue]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/-- Every decision has a provider response plan. -/
def planResponse : Operation PaymentWebhook.decisionPartition responsePartition where
  run
    | .reject => some .rejectRequest
    | .ignore | .recordFailure | .fulfill | .acknowledgeDuplicate => some .acknowledge

/-- Every decision carries a distinct audit intent. -/
def planAudit : Operation PaymentWebhook.decisionPartition auditPartition where
  run
    | .reject => some .invalidDelivery
    | .ignore => some .unsupportedDelivery
    | .recordFailure => some .paymentFailed
    | .fulfill => some .firstSuccess
    | .acknowledgeDuplicate => some .duplicateSuccess

/-- Only selected outcomes request customer notification. -/
def planNotification : Operation PaymentWebhook.decisionPartition notificationPartition where
  run
    | .recordFailure => some .paymentFailure
    | .fulfill => some .successReceipt
    | .reject | .ignore | .acknowledgeDuplicate => none

/-- Only the success command requests fulfillment. This does not execute the command. -/
def planFulfillment : Operation PaymentWebhook.ledgerCommandPartition fulfillmentPartition where
  run
    | .recordAndQueueFulfillment => some .enqueue
    | .recordFailure => none

private def plannedCode (symbol : String) : Operation.ImplementationDisposition :=
  .planned { primary := {
    repository := "archiscript"
    path := "examples/payment-webhook-network.mjs"
    symbol := some symbol
  } }

def responseDeclaration : Operation.Declaration where
  source := PaymentWebhook.decisionPartition
  target := responsePartition
  operation := planResponse
  BranchName := PaymentWebhook.Decision
  branchNameDecidableEq := inferInstance
  branchNames := [.reject, .ignore, .recordFailure, .fulfill, .acknowledgeDuplicate]
  branchNames_complete := by intro i; cases i <;> simp
  branchNames_nodup := by decide
  branch
    | .reject => ⟨.reject, .rejectRequest, rfl⟩
    | .ignore => ⟨.ignore, .acknowledge, rfl⟩
    | .recordFailure => ⟨.recordFailure, .acknowledge, rfl⟩
    | .fulfill => ⟨.fulfill, .acknowledge, rfl⟩
    | .acknowledgeDuplicate => ⟨.acknowledgeDuplicate, .acknowledge, rfl⟩
  responsibilityOwners := ["payments-api"]
  implementation := some (plannedCode "planResponse")

def auditDeclaration : Operation.Declaration where
  source := PaymentWebhook.decisionPartition
  target := auditPartition
  operation := planAudit
  BranchName := PaymentWebhook.Decision
  branchNameDecidableEq := inferInstance
  branchNames := [.reject, .ignore, .recordFailure, .fulfill, .acknowledgeDuplicate]
  branchNames_complete := by intro i; cases i <;> simp
  branchNames_nodup := by decide
  branch
    | .reject => ⟨.reject, .invalidDelivery, rfl⟩
    | .ignore => ⟨.ignore, .unsupportedDelivery, rfl⟩
    | .recordFailure => ⟨.recordFailure, .paymentFailed, rfl⟩
    | .fulfill => ⟨.fulfill, .firstSuccess, rfl⟩
    | .acknowledgeDuplicate => ⟨.acknowledgeDuplicate, .duplicateSuccess, rfl⟩
  responsibilityOwners := ["payments-audit"]
  implementation := some (plannedCode "planAudit")

inductive NotificationBranch where
  | recordFailure | fulfill
  deriving DecidableEq, Repr

def notificationDeclaration : Operation.Declaration where
  source := PaymentWebhook.decisionPartition
  target := notificationPartition
  operation := planNotification
  BranchName := NotificationBranch
  branchNameDecidableEq := inferInstance
  branchNames := [.recordFailure, .fulfill]
  branchNames_complete := by intro i; cases i <;> simp
  branchNames_nodup := by decide
  branch
    | .recordFailure => ⟨.recordFailure, .paymentFailure, rfl⟩
    | .fulfill => ⟨.fulfill, .successReceipt, rfl⟩
  responsibilityOwners := ["customer-notifications"]
  implementation := some (plannedCode "planNotification")

inductive FulfillmentBranch where
  | recordAndQueueFulfillment
  deriving DecidableEq, Repr

def fulfillmentDeclaration : Operation.Declaration where
  source := PaymentWebhook.ledgerCommandPartition
  target := fulfillmentPartition
  operation := planFulfillment
  BranchName := FulfillmentBranch
  branchNameDecidableEq := inferInstance
  branchNames := [.recordAndQueueFulfillment]
  branchNames_complete := by intro i; cases i <;> simp
  branchNames_nodup := by decide
  branch
    | .recordAndQueueFulfillment => ⟨.recordAndQueueFulfillment, .enqueue, rfl⟩
  responsibilityOwners := ["fulfillment"]
  implementation := some (plannedCode "planFulfillment")

inductive OperationName where
  | decide | requestLedgerCommand | planResponse | planAudit
  | planNotification | planFulfillment
  deriving DecidableEq, Repr

def operationRegistry : Operation.Registry where
  OperationName := OperationName
  operationNameDecidableEq := inferInstance
  operationNames := [.decide, .requestLedgerCommand, .planResponse,
                     .planAudit, .planNotification, .planFulfillment]
  operationNames_complete := by intro i; cases i <;> simp
  operationNames_nodup := by decide
  resolve
    | .decide => PaymentWebhook.decideDeclaration
    | .requestLedgerCommand => PaymentWebhook.ledgerDeclaration
    | .planResponse => responseDeclaration
    | .planAudit => auditDeclaration
    | .planNotification => notificationDeclaration
    | .planFulfillment => fulfillmentDeclaration

theorem duplicate_acknowledged :
    (planResponse.comp PaymentWebhook.decide) .duplicateSuccess = some .acknowledge := rfl

theorem duplicate_has_no_notification_intent :
    (planNotification.comp PaymentWebhook.decide) .duplicateSuccess = none := rfl

theorem duplicate_requests_no_fulfillment :
    (planFulfillment.comp
      (PaymentWebhook.requestLedgerCommand.comp PaymentWebhook.decide))
      .duplicateSuccess = none := rfl

theorem first_success_requests_fulfillment :
    (planFulfillment.comp
      (PaymentWebhook.requestLedgerCommand.comp PaymentWebhook.decide))
      .firstSuccess = some .enqueue := rfl

end ArchiScript.Examples.PaymentWebhookNetwork
