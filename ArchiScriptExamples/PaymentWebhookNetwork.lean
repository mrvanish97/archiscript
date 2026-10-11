import ArchiScriptExamples.PaymentWebhook

namespace ArchiScriptExamples.PaymentWebhookNetwork
open ArchiScript

/-- The response obligation to the provider, not an HTTP write. -/
inductive ProviderResponse where
  | rejectRequest | acknowledge
  deriving DecidableEq, Repr

instance : MemberEnumeration ProviderResponse where
  indices := [.rejectRequest, .acknowledge]
  complete := by intro i; cases i <;> simp

abbrev responsePartition : Partition where
  Carrier := ProviderResponse
  MemberIndex := ProviderResponse
  carrierNonempty := ⟨.acknowledge⟩
  memberIndexDecidableEq := inferInstance
  memberIndexFinite := ⟨[.rejectRequest, .acknowledge], by intro i; cases i <;> simp⟩
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

abbrev responseSemanticPartition : SemanticPartition where
  partition := responsePartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

private def responseCarrierClosure : CarrierClosure ProviderResponse :=
  ⟨[.rejectRequest, .acknowledge], by intro x; cases x <;> simp⟩

/-- Audit categories are intent to record, not evidence that a record exists. -/
inductive AuditIntent where
  | invalidDelivery | unsupportedDelivery | paymentFailed
  | firstSuccess | duplicateSuccess
  deriving DecidableEq, Repr

instance : MemberEnumeration AuditIntent where
  indices := [.invalidDelivery, .unsupportedDelivery, .paymentFailed,
                    .firstSuccess, .duplicateSuccess]
  complete := by intro i; cases i <;> simp

abbrev auditPartition : Partition where
  Carrier := AuditIntent
  MemberIndex := AuditIntent
  carrierNonempty := ⟨.invalidDelivery⟩
  memberIndexDecidableEq := inferInstance
  memberIndexFinite := ⟨[.invalidDelivery, .unsupportedDelivery, .paymentFailed,
                    .firstSuccess, .duplicateSuccess], by intro i; cases i <;> simp⟩
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

abbrev auditSemanticPartition : SemanticPartition where
  partition := auditPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

private def auditCarrierClosure : CarrierClosure AuditIntent :=
  ⟨[.invalidDelivery, .unsupportedDelivery, .paymentFailed,
    .firstSuccess, .duplicateSuccess], by intro x; cases x <;> simp⟩

/-- A possible customer notification, not proof that a message was sent. -/
inductive NotificationIntent where
  | paymentFailure | successReceipt
  deriving DecidableEq, Repr

instance : MemberEnumeration NotificationIntent where
  indices := [.paymentFailure, .successReceipt]
  complete := by intro i; cases i <;> simp

abbrev notificationPartition : Partition where
  Carrier := NotificationIntent
  MemberIndex := NotificationIntent
  carrierNonempty := ⟨.paymentFailure⟩
  memberIndexDecidableEq := inferInstance
  memberIndexFinite := ⟨[.paymentFailure, .successReceipt], by intro i; cases i <;> simp⟩
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

abbrev notificationSemanticPartition : SemanticPartition where
  partition := notificationPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

private def notificationCarrierClosure : CarrierClosure NotificationIntent :=
  ⟨[.paymentFailure, .successReceipt], by intro x; cases x <;> simp⟩

/-- The fulfillment boundary has one request kind in this scoped example. -/
inductive FulfillmentRequest where
  | enqueue
  deriving DecidableEq, Repr

instance : MemberEnumeration FulfillmentRequest where
  indices := [.enqueue]
  complete := by intro i; cases i <;> simp

abbrev fulfillmentPartition : Partition where
  Carrier := FulfillmentRequest
  MemberIndex := FulfillmentRequest
  carrierNonempty := ⟨.enqueue⟩
  memberIndexDecidableEq := inferInstance
  memberIndexFinite := ⟨[.enqueue], by intro i; cases i <;> simp⟩
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

abbrev fulfillmentSemanticPartition : SemanticPartition where
  partition := fulfillmentPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

private def fulfillmentCarrierClosure : CarrierClosure FulfillmentRequest :=
  ⟨[.enqueue], by intro x; cases x <;> simp⟩

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

abbrev responseArchitecture : ArchitecturalPartition where
  partition := responsePartition
  carrierOrigin := .architecturalDomain "PaymentWebhookNetwork.planResponse" (by decide)
  carrierClosure := some responseCarrierClosure
  selectedMembers := fun i => ⟨fun x => x = i, .predicate (fun x => x = i)⟩
  hasMembers := by intro i x; rfl

abbrev auditArchitecture : ArchitecturalPartition where
  partition := auditPartition
  carrierOrigin := .architecturalDomain "PaymentWebhookNetwork.planAudit" (by decide)
  carrierClosure := some auditCarrierClosure
  selectedMembers := fun i => ⟨fun x => x = i, .predicate (fun x => x = i)⟩
  hasMembers := by intro i x; rfl

abbrev notificationArchitecture : ArchitecturalPartition where
  partition := notificationPartition
  carrierOrigin := .architecturalDomain "PaymentWebhookNetwork.planNotification" (by decide)
  carrierClosure := some notificationCarrierClosure
  selectedMembers := fun i => ⟨fun x => x = i, .predicate (fun x => x = i)⟩
  hasMembers := by intro i x; rfl

abbrev fulfillmentArchitecture : ArchitecturalPartition where
  partition := fulfillmentPartition
  carrierOrigin := .architecturalDomain "PaymentWebhookNetwork.planFulfillment" (by decide)
  carrierClosure := some fulfillmentCarrierClosure
  selectedMembers := fun i => ⟨fun x => x = i, .predicate (fun x => x = i)⟩
  hasMembers := by intro i x; rfl

def architecture : Architecture where
  operations := PaymentWebhook.architecture.operations ++ [
    ⟨PaymentWebhook.decisionArchitecture, responseArchitecture, planResponse⟩,
    ⟨PaymentWebhook.decisionArchitecture, auditArchitecture, planAudit⟩,
    ⟨PaymentWebhook.decisionArchitecture, notificationArchitecture, planNotification⟩,
    ⟨PaymentWebhook.ledgerCommandArchitecture, fulfillmentArchitecture, planFulfillment⟩
  ]

private def plannedCode (symbol : String) : Operation.ImplementationDisposition :=
  .planned { primary := {
    repository := "archiscript"
    path := "examples/payment-webhook-network.mjs"
    symbol := some symbol
  } }

abbrev responseDeclaration : Operation.Declaration where
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

abbrev auditDeclaration : Operation.Declaration where
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

abbrev notificationDeclaration : Operation.Declaration where
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

abbrev fulfillmentDeclaration : Operation.Declaration where
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

end ArchiScriptExamples.PaymentWebhookNetwork
