import Lean
import ArchiScript.Examples.PaymentWebhookNetwork

open Lean
open ArchiScript
open ArchiScript.Examples
open ArchiScript.Examples.PaymentWebhookNetwork

private def shortName {α : Type} [Repr α] (value : α) : String :=
  (reprStr value).splitOn "." |>.getLast!

private def operationJson {X Y : Partition} (id source target : String)
    (op : Operation X Y) : Json :=
  Json.mkObj [
    ("id", toJson s!"PaymentWebhookNetwork.{id}"),
    ("operation", toJson id),
    ("source", toJson source),
    ("target", toJson target),
    ("partial", toJson (X.memberIndices.any fun member => (op member).isNone))
  ]

private def memberJson (id : String) (names : List String) : Json :=
  Json.mkObj [("id", toJson s!"PaymentWebhookNetwork.{id}"),
              ("name", toJson id), ("members", toJson names)]

private def notificationJson (source : PaymentWebhook.Decision) : Json :=
  let target := match planNotification source with
    | none => "none"
    | some result => shortName (show NotificationIntent from result)
  Json.mkObj [("source", toJson (shortName source)), ("target", toJson target)]

private def dispositionJson (disposition : Option Operation.ImplementationDisposition) : Json :=
  match disposition with
  | some (.resolved binding) => sourceJson "resolved" binding.primary
  | some (.planned binding) => sourceJson "planned" binding.primary
  | some (.external reason) => Json.mkObj [("status", toJson "external"), ("reason", toJson reason)]
  | some (.intentionallyAbstract reason) => Json.mkObj [("status", toJson "intentionallyAbstract"), ("reason", toJson reason)]
  | some (.unimplemented reason) => Json.mkObj [("status", toJson "unimplemented"), ("reason", toJson reason)]
  | none => Json.mkObj [("status", toJson "missing")]
where
  sourceJson (status : String) (source : Operation.SourceRef) : Json :=
    Json.mkObj [("status", toJson status),
                ("repository", toJson source.repository),
                ("path", toJson source.path),
                ("symbol", toJson source.symbol)]

private def bindingJson (id : String) (address : Operation.BranchAddress operationRegistry) : Json :=
  Json.mkObj [
    ("id", toJson id),
    ("responsibility", toJson (operationRegistry.resolveBranchResponsibility address)),
    ("implementation", dispositionJson (operationRegistry.resolveBranchImplementation address))
  ]

private def duplicatePathJson : Json := Id.run do
  let decision := PaymentWebhook.decide .duplicateSuccess
  let ledger := decision.bind PaymentWebhook.requestLedgerCommand.run
  let response := decision.bind planResponse.run
  return Json.mkObj [
    ("source", toJson "duplicateSuccess"),
    ("decision", toJson (match decision with
      | none => "none"
      | some result => shortName (show PaymentWebhook.Decision from result))),
    ("ledger", toJson (match ledger with
      | none => "none"
      | some result => shortName (show PaymentWebhook.LedgerCommand from result))),
    ("response", toJson (match response with
      | none => "none"
      | some result => shortName (show ProviderResponse from result)))
  ]

private def checkedClaims : List Json := Id.run do
  have _ : PaymentWebhook.inputPartition.Realizes PaymentWebhook.inputRegions :=
    PaymentWebhook.inputPartition_realizes_regions
  have _ : (planResponse.comp PaymentWebhook.decide) .duplicateSuccess =
      some .acknowledge := duplicate_acknowledged
  have _ : (planNotification.comp PaymentWebhook.decide) .duplicateSuccess = none :=
    duplicate_has_no_notification_intent
  have _ : (planFulfillment.comp
      (PaymentWebhook.requestLedgerCommand.comp PaymentWebhook.decide))
      .duplicateSuccess = none := duplicate_requests_no_fulfillment
  have _ : (planFulfillment.comp
      (PaymentWebhook.requestLedgerCommand.comp PaymentWebhook.decide))
      .firstSuccess = some .enqueue := first_success_requests_fulfillment
  return [
    Json.mkObj [("proof", toJson "PaymentWebhook.inputPartition_realizes_regions"),
                ("claim", toJson "inputPartition realizes independently stated inputRegions")],
    Json.mkObj [("proof", toJson "PaymentWebhookNetwork.duplicate_acknowledged"),
                ("claim", toJson "duplicateSuccess has an acknowledge response plan")],
    Json.mkObj [("proof", toJson "PaymentWebhookNetwork.duplicate_has_no_notification_intent"),
                ("claim", toJson "duplicateSuccess has no notification mapping")],
    Json.mkObj [("proof", toJson "PaymentWebhookNetwork.duplicate_requests_no_fulfillment"),
                ("claim", toJson "duplicateSuccess has no fulfillment-request mapping")],
    Json.mkObj [("proof", toJson "PaymentWebhookNetwork.first_success_requests_fulfillment"),
                ("claim", toJson "firstSuccess maps to an enqueue request")]
  ]

private def projection : Json := Json.mkObj [
  ("model", toJson "PaymentWebhookNetwork"),
  ("topology", toJson ([
    operationJson "decide" "inputPartition" "decisionPartition" PaymentWebhook.decide,
    operationJson "requestLedgerCommand" "decisionPartition" "ledgerCommandPartition"
      PaymentWebhook.requestLedgerCommand,
    operationJson "planResponse" "decisionPartition" "responsePartition" planResponse,
    operationJson "planAudit" "decisionPartition" "auditPartition" planAudit,
    operationJson "planNotification" "decisionPartition" "notificationPartition" planNotification,
    operationJson "planFulfillment" "ledgerCommandPartition" "fulfillmentPartition" planFulfillment
  ] : List Json)),
  ("partitions", toJson ([
    memberJson "inputPartition" (PaymentWebhook.inputPartition.memberIndices.map
      (fun (m : PaymentWebhook.InputMember) => shortName m)),
    memberJson "decisionPartition" (PaymentWebhook.decisionPartition.memberIndices.map
      (fun (m : PaymentWebhook.Decision) => shortName m)),
    memberJson "ledgerCommandPartition" (PaymentWebhook.ledgerCommandPartition.memberIndices.map
      (fun (m : PaymentWebhook.LedgerCommand) => shortName m)),
    memberJson "responsePartition" (responsePartition.memberIndices.map
      (fun (m : ProviderResponse) => shortName m)),
    memberJson "auditPartition" (auditPartition.memberIndices.map
      (fun (m : AuditIntent) => shortName m)),
    memberJson "notificationPartition" (notificationPartition.memberIndices.map
      (fun (m : NotificationIntent) => shortName m)),
    memberJson "fulfillmentPartition" (fulfillmentPartition.memberIndices.map
      (fun (m : FulfillmentRequest) => shortName m))
  ] : List Json)),
  ("notificationMappings", toJson (PaymentWebhook.decisionPartition.memberIndices.map
    (fun (m : PaymentWebhook.Decision) => notificationJson m))),
  ("inputRegions", toJson (PaymentWebhook.inputPartition.memberIndices.map
    (fun (m : PaymentWebhook.InputMember) => Json.mkObj [
      ("id", toJson s!"PaymentWebhookNetwork.inputPartition.{shortName m}"),
      ("name", toJson (shortName m)),
      ("description", toJson (PaymentWebhook.inputRegion m).description)
    ]))),
  ("duplicatePath", duplicatePathJson),
  ("bindingRows", toJson ([
    bindingJson "PaymentWebhookNetwork.decide.duplicateSuccess"
      ⟨.decide, .duplicateSuccess⟩,
    bindingJson "PaymentWebhookNetwork.planResponse.acknowledgeDuplicate"
      ⟨.planResponse, .acknowledgeDuplicate⟩,
    bindingJson "PaymentWebhookNetwork.planAudit.acknowledgeDuplicate"
      ⟨.planAudit, .acknowledgeDuplicate⟩,
    bindingJson "PaymentWebhookNetwork.planFulfillment.recordAndQueueFulfillment"
      ⟨.planFulfillment, .recordAndQueueFulfillment⟩
  ] : List Json)),
  ("missingResponsibility", toJson operationRegistry.branchesWithoutResponsibility.length),
  ("missingImplementation", toJson operationRegistry.branchesWithoutImplementation.length),
  ("checkedClaims", toJson checkedClaims)
]

def main : IO Unit := IO.println projection.compress
