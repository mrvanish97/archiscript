import Lean
import ArchiScriptExamples.PaymentWebhookNetwork

open Lean
open ArchiScript
open ArchiScriptExamples
open ArchiScriptExamples.PaymentWebhookNetwork

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

private def mappingCoverageJson (name : OperationName) : Json :=
  let declaration := operationRegistry.resolve name
  Json.mkObj [
    ("id", toJson s!"PaymentWebhookNetwork.{shortName name}"),
    ("missingDefinedMappings", toJson declaration.definedMappingsWithoutBranch.length)
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
  have _ : PaymentWebhook.inputPartition.HasMembers PaymentWebhook.inputMembers :=
    PaymentWebhook.inputSemanticPartition.hasMembers
  have _ : PaymentWebhook.decisionPartition.HasMembers
      PaymentWebhook.decisionSemanticPartition.members :=
    PaymentWebhook.decisionSemanticPartition.hasMembers
  have _ : PaymentWebhook.ledgerCommandPartition.HasMembers
      PaymentWebhook.ledgerCommandSemanticPartition.members :=
    PaymentWebhook.ledgerCommandSemanticPartition.hasMembers
  have _ : responsePartition.HasMembers responseSemanticPartition.members :=
    responseSemanticPartition.hasMembers
  have _ : auditPartition.HasMembers auditSemanticPartition.members :=
    auditSemanticPartition.hasMembers
  have _ : notificationPartition.HasMembers notificationSemanticPartition.members :=
    notificationSemanticPartition.hasMembers
  have _ : fulfillmentPartition.HasMembers fulfillmentSemanticPartition.members :=
    fulfillmentSemanticPartition.hasMembers
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
    Json.mkObj [("proof", toJson "PaymentWebhook.inputSemanticPartition.hasMembers"),
                ("claim", toJson "inputPartition classifier agrees with inputMembers")],
    Json.mkObj [("proof", toJson "PaymentWebhookNetwork.duplicate_acknowledged"),
                ("claim", toJson "duplicateSuccess has an acknowledge response plan")],
    Json.mkObj [("proof", toJson "PaymentWebhookNetwork.duplicate_has_no_notification_intent"),
                ("claim", toJson "duplicateSuccess has no notification mapping")],
    Json.mkObj [("proof", toJson "PaymentWebhookNetwork.duplicate_requests_no_fulfillment"),
                ("claim", toJson "duplicateSuccess has no fulfillment-request mapping")],
    Json.mkObj [("proof", toJson "PaymentWebhookNetwork.first_success_requests_fulfillment"),
                ("claim", toJson "firstSuccess maps to an enqueue request")]
  ]

private def semanticPartitionJson (id proof : String) (members : List String) : Json :=
  Json.mkObj [("id", toJson id), ("members", toJson members), ("proof", toJson proof)]

private def provenanceJson {α : Type} : CarrierOrigin α → Json
  | .externalRoot boundary => Json.mkObj [
      ("status", toJson "trusted-external-root"),
      ("source", toJson boundary.source), ("scope", toJson boundary.scope),
      ("claim", toJson boundary.claim), ("revision", toJson boundary.revision)]
  | .externalNarrowing upstream boundary => Json.mkObj [
      ("status", toJson "trusted-external-narrowing"),
      ("upstreamOrigin", provenanceJson upstream),
      ("source", toJson boundary.source), ("scope", toJson boundary.scope),
      ("claim", toJson boundary.claim), ("revision", toJson boundary.revision)]
  | .architecturalDomain identity _ => Json.mkObj [
      ("status", toJson "architecture-defined-domain"),
      ("identity", toJson identity),
      ("limit", toJson "This origin identifies a semantic carrier; operations map members only")]

private def definitionJson {α : Type} {meaning : Domain α} :
    DomainDerivation α meaning → Json
  | .predicate _ => Json.mkObj [("status", toJson "lean-predicate")]
  | .opaque reason _ _ => Json.mkObj [
      ("status", toJson "opaque"), ("reason", toJson reason)]
  | .intersection left right => Json.mkObj [
      ("status", toJson "intersection"),
      ("parts", toJson [definitionJson left, definitionJson right])]
  | .union left right => Json.mkObj [
      ("status", toJson "union"),
      ("parts", toJson [definitionJson left, definitionJson right])]
  | .relativeComplement base removed _ => Json.mkObj [
      ("status", toJson "relative-complement"),
      ("parts", toJson [definitionJson base, definitionJson removed])]

private def architectureJson (id : String) (P : ArchitecturalPartition)
    (memberName : P.partition.MemberIndex → String) : Json :=
  Json.mkObj [
    ("id", toJson id), ("carrierProvenance", provenanceJson P.carrierOrigin),
    ("carrierClosure", toJson P.carrierClosure.isSome),
    ("supportingSubdomains", toJson (P.supportingSubdomains.map fun s =>
      Json.mkObj [
        ("id", toJson s!"{id}.{s.name}"),
        ("definition", definitionJson s.definition)])),
    ("members", toJson (P.partition.memberIndices.map fun i =>
      Json.mkObj [
        ("id", toJson s!"{id}.{memberName i}"),
        ("definition", definitionJson (P.selectedMembers i).definition)]))
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
  ("inputRegions", toJson (PaymentWebhook.inputSemanticPartition.partition.memberIndices.map
    (fun (m : PaymentWebhook.InputMember) => Json.mkObj [
      ("id", toJson s!"PaymentWebhookNetwork.inputPartition.{shortName m}"),
      ("name", toJson (shortName m)),
      ("description", toJson (PaymentWebhook.inputRegion m).description)
    ]))),
  ("semanticPartitions", toJson ([
    semanticPartitionJson "PaymentWebhookNetwork.inputPartition"
      "PaymentWebhook.inputSemanticPartition.hasMembers"
      (PaymentWebhook.inputSemanticPartition.partition.memberIndices.map
        (fun (m : PaymentWebhook.InputMember) => s!"PaymentWebhookNetwork.inputPartition.{shortName m}")),
    semanticPartitionJson "PaymentWebhookNetwork.decisionPartition"
      "PaymentWebhook.decisionSemanticPartition.hasMembers"
      (PaymentWebhook.decisionSemanticPartition.partition.memberIndices.map
        (fun (m : PaymentWebhook.Decision) => s!"PaymentWebhookNetwork.decisionPartition.{shortName m}")),
    semanticPartitionJson "PaymentWebhookNetwork.ledgerCommandPartition"
      "PaymentWebhook.ledgerCommandSemanticPartition.hasMembers"
      (PaymentWebhook.ledgerCommandSemanticPartition.partition.memberIndices.map
        (fun (m : PaymentWebhook.LedgerCommand) => s!"PaymentWebhookNetwork.ledgerCommandPartition.{shortName m}")),
    semanticPartitionJson "PaymentWebhookNetwork.responsePartition"
      "PaymentWebhookNetwork.responseSemanticPartition.hasMembers"
      (responseSemanticPartition.partition.memberIndices.map
        (fun (m : ProviderResponse) => s!"PaymentWebhookNetwork.responsePartition.{shortName m}")),
    semanticPartitionJson "PaymentWebhookNetwork.auditPartition"
      "PaymentWebhookNetwork.auditSemanticPartition.hasMembers"
      (auditSemanticPartition.partition.memberIndices.map
        (fun (m : AuditIntent) => s!"PaymentWebhookNetwork.auditPartition.{shortName m}")),
    semanticPartitionJson "PaymentWebhookNetwork.notificationPartition"
      "PaymentWebhookNetwork.notificationSemanticPartition.hasMembers"
      (notificationSemanticPartition.partition.memberIndices.map
        (fun (m : NotificationIntent) => s!"PaymentWebhookNetwork.notificationPartition.{shortName m}")),
    semanticPartitionJson "PaymentWebhookNetwork.fulfillmentPartition"
      "PaymentWebhookNetwork.fulfillmentSemanticPartition.hasMembers"
      (fulfillmentSemanticPartition.partition.memberIndices.map
        (fun (m : FulfillmentRequest) => s!"PaymentWebhookNetwork.fulfillmentPartition.{shortName m}"))
  ] : List Json)),
  ("architecturalPartitions", toJson ([
    architectureJson "PaymentWebhookNetwork.inputPartition" PaymentWebhook.inputArchitecture
      (fun i => shortName (show PaymentWebhook.InputMember from i)),
    architectureJson "PaymentWebhookNetwork.decisionPartition" PaymentWebhook.decisionArchitecture
      (fun i => shortName (show PaymentWebhook.Decision from i)),
    architectureJson "PaymentWebhookNetwork.ledgerCommandPartition" PaymentWebhook.ledgerCommandArchitecture
      (fun i => shortName (show PaymentWebhook.LedgerCommand from i)),
    architectureJson "PaymentWebhookNetwork.responsePartition" responseArchitecture
      (fun i => shortName (show ProviderResponse from i)),
    architectureJson "PaymentWebhookNetwork.auditPartition" auditArchitecture
      (fun i => shortName (show AuditIntent from i)),
    architectureJson "PaymentWebhookNetwork.notificationPartition" notificationArchitecture
      (fun i => shortName (show NotificationIntent from i)),
    architectureJson "PaymentWebhookNetwork.fulfillmentPartition" fulfillmentArchitecture
      (fun i => shortName (show FulfillmentRequest from i))
  ] : List Json)),
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
  ("mappingCoverage", toJson (operationRegistry.operationNames.map mappingCoverageJson)),
  ("checkedClaims", toJson checkedClaims)
]

def main : IO Unit := IO.println projection.compress
