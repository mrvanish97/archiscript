import Lean
import ArchiScript.Examples.PaymentWebhook

open Lean
open ArchiScript
open ArchiScript.Examples.PaymentWebhook

private def shortName {α : Type} [Repr α] (value : α) : String :=
  (reprStr value).splitOn "." |>.getLast!

private def sourceRefJson (source : Operation.SourceRef) : Json :=
  Json.mkObj [
    ("repository", toJson source.repository),
    ("path", toJson source.path),
    ("symbol", toJson source.symbol),
    ("startLine", toJson source.startLine),
    ("endLine", toJson source.endLine),
    ("revision", toJson source.revision)
  ]

private def bindingJson (binding : Operation.ImplementationBinding) : Json :=
  Json.mkObj [
    ("primary", sourceRefJson binding.primary),
    ("supporting", toJson (binding.supporting.map sourceRefJson)),
    ("evidence", toJson (binding.evidence.map fun item =>
      Json.mkObj [("kind", toJson (shortName item.kind)),
                  ("reference", toJson item.reference)]))
  ]

private def dispositionJson : Option Operation.ImplementationDisposition → Json
  | none => Json.mkObj [("status", toJson "missing")]
  | some (.planned binding) => Json.mkObj [("status", toJson "planned"), ("binding", bindingJson binding)]
  | some (.resolved binding) => Json.mkObj [("status", toJson "resolved"), ("binding", bindingJson binding)]
  | some (.external reference) => Json.mkObj [("status", toJson "external"), ("reason", toJson reference)]
  | some (.intentionallyAbstract reason) => Json.mkObj [("status", toJson "intentionallyAbstract"), ("reason", toJson reason)]
  | some (.unimplemented reason) => Json.mkObj [("status", toJson "unimplemented"), ("reason", toJson reason)]

private def decideBranchJson (name : DecideBranch) : Json := Id.run do
  let branch := decideDeclaration.branch name
  let address : Operation.BranchAddress operationRegistry := ⟨.decide, name⟩
  return Json.mkObj [
    ("id", toJson s!"PaymentWebhook.decide.{shortName name}"),
    ("source", toJson (shortName (show InputMember from branch.source))),
    ("target", toJson (shortName (show Decision from branch.target))),
    ("responsibility", toJson (operationRegistry.resolveBranchResponsibility address)),
    ("implementation", dispositionJson (operationRegistry.resolveBranchImplementation address))
  ]

private def ledgerMappingJson (source : Decision) : Json := Id.run do
  let target := match requestLedgerCommand source with
    | none => "none"
    | some value => shortName (show LedgerCommand from value)
  return Json.mkObj [
    ("source", toJson (shortName source)),
    ("target", toJson target)
  ]

private def ledgerBranchJson (name : LedgerBranch) : Json := Id.run do
  let branch := ledgerDeclaration.branch name
  let address : Operation.BranchAddress operationRegistry := ⟨.requestLedgerCommand, name⟩
  return Json.mkObj [
    ("id", toJson s!"PaymentWebhook.requestLedgerCommand.{shortName name}"),
    ("source", toJson (shortName (show Decision from branch.source))),
    ("target", toJson (shortName (show LedgerCommand from branch.target))),
    ("responsibility", toJson (operationRegistry.resolveBranchResponsibility address)),
    ("implementation", dispositionJson (operationRegistry.resolveBranchImplementation address))
  ]

private def checkedClaims : List Json := Id.run do
  have _ : inputPartition.Realizes inputRegions := inputPartition_realizes_regions
  have _ : (requestLedgerCommand.comp decide) .firstSuccess =
      some .recordAndQueueFulfillment := first_success_requests_fulfillment
  have _ : (requestLedgerCommand.comp decide) .duplicateSuccess = none :=
    duplicate_requests_no_ledger_command
  return [
    Json.mkObj [("proof", toJson "PaymentWebhook.inputPartition_realizes_regions"),
                ("claim", toJson "inputPartition realizes inputRegions")],
    Json.mkObj [("proof", toJson "PaymentWebhook.first_success_requests_fulfillment"),
                ("claim", toJson "requestLedgerCommand.comp decide maps firstSuccess to recordAndQueueFulfillment")],
    Json.mkObj [("proof", toJson "PaymentWebhook.duplicate_requests_no_ledger_command"),
                ("claim", toJson "requestLedgerCommand.comp decide maps duplicateSuccess to none")]
  ]

private def objectJson (kind id : String) : Json :=
  Json.mkObj [("id", toJson id), ("kind", toJson kind)]

private def inputRegionJson (name : InputMember) : Json :=
  Json.mkObj [
    ("id", toJson s!"PaymentWebhook.inputPartition.{shortName name}"),
    ("name", toJson (shortName name)),
    ("description", toJson (inputRegion name).description)
  ]

private def projection : Json := Json.mkObj [
  ("model", toJson "PaymentWebhook"),
  ("objects", toJson ([
    objectJson "carrier" "PaymentWebhook.Input",
    objectJson "partition" "PaymentWebhook.inputPartition",
    objectJson "partition" "PaymentWebhook.decisionPartition",
    objectJson "partition" "PaymentWebhook.ledgerCommandPartition",
    objectJson "operation" "PaymentWebhook.decide",
    objectJson "operation" "PaymentWebhook.requestLedgerCommand"
  ] ++ inputPartition.memberIndices.map (fun (name : InputMember) =>
    objectJson "member" s!"PaymentWebhook.inputPartition.{shortName name}") ++
       decisionPartition.memberIndices.map (fun (name : Decision) =>
    objectJson "member" s!"PaymentWebhook.decisionPartition.{shortName name}") ++
       ledgerCommandPartition.memberIndices.map (fun (name : LedgerCommand) =>
    objectJson "member" s!"PaymentWebhook.ledgerCommandPartition.{shortName name}") ++
       decideDeclaration.branchNames.flatMap (fun (name : DecideBranch) =>
    [objectJson "branch" s!"PaymentWebhook.decide.{shortName name}",
     objectJson "implementationBinding" s!"PaymentWebhook.decide.{shortName name}.implementation"]) ++
       ledgerDeclaration.branchNames.flatMap (fun (name : LedgerBranch) =>
    [objectJson "branch" s!"PaymentWebhook.requestLedgerCommand.{shortName name}",
     objectJson "implementationBinding"
       s!"PaymentWebhook.requestLedgerCommand.{shortName name}.implementation"]))),
  ("inputMembers", toJson (inputPartition.memberIndices.map (fun (m : InputMember) => shortName m))),
  ("inputRegions", toJson (inputPartition.memberIndices.map
    (fun (m : InputMember) => inputRegionJson m))),
  ("decisionMembers", toJson (decisionPartition.memberIndices.map (fun (m : Decision) => shortName m))),
  ("ledgerMembers", toJson (ledgerCommandPartition.memberIndices.map (fun (m : LedgerCommand) => shortName m))),
  ("topology", toJson ([
    Json.mkObj [
      ("id", toJson "PaymentWebhook.decide"),
      ("source", toJson "inputPartition"),
      ("operation", toJson (shortName OperationName.decide)),
      ("target", toJson "decisionPartition"),
      ("partial", toJson (inputPartition.memberIndices.any fun member => (decide member).isNone))
    ],
    Json.mkObj [
      ("id", toJson "PaymentWebhook.requestLedgerCommand"),
      ("source", toJson "decisionPartition"),
      ("operation", toJson (shortName OperationName.requestLedgerCommand)),
      ("target", toJson "ledgerCommandPartition"),
      ("partial", toJson (decisionPartition.memberIndices.any
        fun member => (requestLedgerCommand member).isNone))
    ]
  ] : List Json)),
  ("decideBranches", toJson (decideDeclaration.branchNames.map decideBranchJson)),
  ("ledgerBranches", toJson (ledgerDeclaration.branchNames.map ledgerBranchJson)),
  ("ledgerMappings", toJson (decisionPartition.memberIndices.map ledgerMappingJson)),
  ("checkedClaims", toJson checkedClaims)
]

def main : IO Unit := IO.println projection.compress
