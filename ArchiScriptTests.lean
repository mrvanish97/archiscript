import ArchiScript
import ArchiScript.Examples.UserRegistration
import ArchiScript.Examples.PaymentWebhook
import ArchiScript.Examples.PaymentWebhookNetwork
import ArchiScriptTests.Domains

namespace ArchiScriptTests
open ArchiScript
open ArchiScript.Examples.UserRegistration

example (x : userPartition.Carrier) : ∃ i, userPartition.member i x :=
  userPartition.coverage x

example : ¬ (userPartition.member .validNew (.existingUser 7) ∧
    userPartition.member .validExisting (.existingUser 7)) :=
  userPartition.disjoint (by intro h; cases h) _

example : register existingUserBranchWitness.source = some existingUserBranchWitness.target :=
  existingUserBranchWitness.in_operation

example : existingUserBranch ≠ returnExistingBranch :=
  same_branch_name_different_operations

example : existingUserBranchAlias = existingUserBranch :=
  rfl

example : (routedRegistration.resolveOutbound .api ()).target = userPartition := rfl

example : ParameterizedPartition.RoutingRelevant routedRegistration :=
  routedRegistration_is_relevant

example : ParameterizedPartition.RoutesEquivalent renamedRoutes .web .api :=
  renamedRoutes_equivalent

#guard register .validExisting == some .selected
#guard register .validNew == some .created

-- Whole-operation responsibility, inheritance, overrides, and canonical aliases.
#guard registerDeclaration.responsibilityOwners == ["registration"]
#guard operationRegistry.resolveBranchResponsibility existingUserBranch == ["registration"]
#guard operationRegistry.resolveBranchResponsibility newUserBranch == ["user-storage"]
#guard operationRegistry.resolveBranchResponsibility existingUserBranchAlias == ["registration"]
#guard returnToUserDeclaration.effectiveResponsibility .existingUser == []

def explicitlyUnassigned : Operation.Declaration :=
  { registerDeclaration with branchResponsibilityOwners := fun _ => some [] }

#guard explicitlyUnassigned.effectiveResponsibility .newUser == []
#guard operationRegistry.resolveBranchImplementation existingUserBranch ==
  some (.planned { primary := { repository := "registration-service", path := "src/registration.ts", symbol := some "register" } })
#guard operationRegistry.resolveBranchImplementation existingUserBranchAlias ==
  operationRegistry.resolveBranchImplementation existingUserBranch
#guard operationRegistry.resolveBranchImplementation invalidUserBranch ==
  some (.unimplemented "illustrative model; production handler not yet supplied")
#guard operationRegistry.branchesWithoutImplementation.length == 6
#guard operationRegistry.branchesWithoutResponsibility.length == 6
#guard operationRegistry.branchAddresses.length == 9
#guard (operationRegistry.branchesAt {
  repository := "registration-service", path := "src/registration.ts",
  symbol := some "register", startLine := some 100 }).length == 2
#guard Operation.SourceRef.sameIdentity
  { repository := "repo", path := "src/a.ts", symbol := some "f", startLine := some 1 }
  { repository := "repo", path := "src/a.ts", symbol := some "f", startLine := some 80 }
#guard (operationRegistry.resolveBranch newUserBranch).target == RegistrationMemberIndex.created

-- The companion implementation binds every defined PaymentWebhook branch.
private def webhookRegistry := ArchiScript.Examples.PaymentWebhook.operationRegistry
#guard webhookRegistry.branchAddresses.length == 7
#guard webhookRegistry.branchesWithoutResponsibility.length == 0
#guard webhookRegistry.branchesWithoutImplementation.length == 0
#guard (webhookRegistry.branchesAt {
  repository := "archiscript", path := "examples/payment-webhook.mjs",
  symbol := some "decide" }).length == 5
#guard (webhookRegistry.branchesAt {
  repository := "archiscript", path := "examples/payment-webhook.mjs",
  symbol := some "handleWebhook" }).length == 7

private def networkRegistry := ArchiScript.Examples.PaymentWebhookNetwork.operationRegistry
#guard networkRegistry.operationNames.length == 6
#guard networkRegistry.branchAddresses.length == 20
#guard networkRegistry.branchesWithoutResponsibility.length == 0
#guard networkRegistry.branchesWithoutImplementation.length == 0

private def concurrencyFinding : ReviewFinding := {
  id := "RV-1"
  subject := { kind := .carrier, canonicalId := "PaymentWebhook.Input" }
  reviewer := "payments engineer"
  concern := "alreadyRecorded may race with another delivery"
  requestedChange := "state the snapshot or transaction boundary"
}

private def reviewRecord : ReviewRecord := {
  modelRevision := "model-v1"
  decision := .approved "payments engineer" "model-v1"
  findings := [concurrencyFinding]
}

#guard !reviewRecord.implementationAllowed
#guard { reviewRecord with findings := [{ concurrencyFinding with disposition := .addressed }] } |>.implementationAllowed
#guard !({ reviewRecord with modelRevision := "model-v2" }).implementationAllowed

example : (Operation.id userPartition).comp (Operation.id userPartition) =
    Operation.id userPartition := by
  simp

end ArchiScriptTests
