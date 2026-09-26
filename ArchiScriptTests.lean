import ArchiScript
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

-- Whole-operation ownership, inheritance, overrides, and canonical aliases.
#guard registerDeclaration.owners == ["registration"]
#guard operationRegistry.resolveBranchOwners existingUserBranch == ["registration"]
#guard operationRegistry.resolveBranchOwners newUserBranch == ["user-storage"]
#guard operationRegistry.resolveBranchOwners existingUserBranchAlias == ["registration"]
#guard returnToUserDeclaration.effectiveOwners .existingUser == []

def explicitlyUnassigned : Operation.Declaration :=
  { registerDeclaration with branchOwners := fun _ => some [] }

#guard explicitlyUnassigned.effectiveOwners .newUser == []
#guard (operationRegistry.resolveBranch newUserBranch).target == RegistrationMemberIndex.created

example : (Operation.id userPartition).comp (Operation.id userPartition) =
    Operation.id userPartition := by
  simp

end ArchiScriptTests
