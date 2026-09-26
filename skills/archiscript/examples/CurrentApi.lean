import ArchiScript
import ArchiScript.Examples.UserRegistration

namespace SkillSmoke

open ArchiScript

inductive RequestIndex where
  | zero
  | positive
  deriving DecidableEq

def positive : Domain Nat := fun n => 0 < n

def requestPartition : Partition where
  Carrier := Nat
  MemberIndex := RequestIndex
  carrierNonempty := ⟨0⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.zero, .positive]
  memberIndices_complete := by intro i; cases i <;> simp
  classify n := if n = 0 then .zero else .positive
  member_inhabited
    | .zero => ⟨0, rfl⟩
    | .positive => ⟨1, rfl⟩

def requestRegions : RequestIndex → Domain Nat
  | .zero => Domain.complement positive
  | .positive => positive

example : requestPartition.Realizes requestRegions := by
  intro i n
  cases i <;> cases n <;> simp [Partition.member, requestPartition, requestRegions,
    Domain.complement, positive]

def accept : Operation requestPartition requestPartition where
  run
    | .zero => none
    | .positive => some .positive

inductive OperationName where | accept deriving DecidableEq
inductive BranchName where | positive deriving DecidableEq

def acceptDeclaration : Operation.Declaration where
  source := requestPartition
  target := requestPartition
  operation := accept
  BranchName := BranchName
  branchNameDecidableEq := inferInstance
  branchNames := [.positive]
  branchNames_complete := by intro name; cases name; simp
  branchNames_nodup := by decide
  branch
    | .positive => ⟨.positive, .positive, rfl⟩
  responsibilityOwners := ["request-api"]
  branchResponsibilityOwners := fun _ => some ["request-processing"]
  implementation := some (.planned { primary := { repository := "request-service", path := "src/requests.ts", symbol := some "accept" } })

def registry : Operation.Registry where
  OperationName := OperationName
  operationNameDecidableEq := inferInstance
  operationNames := [.accept]
  operationNames_complete := by intro name; cases name; simp
  operationNames_nodup := by decide
  resolve
    | .accept => acceptDeclaration

def acceptedBranch : Operation.BranchAddress registry :=
  ⟨.accept, .positive⟩

def acceptedBranchWitness := registry.resolveBranch acceptedBranch

#guard registry.resolveBranchResponsibility acceptedBranch == ["request-processing"]
#guard registry.branchesWithoutImplementation.length == 0

end SkillSmoke

namespace UserRegistrationSmoke

open ArchiScript
open ArchiScript.Examples.UserRegistration

example : register existingUserBranchWitness.source =
    some existingUserBranchWitness.target :=
  existingUserBranchWitness.in_operation

example : existingUserBranch ≠ returnExistingBranch :=
  same_branch_name_different_operations

example : existingUserBranchAlias = existingUserBranch :=
  rfl

example : ParameterizedPartition.RoutingRelevant routedRegistration :=
  routedRegistration_is_relevant

#check existingUserBranch_creates_no_user
#check NewUserCreation

end UserRegistrationSmoke
