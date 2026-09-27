import ArchiScript

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

def requestMembers : RequestIndex → Domain Nat
  | .zero => Domain.complement positive
  | .positive => positive

example : requestPartition.HasMembers requestMembers := by
  intro i n
  cases i <;> cases n <;> simp [Partition.member, requestPartition, requestMembers,
    Domain.complement, positive]

def requestSemanticPartition : SemanticPartition where
  partition := requestPartition
  members := requestMembers
  hasMembers := by
    intro i n
    cases i <;> cases n <;> simp [Partition.member, requestPartition, requestMembers,
      Domain.complement, positive]

def requestArchitecture : ArchitecturalPartition where
  partition := requestPartition
  carrierProvenance := .externalRoot {
    source := "request protocol"
    scope := "count field after decoding"
    claim := "the decoder emits Nat values at this boundary"
    revision := "smoke-protocol-1"
    identified := by decide
  }
  selectedMembers := fun i => {
    meaning := requestMembers i
    definition := .formula "zero or positive count"
  }
  hasMembers := requestSemanticPartition.hasMembers

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
