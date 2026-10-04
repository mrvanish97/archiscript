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
  carrierOrigin := .externalRoot {
    source := "request protocol"
    scope := "count field after decoding"
    claim := "the decoder emits Nat values at this boundary"
    revision := "smoke-protocol-1"
    identified := by decide
  }
  selectedMembers := fun i => {
    meaning := requestMembers i
    definition := .predicate (requestMembers i)
  }
  hasMembers := requestSemanticPartition.hasMembers

def accept : Operation requestPartition requestPartition where
  run
    | .zero => none
    | .positive => some .positive

#check Partition.coproduct
#check SemanticPartition.coproduct
#check Operation.coproductInl
#check Operation.coproductInr
#check Operation.copair
#check Operation.copair_unique
#check Partition.RefinesVia
#check Partition.coarseningOperation
#check Operation.analyzeFactorization

def pairedRequests : SemanticPartition :=
  requestSemanticPartition.tensor requestSemanticPartition

example : pairedRequests.partition = requestPartition.tensor requestPartition := rfl

example (i j : RequestIndex) (x y : Nat) :
    pairedRequests.members (i, j) (x, y) ↔
      requestMembers i x ∧ requestMembers j y := Iff.rfl

def pairedAccept : Operation (requestPartition.tensor requestPartition)
    (requestPartition.tensor requestPartition) := accept.tensor accept

example : pairedAccept (.zero, .positive) = none := rfl
example : pairedAccept (.positive, .positive) = some (.positive, .positive) := rfl

example : (Operation.associatorInv requestPartition requestPartition requestPartition).comp
    (Operation.associator requestPartition requestPartition requestPartition) =
      Operation.id ((requestPartition.tensor requestPartition).tensor requestPartition) :=
  Operation.associator_left_inv _ _ _

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

-- The smoke file also covers the structural monoidal API, not only tensor construction.
#guard Partition.unit.memberIndices.length == 1

example :
    (Operation.symmetry requestPartition requestPartition).comp
        (Operation.symmetry requestPartition requestPartition) =
      Operation.id (requestPartition.tensor requestPartition) :=
  Operation.symmetry_involutive requestPartition requestPartition

example :
    ((Operation.id requestPartition).tensor (Operation.leftUnitor requestPartition)).comp
        (Operation.associator requestPartition Partition.unit requestPartition) =
      (Operation.rightUnitor requestPartition).tensor (Operation.id requestPartition) :=
  Operation.triangle requestPartition requestPartition

/-- Architectural handoff remains separate from the low-level member map. -/
def requestArchitecturalOperation : ArchitecturalOperation where
  source := requestArchitecture
  target := requestArchitecture
  operation := accept

def architecture : Architecture where
  operations := [requestArchitecturalOperation]

#guard architecture.operations.length == 1

/-- A minimal routed family exercises the public parameterized-routing surface. -/
def routedRequests : ParameterizedPartition.Routed requestPartition where
  specialize := fun _ => requestPartition
  registry := registry
  Route := fun _ => Unit
  routes := fun _ => [()]
  routes_complete := by
    intro _ route
    cases route
    simp
  routeOperation := fun _ _ => .accept
  routeSource := by
    intro _ route
    cases route
    rfl

def routedPositive := routedRequests.resolveOutbound .positive ()

example : routedPositive.target = requestPartition := rfl
example : ParameterizedPartition.HasOperation routedRequests .positive .accept := by
  exact ⟨(), rfl⟩

/-- Review approval is an explicit workflow predicate, not a consequence of compilation. -/
private def smokeReview : ReviewRecord where
  modelRevision := "smoke-v1"
  decision := .approved "skill-reviewer" "smoke-v1"

#guard smokeReview.implementationAllowed

end SkillSmoke