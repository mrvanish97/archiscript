import ArchiScript.ParameterizedPartition

namespace ArchiScript.Examples.UserRegistration
open ArchiScript

inductive UserInput where
  | malformed
  | newUser (email : String)
  | existingUser (id : Nat)
  deriving DecidableEq, Repr

inductive UserMemberIndex where
  | invalid
  | validNew
  | validExisting
  deriving DecidableEq, Repr

def userPartition : Partition where
  Carrier := UserInput
  MemberIndex := UserMemberIndex
  carrierNonempty := ⟨.malformed⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.invalid, .validNew, .validExisting]
  memberIndices_complete := by intro i; cases i <;> simp
  classify
    | .malformed => .invalid
    | .newUser _ => .validNew
    | .existingUser _ => .validExisting
  member_inhabited
    | .invalid => ⟨.malformed, rfl⟩
    | .validNew => ⟨.newUser "new@example.test", rfl⟩
    | .validExisting => ⟨.existingUser 0, rfl⟩

inductive RegistrationMemberIndex where
  | rejected
  | created
  | selected
  deriving DecidableEq, Repr

inductive RegistrationResult where
  | rejected
  | created (id : Nat)
  | selected (id : Nat)

def registrationPartition : Partition where
  Carrier := RegistrationResult
  MemberIndex := RegistrationMemberIndex
  carrierNonempty := ⟨.rejected⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.rejected, .created, .selected]
  memberIndices_complete := by intro i; cases i <;> simp
  classify
    | .rejected => .rejected
    | .created _ => .created
    | .selected _ => .selected
  member_inhabited
    | .rejected => ⟨.rejected, rfl⟩
    | .created => ⟨.created 0, rfl⟩
    | .selected => ⟨.selected 0, rfl⟩

def register : Operation userPartition registrationPartition where
  run
    | .invalid => some .rejected
    | .validNew => some .created
    | .validExisting => some .selected

abbrev UserStore := Nat → Prop

def NoNewUserCreated (before after : UserStore) : Prop :=
  ∀ id, after id → before id

inductive Channel where | web | api deriving DecidableEq, Repr

def channelPartition : Partition where
  Carrier := Bool
  MemberIndex := Channel
  carrierNonempty := ⟨false⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.web, .api]
  memberIndices_complete := by intro i; cases i <;> simp
  classify | false => .web | true => .api
  member_inhabited | .web => ⟨false, rfl⟩ | .api => ⟨true, rfl⟩

inductive OperationName where
  | register
  | registrationIdentity
  | returnToUser
  deriving DecidableEq

inductive BranchName where
  | invalid
  | newUser
  | existingUser
  deriving DecidableEq

def returnToUser : Operation registrationPartition userPartition where
  run
    | .rejected => some .invalid
    | .created => some .validNew
    | .selected => some .validExisting

def registerDeclaration : Operation.Declaration where
  source := userPartition
  target := registrationPartition
  operation := register
  BranchName := BranchName
  branchNameDecidableEq := inferInstance
  branch
    | .invalid => ⟨.invalid, .rejected, rfl⟩
    | .newUser => ⟨.validNew, .created, rfl⟩
    | .existingUser => ⟨.validExisting, .selected, rfl⟩
  owners := ["registration"]
  branchOwners
    | .newUser => some ["user-storage"]
    | _ => none

def registrationIdentityDeclaration : Operation.Declaration where
  source := registrationPartition
  target := registrationPartition
  operation := Operation.id registrationPartition
  BranchName := BranchName
  branchNameDecidableEq := inferInstance
  branch
    | .invalid => ⟨.rejected, .rejected, rfl⟩
    | .newUser => ⟨.created, .created, rfl⟩
    | .existingUser => ⟨.selected, .selected, rfl⟩

def returnToUserDeclaration : Operation.Declaration where
  source := registrationPartition
  target := userPartition
  operation := returnToUser
  BranchName := BranchName
  branchNameDecidableEq := inferInstance
  branch
    | .invalid => ⟨.rejected, .invalid, rfl⟩
    | .newUser => ⟨.created, .validNew, rfl⟩
    | .existingUser => ⟨.selected, .validExisting, rfl⟩

def operationRegistry : Operation.Registry where
  OperationName := OperationName
  operationNameDecidableEq := inferInstance
  resolve
    | .register => registerDeclaration
    | .registrationIdentity => registrationIdentityDeclaration
    | .returnToUser => returnToUserDeclaration

/-- Canonical branch addresses: identity is (registry operation, scoped name). -/
def invalidUserBranch : Operation.BranchAddress operationRegistry :=
  ⟨.register, .invalid⟩

def existingUserBranch : Operation.BranchAddress operationRegistry :=
  ⟨.register, .existingUser⟩

def newUserBranch : Operation.BranchAddress operationRegistry :=
  ⟨.register, .newUser⟩

def existingUserBranchWitness := operationRegistry.resolveBranch existingUserBranch
def newUserBranchWitness := operationRegistry.resolveBranch newUserBranch

/-- The same scoped name under another operation is a distinct branch. -/
def returnExistingBranch : Operation.BranchAddress operationRegistry :=
  ⟨.returnToUser, .existingUser⟩

theorem same_branch_name_different_operations :
    existingUserBranch ≠ returnExistingBranch := by
  intro h
  have operationEq := Operation.BranchAddress.operation_eq h
  cases operationEq

/-- An alias reuses the canonical operation identity and therefore the branch. -/
def registerAlias : operationRegistry.OperationName := .register
def existingUserBranchAlias : Operation.BranchAddress operationRegistry :=
  ⟨registerAlias, .existingUser⟩

/--
The existing-user effect contract is indexed by the canonical resolved branch.
Its store conclusion comes from `store_preserved`, not from member mapping.
-/
structure ExistingSelection (branch : Operation.Branch register)
    (before after : UserStore) where
  source_is_existing : branch.source = UserMemberIndex.validExisting
  input : UserInput
  input_in_branch : userPartition.classify input = branch.source
  output : RegistrationResult
  output_in_branch : registrationPartition.classify output = branch.target
  selectedId : Nat
  selected_was_present : before selectedId
  output_is_selected : output = .selected selectedId
  store_preserved : after = before

theorem existingUserBranch_creates_no_user
    {before after : UserStore}
    (step : ExistingSelection existingUserBranchWitness before after) :
    NoNewUserCreated before after := by
  intro id presentAfter
  rw [step.store_preserved] at presentAfter
  exact presentAfter

structure NewUserCreation (branch : Operation.Branch register)
    (before after : UserStore) where
  source_is_new : branch.source = UserMemberIndex.validNew
  input : UserInput
  input_in_branch : userPartition.classify input = branch.source
  output : RegistrationResult
  output_in_branch : registrationPartition.classify output = branch.target
  createdId : Nat
  output_is_created : output = .created createdId
  absent_before : ¬ before createdId
  present_after : after createdId
  other_users_preserved : ∀ id, id ≠ createdId → (after id ↔ before id)

/-- Equal route counts, but the actual identified operations differ. -/
def routedRegistration : ParameterizedPartition.Routed channelPartition where
  specialize := fun _ => registrationPartition
  registry := operationRegistry
  Route := fun _ => Unit
  routes := fun _ => [()]
  routes_complete := by
    intro _ r
    cases r
    simp
  routeOperation
    | .web, () => .registrationIdentity
    | .api, () => .returnToUser
  routeSource := by intro k route; cases k <;> cases route <;> rfl

theorem routedRegistration_is_relevant :
    ParameterizedPartition.RoutingRelevant routedRegistration := by
  refine ⟨.web, .api, ?_⟩
  refine ⟨.registrationIdentity, ?_⟩
  constructor
  · intro _ apiRoute
    rcases apiRoute with ⟨route, h⟩
    cases route
    cases h
  · intro _
    exact ⟨(), rfl⟩

inductive WebAlias where | primary
inductive ApiAlias where | renamed

/-- Different alias types/names for the same identified route are irrelevant. -/
def renamedRoutes : ParameterizedPartition.Routed channelPartition where
  specialize := fun _ => registrationPartition
  registry := operationRegistry
  Route | .web => WebAlias | .api => ApiAlias
  routes | .web => [.primary] | .api => [.renamed]
  routes_complete := by
    intro k route
    cases k <;> cases route <;> simp
  routeOperation := fun _ _ => .registrationIdentity
  routeSource := by intro k route; cases k <;> cases route <;> rfl

theorem renamedRoutes_equivalent :
    ParameterizedPartition.RoutesEquivalent renamedRoutes .web .api := by
  intro key
  cases key
  · constructor <;> intro h <;> rcases h with ⟨route, h⟩ <;> cases route <;> cases h
  · constructor <;> intro _
    · exact ⟨.renamed, rfl⟩
    · exact ⟨.primary, rfl⟩
  · constructor <;> intro h <;> rcases h with ⟨route, h⟩ <;> cases route <;> cases h

inductive Region where | domestic | international deriving DecidableEq, Repr

def regionPartition : Partition where
  Carrier := Bool
  MemberIndex := Region
  carrierNonempty := ⟨false⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.domestic, .international]
  memberIndices_complete := by intro i; cases i <;> simp
  classify | false => .domestic | true => .international
  member_inhabited | .domestic => ⟨false, rfl⟩ | .international => ⟨true, rfl⟩

/-- Two finite specialization steps, resolved inside-out to an ordinary VDP. -/
def regionalChannelRegistration : ParameterizedPartition.Nested regionPartition where
  innerParameter := fun _ => channelPartition
  result := fun
    | .domestic, .web => registrationPartition
    | .domestic, .api => userPartition
    | .international, .web => userPartition
    | .international, .api => registrationPartition

example : (regionalChannelRegistration.specialize .domestic .web).MemberIndex =
    RegistrationMemberIndex := rfl

end ArchiScript.Examples.UserRegistration
