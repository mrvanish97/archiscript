import ArchiScriptExamples.ProofSupport
import ArchiScript.ParameterizedPartition

namespace ArchiScriptExamples.UserRegistration
open ArchiScript

/-- Preclassified API fixture. These constructors assume upstream classification;
they do not model untrusted registration input or validate email strings. -/
inductive PreclassifiedUserInput where
  | malformed
  | newUser (email : String)
  | existingUser (id : Nat)
  deriving DecidableEq, Repr

inductive UserMemberIndex where
  | invalid
  | validNew
  | validExisting
  deriving DecidableEq, Repr

instance : MemberEnumeration UserMemberIndex where
  indices := [.invalid, .validNew, .validExisting]
  complete := by intro i; cases i <;> simp

def userPartitionRegions : UserMemberIndex → Domain PreclassifiedUserInput
  | .invalid => fun x => x = .malformed
  | .validNew => fun x => ∃ email, x = .newUser email
  | .validExisting => fun x => ∃ id, x = .existingUser id

def userPartitionLookup : PreclassifiedUserInput → UserMemberIndex
    | .malformed => .invalid
    | .newUser _ => .validNew
    | .existingUser _ => .validExisting

theorem userPartitionLookup_correct : ∀ i x, userPartitionLookup x = i ↔ userPartitionRegions i x := by
  intro i x
  cases i <;> cases x <;> simp [userPartitionLookup, userPartitionRegions]

theorem userPartitionLookup_inhabited : ∀ i : UserMemberIndex, ∃ x : PreclassifiedUserInput, userPartitionLookup x = i := fun
    | .invalid => ⟨.malformed, rfl⟩
    | .validNew => ⟨.newUser "new@example.test", rfl⟩
    | .validExisting => ⟨.existingUser 0, rfl⟩

abbrev userPartition : Partition :=
  partitionOfRegions PreclassifiedUserInput UserMemberIndex "userPartition" userPartitionRegions
    (⟨[.invalid, .validNew, .validExisting], by intro i; cases i <;> simp⟩) userPartitionLookup userPartitionLookup_correct
    (by
      intro i
      obtain ⟨x, hx⟩ := userPartitionLookup_inhabited i
      exact ⟨x, (userPartitionLookup_correct i x).mp hx⟩)
    ⟨.invalid⟩

inductive RegistrationMemberIndex where
  | rejected
  | created
  | selected
  deriving DecidableEq, Repr

inductive RegistrationResult where
  | rejected
  | created (id : Nat)
  | selected (id : Nat)

instance : MemberEnumeration RegistrationMemberIndex where
  indices := [.rejected, .created, .selected]
  complete := by intro i; cases i <;> simp

def registrationPartitionRegions : RegistrationMemberIndex → Domain RegistrationResult
  | .rejected => fun x => x = .rejected
  | .created => fun x => ∃ id, x = .created id
  | .selected => fun x => ∃ id, x = .selected id

def registrationPartitionLookup : RegistrationResult → RegistrationMemberIndex
    | .rejected => .rejected
    | .created _ => .created
    | .selected _ => .selected

theorem registrationPartitionLookup_correct : ∀ i x, registrationPartitionLookup x = i ↔ registrationPartitionRegions i x := by
  intro i x
  cases i <;> cases x <;> simp [registrationPartitionLookup, registrationPartitionRegions]

theorem registrationPartitionLookup_inhabited : ∀ i : RegistrationMemberIndex, ∃ x : RegistrationResult, registrationPartitionLookup x = i := fun
    | .rejected => ⟨.rejected, rfl⟩
    | .created => ⟨.created 0, rfl⟩
    | .selected => ⟨.selected 0, rfl⟩

abbrev registrationPartition : Partition :=
  partitionOfRegions RegistrationResult RegistrationMemberIndex "registrationPartition" registrationPartitionRegions
    (⟨[.rejected, .created, .selected], by intro i; cases i <;> simp⟩) registrationPartitionLookup registrationPartitionLookup_correct
    (by
      intro i
      obtain ⟨x, hx⟩ := registrationPartitionLookup_inhabited i
      exact ⟨x, (registrationPartitionLookup_correct i x).mp hx⟩)
    ⟨.rejected⟩

def register : Operation userPartition registrationPartition where
  run
    | .invalid => some .rejected
    | .validNew => some .created
    | .validExisting => some .selected

abbrev UserStore := Nat → Prop

inductive Channel where | web | api deriving DecidableEq, Repr

instance : MemberEnumeration Channel where
  indices := [.web, .api]
  complete := by intro i; cases i <;> simp

def channelPartitionRegions : Channel → Domain Bool
  | .web => fun x => x = false
  | .api => fun x => x = true

def channelPartitionLookup : Bool → Channel | false => .web | true => .api

theorem channelPartitionLookup_correct : ∀ i x, channelPartitionLookup x = i ↔ channelPartitionRegions i x := by
  intro i x
  cases i <;> cases x <;> simp [channelPartitionLookup, channelPartitionRegions]

theorem channelPartitionLookup_inhabited : ∀ i : Channel, ∃ x : Bool, channelPartitionLookup x = i := fun
    | .web => ⟨false, rfl⟩ | .api => ⟨true, rfl⟩

abbrev channelPartition : Partition :=
  partitionOfRegions Bool Channel "channelPartition" channelPartitionRegions
    (⟨[.web, .api], by intro i; cases i <;> simp⟩) channelPartitionLookup channelPartitionLookup_correct
    (by
      intro i
      obtain ⟨x, hx⟩ := channelPartitionLookup_inhabited i
      exact ⟨x, (channelPartitionLookup_correct i x).mp hx⟩)
    ⟨.web⟩

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

abbrev registerDeclaration : Operation.Declaration where
  source := userPartition
  target := registrationPartition
  operation := register
  BranchName := BranchName
  branchNameDecidableEq := inferInstance
  branchNames := [.invalid, .newUser, .existingUser]
  branchNames_complete := by intro name; cases name <;> simp
  branchNames_nodup := by decide
  branch
    | .invalid => ⟨.invalid, .rejected, rfl⟩
    | .newUser => ⟨.validNew, .created, rfl⟩
    | .existingUser => ⟨.validExisting, .selected, rfl⟩
  responsibilityOwners := ["registration"]
  branchResponsibilityOwners
    | .newUser => some ["user-storage"]
    | _ => none
  implementation := some (.planned {
    primary := { repository := "registration-service", path := "src/registration.ts", symbol := some "register" }
  })
  branchImplementation
    | .invalid => some (.unimplemented "illustrative model; production handler not yet supplied")
    | _ => none

abbrev registrationIdentityDeclaration : Operation.Declaration where
  source := registrationPartition
  target := registrationPartition
  operation := Operation.id registrationPartition
  BranchName := BranchName
  branchNameDecidableEq := inferInstance
  branchNames := [.invalid, .newUser, .existingUser]
  branchNames_complete := by intro name; cases name <;> simp
  branchNames_nodup := by decide
  branch
    | .invalid => ⟨.rejected, .rejected, rfl⟩
    | .newUser => ⟨.created, .created, rfl⟩
    | .existingUser => ⟨.selected, .selected, rfl⟩

abbrev returnToUserDeclaration : Operation.Declaration where
  source := registrationPartition
  target := userPartition
  operation := returnToUser
  BranchName := BranchName
  branchNameDecidableEq := inferInstance
  branchNames := [.invalid, .newUser, .existingUser]
  branchNames_complete := by intro name; cases name <;> simp
  branchNames_nodup := by decide
  branch
    | .invalid => ⟨.rejected, .invalid, rfl⟩
    | .newUser => ⟨.created, .validNew, rfl⟩
    | .existingUser => ⟨.selected, .validExisting, rfl⟩

def operationRegistry : Operation.Registry where
  OperationName := OperationName
  operationNameDecidableEq := inferInstance
  operationNames := [.register, .registrationIdentity, .returnToUser]
  operationNames_complete := by intro name; cases name <;> simp
  operationNames_nodup := by decide
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
The existing-user value and effect contract is indexed by the canonical resolved
branch. The selected ID relation and store premise are separate from the member map.
-/
structure ExistingSelection (branch : Operation.Branch register)
    (before after : UserStore) where
  source_is_existing : branch.source = UserMemberIndex.validExisting
  input : PreclassifiedUserInput
  input_in_branch : userPartition.member branch.source input
  output : RegistrationResult
  output_in_branch : registrationPartition.member branch.target output
  selectedId : Nat
  input_is_selected_id : input = .existingUser selectedId
  selected_was_present : before selectedId
  output_is_selected : output = .selected selectedId
  store_preserved : after = before

structure NewUserCreation (branch : Operation.Branch register)
    (before after : UserStore) where
  source_is_new : branch.source = UserMemberIndex.validNew
  input : PreclassifiedUserInput
  input_in_branch : userPartition.member branch.source input
  output : RegistrationResult
  output_in_branch : registrationPartition.member branch.target output
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

instance : MemberEnumeration Region where
  indices := [.domestic, .international]
  complete := by intro i; cases i <;> simp

def regionPartitionRegions : Region → Domain Bool
  | .domestic => fun x => x = false
  | .international => fun x => x = true

def regionPartitionLookup : Bool → Region | false => .domestic | true => .international

theorem regionPartitionLookup_correct : ∀ i x, regionPartitionLookup x = i ↔ regionPartitionRegions i x := by
  intro i x
  cases i <;> cases x <;> simp [regionPartitionLookup, regionPartitionRegions]

theorem regionPartitionLookup_inhabited : ∀ i : Region, ∃ x : Bool, regionPartitionLookup x = i := fun
    | .domestic => ⟨false, rfl⟩ | .international => ⟨true, rfl⟩

abbrev regionPartition : Partition :=
  partitionOfRegions Bool Region "regionPartition" regionPartitionRegions
    (⟨[.domestic, .international], by intro i; cases i <;> simp⟩) regionPartitionLookup regionPartitionLookup_correct
    (by
      intro i
      obtain ⟨x, hx⟩ := regionPartitionLookup_inhabited i
      exact ⟨x, (regionPartitionLookup_correct i x).mp hx⟩)
    ⟨.domestic⟩

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

end ArchiScriptExamples.UserRegistration
