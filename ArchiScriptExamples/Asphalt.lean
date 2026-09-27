import ArchiScript

/-!
An adversarial *admission* slice, not a model of the whole control plane.
The classifier decides which architectural action is requested from a fixed
observation. It does not grant a lease, reserve capacity, prove provider state,
or authorize a production mutation. See benchmarks/asphalt/README.md.
-/
namespace ArchiScriptExamples.Asphalt
open ArchiScript

/-! Carrier provenance probe: the upstream universe is all signed counts.
The downstream Nat carrier is justified only for values emitted by a contract
that rejects negative counts. This is not a runtime decoder conformance proof. -/
inductive CountMember where
  | negative | nonnegative
  deriving DecidableEq

def countMembers : CountMember → Domain Int
  | .negative => fun x => x < 0
  | .nonnegative => fun x => 0 ≤ x

def countPartition : Partition where
  Carrier := Int
  MemberIndex := CountMember
  carrierNonempty := ⟨0⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.negative, .nonnegative]
  memberIndices_complete := by intro i; cases i <;> simp
  classify x := if x < 0 then .negative else .nonnegative
  member_inhabited
    | .negative => ⟨-1, by decide⟩
    | .nonnegative => ⟨0, by decide⟩

def countSemanticPartition : SemanticPartition where
  partition := countPartition
  members := countMembers
  hasMembers := by
    intro i x
    cases i
    · simp [Partition.member, countPartition, countMembers]
    · simp [Partition.member, countPartition, countMembers]
      omega

def decodeNatural (x : Int) : Option Nat :=
  if 0 ≤ x then some x.toNat else none

theorem decodeNatural_only_nonnegative (x : Int) (n : Nat)
    (h : decodeNatural x = some n) : countMembers .nonnegative x := by
  by_cases hx : 0 ≤ x
  · exact hx
  · simp [decodeNatural, hx] at h

theorem decodeNatural_covers_carrier (n : Nat) :
    ∃ x : Int, decodeNatural x = some n := by
  refine ⟨Int.ofNat n, ?_⟩
  simp [decodeNatural]

def naturalCarrierProvenance : CarrierProvenance Nat :=
  .derived "Asphalt.countPartition" "Asphalt.countPartition.nonnegative"
    countSemanticPartition
    (.externalRoot {
      source := "Asphalt signed-count fixture"
      scope := "all signed request counts before decoding"
      claim := "The fixture supplies Int counts, including negative values"
      revision := "benchmark-slice-1"
      identified := by decide
    })
    .nonnegative decodeNatural
    decodeNatural_only_nonnegative decodeNatural_covers_carrier

/-- A decoder that maps negative values to naturals cannot claim this source
member. The counterexample is the missing boundary case. -/
theorem absoluteValue_decoder_is_not_narrowing :
    ¬ ∀ x n, (some x.natAbs : Option Nat) = some n →
      countMembers .nonnegative x := by
  intro h
  have hneg := h (-1) 1 (by decide)
  simp [countMembers] at hneg

structure Identity where
  requestId : String
  logicalDeploymentId : String
  attemptId : String
  tenantId : String
  serviceId : String
  environmentId : String
  artifactDigest : String
  approvedDigest : String
  deriving Repr

structure Retry where
  attemptNumber : Nat
  maxAttempts : Nat
  previousAttemptId : Option String
  nextRetryAt : Nat
  budgetRemaining : Nat
  deriving Repr

structure LeaseObservation where
  ownerId : String
  attemptId : String
  observedEpoch : Nat
  resourceEpoch : Nat
  expiresAt : Nat
  observedAt : Nat
  deriving Repr

structure Revisions where
  policy : Nat
  approvedPolicy : Nat
  infrastructure : Nat
  network : Nat
  analyzedNetwork : Option Nat
  iam : Nat
  secrets : Nat
  schema : Nat
  requiredSchema : Nat
  deriving Repr

structure CapacityObservation where
  observedCpu : Nat
  observedMemory : Nat
  observedIps : Nat
  requestedCpu : Nat
  requestedMemory : Nat
  requestedIps : Nat
  reservationId : Option String
  deriving Repr

structure Input where
  identity : Identity
  retry : Retry
  lease : LeaseObservation
  revisions : Revisions
  capacity : CapacityObservation
  now : Nat
  currentlyDeployedDigest : String
  superseded : Bool
  rollbackCompatible : Bool
  -- These are observations with provenance, not trusted truth values.
  ciResultId : Option String
  scanResultId : Option String
  approvalRevision : Option String
  regionalHealthObservationId : Option String
  deriving Repr

def validIdentity (x : Input) : Prop :=
  x.identity.requestId ≠ "" ∧ x.identity.logicalDeploymentId ≠ "" ∧
  x.identity.attemptId ≠ "" ∧ x.identity.tenantId ≠ "" ∧
  x.identity.serviceId ≠ "" ∧ x.identity.environmentId ≠ ""

def alreadySatisfied (x : Input) : Prop :=
  x.currentlyDeployedDigest = x.identity.artifactDigest

def fenced (x : Input) : Prop :=
  x.lease.attemptId = x.identity.attemptId ∧
  x.lease.observedEpoch = x.lease.resourceEpoch ∧
  x.now < x.lease.expiresAt ∧ x.lease.observedAt ≤ x.now

def approvalMatches (x : Input) : Prop :=
  x.identity.artifactDigest ≠ "" ∧
  x.identity.artifactDigest = x.identity.approvedDigest ∧
  x.revisions.policy = x.revisions.approvedPolicy ∧
  x.approvalRevision.isSome

def migrationCompatible (x : Input) : Prop :=
  x.revisions.schema ≥ x.revisions.requiredSchema ∧ x.rollbackCompatible = true

def retryPermitted (x : Input) : Prop :=
  x.retry.attemptNumber < x.retry.maxAttempts ∧
  x.retry.budgetRemaining > 0

def retryDue (x : Input) : Prop := x.retry.nextRetryAt ≤ x.now

/-- These are only references to checks. Their existence does not establish a pass. -/
def evidenceAddressable (x : Input) : Prop :=
  x.ciResultId.isSome ∧ x.scanResultId.isSome ∧
  x.regionalHealthObservationId.isSome ∧
  x.revisions.analyzedNetwork = some x.revisions.network

instance (x : Input) : Decidable (validIdentity x) := by
  unfold validIdentity
  infer_instance
instance (x : Input) : Decidable (alreadySatisfied x) := by
  unfold alreadySatisfied
  infer_instance
instance (x : Input) : Decidable (fenced x) := by
  unfold fenced
  infer_instance
instance (x : Input) : Decidable (approvalMatches x) := by
  unfold approvalMatches
  infer_instance
instance (x : Input) : Decidable (migrationCompatible x) := by
  unfold migrationCompatible
  infer_instance
instance (x : Input) : Decidable (retryPermitted x) := by
  unfold retryPermitted
  infer_instance
instance (x : Input) : Decidable (retryDue x) := by
  unfold retryDue
  infer_instance
instance (x : Input) : Decidable (evidenceAddressable x) := by
  unfold evidenceAddressable
  infer_instance

inductive Admission where
  | malformed | satisfied | superseded | staleAuthority | staleApproval
  | migrationUnsafe | retryExhausted | retryDelayed | evidenceUnknown
  | requestReservation
  deriving DecidableEq, Repr

private def exampleInput : Input where
  identity := ⟨"request", "logical", "attempt", "tenant", "service", "prod", "sha256:a", "sha256:a"⟩
  retry := ⟨0, 3, none, 0, 3⟩
  lease := ⟨"worker", "attempt", 11, 11, 100, 0⟩
  revisions := ⟨2, 2, 4, 5, some 5, 3, 8, 42, 42⟩
  capacity := ⟨8, 16, 4, 2, 4, 3, none⟩
  now := 1
  currentlyDeployedDigest := "sha256:old"
  superseded := false
  rollbackCompatible := true
  ciResultId := some "ci-1"
  scanResultId := some "scan-1"
  approvalRevision := some "approval-1"
  regionalHealthObservationId := some "health-1"

def classify (x : Input) : Admission :=
  if ¬ validIdentity x then .malformed
  else if alreadySatisfied x then .satisfied
  else if x.superseded then .superseded
  else if ¬ fenced x then .staleAuthority
  else if ¬ approvalMatches x then .staleApproval
  else if ¬ migrationCompatible x then .migrationUnsafe
  else if ¬ retryPermitted x then .retryExhausted
  else if ¬ retryDue x then .retryDelayed
  else if ¬ evidenceAddressable x then .evidenceUnknown
  else .requestReservation

def admissionPartition : Partition where
  Carrier := Input
  MemberIndex := Admission
  carrierNonempty := ⟨exampleInput⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.malformed, .satisfied, .superseded, .staleAuthority,
    .staleApproval, .migrationUnsafe, .retryExhausted, .retryDelayed,
    .evidenceUnknown, .requestReservation]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := classify
  member_inhabited := by
    intro i
    cases i
    · exact ⟨{ exampleInput with identity := { exampleInput.identity with requestId := "" } }, by decide⟩
    · exact ⟨{ exampleInput with currentlyDeployedDigest := "sha256:a" }, by decide⟩
    · exact ⟨{ exampleInput with superseded := true }, by decide⟩
    · exact ⟨{ exampleInput with lease := { exampleInput.lease with resourceEpoch := 12 } }, by decide⟩
    · exact ⟨{ exampleInput with revisions := { exampleInput.revisions with policy := 3 } }, by decide⟩
    · exact ⟨{ exampleInput with rollbackCompatible := false }, by decide⟩
    · exact ⟨{ exampleInput with retry := { exampleInput.retry with budgetRemaining := 0 } }, by decide⟩
    · exact ⟨{ exampleInput with retry := { exampleInput.retry with nextRetryAt := 20 } }, by decide⟩
    · exact ⟨{ exampleInput with scanResultId := none }, by decide⟩
    · exact ⟨exampleInput, by decide⟩

/-! Independent predicates state the precedence used by this consumer. -/
def admissionMembers : Admission → Domain Input
  | .malformed => fun x => ¬ validIdentity x
  | .satisfied => fun x => validIdentity x ∧ alreadySatisfied x
  | .superseded => fun x => validIdentity x ∧ ¬ alreadySatisfied x ∧ x.superseded = true
  | .staleAuthority => fun x => validIdentity x ∧ ¬ alreadySatisfied x ∧
      x.superseded = false ∧ ¬ fenced x
  | .staleApproval => fun x => validIdentity x ∧ ¬ alreadySatisfied x ∧
      x.superseded = false ∧ fenced x ∧ ¬ approvalMatches x
  | .migrationUnsafe => fun x => validIdentity x ∧ ¬ alreadySatisfied x ∧
      x.superseded = false ∧ fenced x ∧ approvalMatches x ∧ ¬ migrationCompatible x
  | .retryExhausted => fun x => validIdentity x ∧ ¬ alreadySatisfied x ∧
      x.superseded = false ∧ fenced x ∧ approvalMatches x ∧ migrationCompatible x ∧
      ¬ retryPermitted x
  | .retryDelayed => fun x => validIdentity x ∧ ¬ alreadySatisfied x ∧
      x.superseded = false ∧ fenced x ∧ approvalMatches x ∧ migrationCompatible x ∧
      retryPermitted x ∧ ¬ retryDue x
  | .evidenceUnknown => fun x => validIdentity x ∧ ¬ alreadySatisfied x ∧
      x.superseded = false ∧ fenced x ∧ approvalMatches x ∧ migrationCompatible x ∧
      retryPermitted x ∧ retryDue x ∧ ¬ evidenceAddressable x
  | .requestReservation => fun x => validIdentity x ∧ ¬ alreadySatisfied x ∧
      x.superseded = false ∧ fenced x ∧ approvalMatches x ∧ migrationCompatible x ∧
      retryPermitted x ∧ retryDue x ∧ evidenceAddressable x

theorem admission_has_members : admissionPartition.HasMembers admissionMembers := by
  intro i x
  by_cases h₁ : validIdentity x
  · by_cases h₂ : alreadySatisfied x
    · cases i <;> simp [Partition.member, admissionPartition, classify,
        admissionMembers, h₁, h₂]
    · cases h₃ : x.superseded
      · by_cases h₄ : fenced x
        · by_cases h₅ : approvalMatches x
          · by_cases h₆ : migrationCompatible x
            · by_cases h₇ : retryPermitted x
              · by_cases h₈ : retryDue x
                · by_cases h₉ : evidenceAddressable x
                  · cases i <;> simp [Partition.member, admissionPartition, classify,
                      admissionMembers, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉]
                  · cases i <;> simp [Partition.member, admissionPartition, classify,
                      admissionMembers, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉]
                · cases i <;> simp [Partition.member, admissionPartition, classify,
                    admissionMembers, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
              · cases i <;> simp [Partition.member, admissionPartition, classify,
                  admissionMembers, h₁, h₂, h₃, h₄, h₅, h₆, h₇]
            · cases i <;> simp [Partition.member, admissionPartition, classify,
                admissionMembers, h₁, h₂, h₃, h₄, h₅, h₆]
          · cases i <;> simp [Partition.member, admissionPartition, classify,
              admissionMembers, h₁, h₂, h₃, h₄, h₅]
        · cases i <;> simp [Partition.member, admissionPartition, classify,
            admissionMembers, h₁, h₂, h₃, h₄]
      · cases i <;> simp [Partition.member, admissionPartition, classify,
          admissionMembers, h₁, h₂, h₃]
  · cases i <;> simp [Partition.member, admissionPartition, classify,
      admissionMembers, h₁]

def admissionSemanticPartition : SemanticPartition where
  partition := admissionPartition
  members := admissionMembers
  hasMembers := admission_has_members

/-- No formula for the actual security service's pass relation is available.
This supporting subdomain is deliberately opaque and does not authorize a
deployment. `scanResultId.isSome` remains only addressability. -/
opaque externalScanPasses : Domain Input := fun _ => True

def admissionArchitecture : ArchitecturalPartition where
  partition := admissionPartition
  carrierProvenance := .externalRoot {
    source := "Asphalt admission fixture"
    scope := "fixed Input observation, excluding open B-01 through B-23 facts"
    claim := "The fixture supplies the modeled observation structure"
    revision := "benchmark-slice-1"
    identified := by decide
  }
  selectedMembers := fun i => {
    meaning := admissionMembers i
    definition := .formula "precedence predicate over the fixed admission observation"
  }
  supportingSubdomains := [{
    name := "externalScanPasses"
    base := fun _ => True
    meaning := externalScanPasses
    contained := by intro _ _; trivial
    definition := .opaque "Security service result semantics are not imported or verified"
  }]
  hasMembers := admission_has_members

inductive NextAction where
  | rejectInput | acknowledgeCurrent | discardOldAttempt | reacquireAuthority
  | seekApproval | requireMigrationReview | stopRetry | waitRetry
  | obtainEvidence | attemptAtomicReservation
  deriving DecidableEq, Repr

def nextActionPartition : Partition where
  Carrier := NextAction
  MemberIndex := NextAction
  carrierNonempty := ⟨.rejectInput⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.rejectInput, .acknowledgeCurrent, .discardOldAttempt,
    .reacquireAuthority, .seekApproval, .requireMigrationReview, .stopRetry,
    .waitRetry, .obtainEvidence, .attemptAtomicReservation]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def nextActionSemanticPartition : SemanticPartition where
  partition := nextActionPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

def decideAdmission : Operation admissionPartition nextActionPartition where
  run
    | .malformed => some .rejectInput
    | .satisfied => some .acknowledgeCurrent
    | .superseded => some .discardOldAttempt
    | .staleAuthority => some .reacquireAuthority
    | .staleApproval => some .seekApproval
    | .migrationUnsafe => some .requireMigrationReview
    | .retryExhausted => some .stopRetry
    | .retryDelayed => some .waitRetry
    | .evidenceUnknown => some .obtainEvidence
    | .requestReservation => some .attemptAtomicReservation

/-- Canonical handoff identities exist even while implementation is unresolved. -/
def admissionDeclaration : Operation.Declaration where
  source := admissionPartition
  target := nextActionPartition
  operation := decideAdmission
  BranchName := Admission
  branchNameDecidableEq := inferInstance
  branchNames := [.malformed, .satisfied, .superseded, .staleAuthority,
    .staleApproval, .migrationUnsafe, .retryExhausted, .retryDelayed,
    .evidenceUnknown, .requestReservation]
  branchNames_complete := by intro i; cases i <;> simp
  branchNames_nodup := by decide
  branch
    | .malformed => ⟨.malformed, .rejectInput, rfl⟩
    | .satisfied => ⟨.satisfied, .acknowledgeCurrent, rfl⟩
    | .superseded => ⟨.superseded, .discardOldAttempt, rfl⟩
    | .staleAuthority => ⟨.staleAuthority, .reacquireAuthority, rfl⟩
    | .staleApproval => ⟨.staleApproval, .seekApproval, rfl⟩
    | .migrationUnsafe => ⟨.migrationUnsafe, .requireMigrationReview, rfl⟩
    | .retryExhausted => ⟨.retryExhausted, .stopRetry, rfl⟩
    | .retryDelayed => ⟨.retryDelayed, .waitRetry, rfl⟩
    | .evidenceUnknown => ⟨.evidenceUnknown, .obtainEvidence, rfl⟩
    | .requestReservation => ⟨.requestReservation, .attemptAtomicReservation, rfl⟩
  responsibilityOwners := ["deployment-control-plane"]
  implementation := some (.unimplemented
    "benchmark candidate; no source resolution or implementation conformance claimed")

inductive OperationName where
  | decideAdmission
  deriving DecidableEq

def operationRegistry : Operation.Registry where
  OperationName := OperationName
  operationNameDecidableEq := inferInstance
  operationNames := [.decideAdmission]
  operationNames_complete := by intro i; cases i; simp
  operationNames_nodup := by simp
  resolve
    | .decideAdmission => admissionDeclaration

#guard admissionDeclaration.definedMappingsWithoutBranch.length == 0
#guard operationRegistry.branchAddresses.length == 10

theorem stale_epoch_changes_admission :
    classify exampleInput = .requestReservation ∧
    classify { exampleInput with lease := { exampleInput.lease with resourceEpoch := 12 } } =
      .staleAuthority := by decide

theorem mutable_tag_cannot_substitute_digest :
    classify { exampleInput with identity := { exampleInput.identity with
      artifactDigest := "sha256:other" } } = .staleApproval := by decide

/-- A deliberately adverse result: a reference named `failed` is still only a
reference. This model cannot inspect its result and must not claim eligibility. -/
theorem scan_reference_can_hide_failure :
    classify { exampleInput with scanResultId := some "scan-failed" } =
      .requestReservation := by decide

/-- This is a counterexample to using observed free IPs as a reservation guarantee. -/
theorem observed_capacity_does_not_cover_two_requests : 3 ≤ 4 ∧ 2 ≤ 4 ∧ ¬ (3 + 2 ≤ 4) := by
  omega

end ArchiScriptExamples.Asphalt
