import ArchiScript

/-!
A compact stress example for ArchiScript's architecture calculus.

The same logical reservation resource is observed by three independently
available triggers. The user path also tensors independent request, inventory,
and state factors and tensors the corresponding local member maps.

The model deliberately separates:
* semantic next-state selection,
* persistence commands,
* outbox commands,
* inventory commands.

All are ordinary member-level Operations. None proves that a runtime side
effect executed successfully.

The payment and expiry paths can both observe Held and request incompatible
updates. That is a concrete concurrency review boundary, not a Lean proof of a
race.
-/
namespace ArchiScriptExamples.ReservationController
open ArchiScript

inductive UserTrigger where
  | malformed
  | reserve
  | cancel
  deriving DecidableEq, Repr

def userTriggerPartition : Partition where
  Carrier := UserTrigger
  MemberIndex := UserTrigger
  carrierNonempty := ⟨.malformed⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.malformed, .reserve, .cancel]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

inductive UserIntent where
  | reserve
  | cancel
  deriving DecidableEq, Repr

def userIntentPartition : Partition where
  Carrier := UserIntent
  MemberIndex := UserIntent
  carrierNonempty := ⟨.reserve⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.reserve, .cancel]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/-- Malformed input has no architectural user intent. -/
def parseUser : Operation userTriggerPartition userIntentPartition where
  run
    | .malformed => none
    | .reserve => some .reserve
    | .cancel => some .cancel

inductive InventoryObservation where
  | unavailable
  | available
  deriving DecidableEq, Repr

def inventoryObservationPartition : Partition where
  Carrier := InventoryObservation
  MemberIndex := InventoryObservation
  carrierNonempty := ⟨.unavailable⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.unavailable, .available]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

inductive InventoryPlan where
  | blocked
  | canHold
  deriving DecidableEq, Repr

def inventoryPlanPartition : Partition where
  Carrier := InventoryPlan
  MemberIndex := InventoryPlan
  carrierNonempty := ⟨.blocked⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.blocked, .canHold]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def planInventory :
    Operation inventoryObservationPartition inventoryPlanPartition where
  run
    | .unavailable => some .blocked
    | .available => some .canHold

inductive ReservationState where
  | empty
  | held
  | paid
  | cancelled
  | expired
  deriving DecidableEq, Repr

def reservationStatePartition : Partition where
  Carrier := ReservationState
  MemberIndex := ReservationState
  carrierNonempty := ⟨.empty⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.empty, .held, .paid, .cancelled, .expired]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

inductive ReservationMutation where
  | hold
  | markPaid
  | cancel
  | expire
  deriving DecidableEq, Repr

def reservationMutationPartition : Partition where
  Carrier := ReservationMutation
  MemberIndex := ReservationMutation
  carrierNonempty := ⟨.hold⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.hold, .markPaid, .cancel, .expire]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/-- Raw user/inventory/state observation context: 3 × 2 × 5 = 30 members. -/
def userContextPartition : Partition :=
  (userTriggerPartition.tensor inventoryObservationPartition).tensor
    reservationStatePartition

/-- The corresponding normalized local-plan context. -/
def userDecisionContextPartition : Partition :=
  (userIntentPartition.tensor inventoryPlanPartition).tensor
    reservationStatePartition

/-- Tensor the independent local maps and carry state unchanged in its own slot. -/
def prepareUserContext :
    Operation userContextPartition userDecisionContextPartition :=
  (parseUser.tensor planInventory).tensor (Operation.id reservationStatePartition)

/-- Cross-factor policy starts only after the independent factors are explicit. -/
def decideUserMutation :
    Operation userDecisionContextPartition reservationMutationPartition where
  run
    | ((.reserve, .canHold), .empty) => some .hold
    | ((.cancel, _), .held) => some .cancel
    | _ => none

def planUserMutation :
    Operation userContextPartition reservationMutationPartition :=
  decideUserMutation.comp prepareUserContext

inductive PaymentTrigger where
  | authorized
  | failed
  deriving DecidableEq, Repr

def paymentTriggerPartition : Partition where
  Carrier := PaymentTrigger
  MemberIndex := PaymentTrigger
  carrierNonempty := ⟨.authorized⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.authorized, .failed]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def paymentContextPartition : Partition :=
  paymentTriggerPartition.tensor reservationStatePartition

/-- Payment webhook decisions observe the same ReservationState VDP. -/
def planPaymentMutation :
    Operation paymentContextPartition reservationMutationPartition where
  run
    | (.authorized, .held) => some .markPaid
    | (.failed, .held) => some .cancel
    | _ => none

inductive ExpiryTrigger where
  | fired
  deriving DecidableEq, Repr

def expiryTriggerPartition : Partition where
  Carrier := ExpiryTrigger
  MemberIndex := ExpiryTrigger
  carrierNonempty := ⟨.fired⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.fired]
  memberIndices_complete := by intro i; cases i; simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def expiryContextPartition : Partition :=
  expiryTriggerPartition.tensor reservationStatePartition

/-- Expiry is independently available from the payment webhook. -/
def planExpiryMutation :
    Operation expiryContextPartition reservationMutationPartition where
  run
    | (.fired, .held) => some .expire
    | _ => none

/--
The controller has exactly three design-time entry channels. Their runtime
carriers remain complete inside each summand; coproduct only aggregates the
already-established architectural alternatives.
-/
def controllerInputPartition : Partition :=
  (userContextPartition.coproduct paymentContextPartition).coproduct
    expiryContextPartition

/--
One canonical controller operation is obtained by copairing the three existing
entry-specific planners. No behavior is added or inferred by the coproduct.
-/
def planControllerMutation :
    Operation controllerInputPartition reservationMutationPartition :=
  Operation.copair
    (Operation.copair planUserMutation planPaymentMutation)
    planExpiryMutation

/-- Pure semantic next-state contract. This is not persistence. -/
def nextReservationState :
    Operation reservationMutationPartition reservationStatePartition where
  run
    | .hold => some .held
    | .markPaid => some .paid
    | .cancel => some .cancelled
    | .expire => some .expired

inductive ReservationWrite where
  | setHeld
  | setPaid
  | setCancelled
  | setExpired
  deriving DecidableEq, Repr

def reservationWritePartition : Partition where
  Carrier := ReservationWrite
  MemberIndex := ReservationWrite
  carrierNonempty := ⟨.setHeld⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.setHeld, .setPaid, .setCancelled, .setExpired]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/-- Every member denotes a write request against the same logical reservation record. -/
def persistMutation :
    Operation reservationMutationPartition reservationWritePartition where
  run
    | .hold => some .setHeld
    | .markPaid => some .setPaid
    | .cancel => some .setCancelled
    | .expire => some .setExpired

inductive OutboxMessage where
  | requestPayment
  | reservationPaid
  | reservationCancelled
  | reservationExpired
  deriving DecidableEq, Repr

def outboxMessagePartition : Partition where
  Carrier := OutboxMessage
  MemberIndex := OutboxMessage
  carrierNonempty := ⟨.requestPayment⟩
  memberIndexDecidableEq := inferInstance
  memberIndices :=
    [.requestPayment, .reservationPaid, .reservationCancelled, .reservationExpired]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/--
Publishing is another ordinary outgoing member map from ReservationMutation.
Together with persistence, next-state selection, and inventory intent this is
fan-out: no execution order between the sibling operations is modeled. They may
be implemented sequentially or in parallel; only an explicit path through an
intermediate VDP would state sequential composition.
-/
def publishMutation :
    Operation reservationMutationPartition outboxMessagePartition where
  run
    | .hold => some .requestPayment
    | .markPaid => some .reservationPaid
    | .cancel => some .reservationCancelled
    | .expire => some .reservationExpired

inductive InventoryCommand where
  | reserveUnits
  | releaseUnits
  deriving DecidableEq, Repr

def inventoryCommandPartition : Partition where
  Carrier := InventoryCommand
  MemberIndex := InventoryCommand
  carrierNonempty := ⟨.reserveUnits⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.reserveUnits, .releaseUnits]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/-- Not every reservation mutation has an inventory side-effect request. -/
def inventoryEffect :
    Operation reservationMutationPartition inventoryCommandPartition where
  run
    | .hold => some .reserveUnits
    | .cancel | .expire => some .releaseUnits
    | .markPaid => none

inductive InventoryMutationView where
  | reserve
  | noCommand
  | release
  deriving DecidableEq, Repr

/--
A lower-resolution view of the same ReservationMutation carrier. It forgets
distinctions that are irrelevant to the inventory consumer only.
-/
def inventoryMutationViewPartition : Partition where
  Carrier := ReservationMutation
  MemberIndex := InventoryMutationView
  carrierNonempty := ⟨.hold⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.reserve, .noCommand, .release]
  memberIndices_complete := by intro i; cases i <;> simp
  classify
    | .hold => .reserve
    | .markPaid => .noCommand
    | .cancel | .expire => .release
  member_inhabited
    | .reserve => ⟨.hold, rfl⟩
    | .noCommand => ⟨.markPaid, rfl⟩
    | .release => ⟨.cancel, rfl⟩

def mutationToInventoryView :
    reservationMutationPartition.MemberIndex →
      inventoryMutationViewPartition.MemberIndex
  | .hold => .reserve
  | .markPaid => .noCommand
  | .cancel | .expire => .release

theorem reservationMutation_refines_inventoryView :
    reservationMutationPartition.RefinesVia
      inventoryMutationViewPartition mutationToInventoryView := by
  refine ⟨rfl, ?_⟩
  intro i mutation hx
  change reservationMutationPartition.classify mutation = i at hx
  cases hx
  cases mutation <;> rfl

def forgetInventoryMutationDetail :
    Operation reservationMutationPartition inventoryMutationViewPartition :=
  Partition.coarseningOperation mutationToInventoryView

def inventoryEffectAtCoarseResolution :
    Operation inventoryMutationViewPartition inventoryCommandPartition where
  run
    | .reserve => some .reserveUnits
    | .noCommand => none
    | .release => some .releaseUnits

theorem inventoryEffect_factorizes :
    inventoryEffectAtCoarseResolution.comp forgetInventoryMutationDetail =
      inventoryEffect := by
  apply Operation.ext
  intro mutation
  cases mutation <;> rfl

theorem inventoryEffect_factorsThrough :
    Operation.FactorsThrough forgetInventoryMutationDetail inventoryEffect :=
  ⟨inventoryEffectAtCoarseResolution, inventoryEffect_factorizes⟩

/--
The same coarsening is not valid for the outbox consumer: cancel and expire are
merged by the inventory view but publish different messages.
-/
theorem publishMutation_does_not_factorThrough_inventoryView :
    ¬ Operation.FactorsThrough forgetInventoryMutationDetail publishMutation := by
  intro h
  have constant := Operation.factorsThrough_constantOnFibers h
  have bad := constant .cancel .expire (by rfl)
  change
    (some OutboxMessage.reservationCancelled : Option OutboxMessage) =
      some OutboxMessage.reservationExpired at bad
  have impossible :
      (some OutboxMessage.reservationCancelled : Option OutboxMessage) ≠
        some OutboxMessage.reservationExpired := by
    decide
  exact impossible bad

/-- Independently sourced paths all produce expected updates of the same state VDP. -/
def userStateUpdate :
    Operation userContextPartition reservationStatePartition :=
  nextReservationState.comp planUserMutation

def paymentStateUpdate :
    Operation paymentContextPartition reservationStatePartition :=
  nextReservationState.comp planPaymentMutation

def expiryStateUpdate :
    Operation expiryContextPartition reservationStatePartition :=
  nextReservationState.comp planExpiryMutation

/-- Independently sourced paths also converge on writes to the same logical resource. -/
def userWrite :
    Operation userContextPartition reservationWritePartition :=
  persistMutation.comp planUserMutation

def paymentWrite :
    Operation paymentContextPartition reservationWritePartition :=
  persistMutation.comp planPaymentMutation

def expiryWrite :
    Operation expiryContextPartition reservationWritePartition :=
  persistMutation.comp planExpiryMutation

/-!
0.5.0 expression-presentation stress coverage.

The Operations above remain the semantic category. The declarations below keep
selected presentation syntax without changing any VDP or Operation identity.
Every expression has one source and one target; the family groups several
consequences of one controller source without tensoring the outputs together.
-/

def prepareUserContextExpression :
    Expression userContextPartition userDecisionContextPartition :=
  .tensor
    (.tensor (.atom parseUser) (.atom planInventory))
    (.identity reservationStatePartition)

def planUserMutationExpression :
    Expression userContextPartition reservationMutationPartition :=
  .comp (.atom decideUserMutation) prepareUserContextExpression

def planPaymentMutationExpression :
    Expression paymentContextPartition reservationMutationPartition :=
  .atom planPaymentMutation

def planExpiryMutationExpression :
    Expression expiryContextPartition reservationMutationPartition :=
  .atom planExpiryMutation

/--
The controller expression keeps the actual tensor/composition/coproduct
presentation instead of wrapping the already-composed semantic Operation as one
opaque atom.
-/
def controllerPlanExpression :
    Expression controllerInputPartition reservationMutationPartition :=
  .copair
    (.copair planUserMutationExpression planPaymentMutationExpression)
    planExpiryMutationExpression

example :
    Expression.denote prepareUserContextExpression = prepareUserContext := rfl

example :
    Expression.denote planUserMutationExpression = planUserMutation := rfl

example :
    Expression.denote controllerPlanExpression = planControllerMutation := rfl

def controllerStateExpression :
    Expression controllerInputPartition reservationStatePartition :=
  .comp (.atom nextReservationState) controllerPlanExpression

def controllerWriteExpression :
    Expression controllerInputPartition reservationWritePartition :=
  .comp (.atom persistMutation) controllerPlanExpression

def controllerPublishExpression :
    Expression controllerInputPartition outboxMessagePartition :=
  .comp (.atom publishMutation) controllerPlanExpression

def controllerInventoryExpression :
    Expression controllerInputPartition inventoryCommandPartition :=
  .comp (.atom inventoryEffect) controllerPlanExpression

/--
One source, several selected consequence expressions. This is architectural
fan-out in the presentation, not `Operation.tensor`: no order or parallel
runtime schedule is asserted between the sibling consequences.
-/
def controllerExpressionFamily : Expression.Family where
  source := controllerInputPartition
  expressions := [
    { target := reservationMutationPartition, expression := controllerPlanExpression },
    { target := reservationStatePartition, expression := controllerStateExpression },
    { target := reservationWritePartition, expression := controllerWriteExpression },
    { target := outboxMessagePartition, expression := controllerPublishExpression },
    { target := inventoryCommandPartition, expression := controllerInventoryExpression }
  ]
  nonempty := by simp

example :
    Expression.denote controllerStateExpression =
      nextReservationState.comp planControllerMutation := rfl

example :
    Expression.denote controllerPublishExpression =
      publishMutation.comp planControllerMutation := rfl

/--
A branch-relative coproduct simplification. The unused payment branch disappears
from this selected expression by the coproduct law; the payment VDP and planner
remain in the architecture and may be used by other expressions.
-/
def userSelectedCoproductNormalization :
    Expression.Rewrite
      (.comp
        (.copair
          planUserMutationExpression
          planPaymentMutationExpression)
        (.coproductInl userContextPartition paymentContextPartition))
      planUserMutationExpression :=
  Expression.Rewrite.copair_inl
    planUserMutationExpression
    planPaymentMutationExpression

def paymentSelectedCoproductNormalization :
    Expression.Rewrite
      (.comp
        (.copair
          planUserMutationExpression
          planPaymentMutationExpression)
        (.coproductInr userContextPartition paymentContextPartition))
      planPaymentMutationExpression :=
  Expression.Rewrite.copair_inr
    planUserMutationExpression
    planPaymentMutationExpression

/--
The first two controller channels expose the shared ReservationState coordinate:

  ((UserTrigger ⊗ InventoryObservation) ⊗ ReservationState)
    ⊕ (PaymentTrigger ⊗ ReservationState)

is canonically isomorphic to

  ((UserTrigger ⊗ InventoryObservation) ⊕ PaymentTrigger)
    ⊗ ReservationState.

This is structural factoring only. It does not claim one database read,
transaction, cache entry, or runtime object for ReservationState.

Both sides are kept as structural expressions rather than introduced as new
named VDP declarations. The existing UserContext and PaymentContext nominal
VDPs remain present; this witness only supplies an isomorphic presentation of
their coproduct source.
-/
def userPaymentSourceIso :
    Partition.PartitionIso
      (userContextPartition.coproduct paymentContextPartition)
      (((userTriggerPartition.tensor inventoryObservationPartition).coproduct
          paymentTriggerPartition).tensor reservationStatePartition) :=
  Partition.tensorCoproductRightDistributivity
    (userTriggerPartition.tensor inventoryObservationPartition)
    paymentTriggerPartition
    reservationStatePartition

def userPaymentPlanExpression :
    Expression (userContextPartition.coproduct paymentContextPartition)
      reservationMutationPartition :=
  .copair
    planUserMutationExpression
    planPaymentMutationExpression

def userPaymentFactoredPlanExpression :
    Expression
      (((userTriggerPartition.tensor inventoryObservationPartition).coproduct
          paymentTriggerPartition).tensor reservationStatePartition)
      reservationMutationPartition :=
  .comp userPaymentPlanExpression (.iso userPaymentSourceIso.symm)

/-- The factored source presentation commutes with the original planner. -/
def userPaymentFactoringCertificate :
    Expression.Transport userPaymentPlanExpression
      userPaymentFactoredPlanExpression :=
  Expression.Transport.source userPaymentPlanExpression userPaymentSourceIso

example :
    userPaymentFactoringCertificate.targetIso.toOperation.comp
        (Expression.denote userPaymentPlanExpression) =
      (Expression.denote userPaymentFactoredPlanExpression).comp
        userPaymentFactoringCertificate.sourceIso.toOperation :=
  userPaymentFactoringCertificate.commutes

/--
Composition can denote an end-to-end controller result while the nominal
ReservationMutation VDP still exists. A diagram that intentionally hides that
intermediate VDP is an architecture projection of the view, not a normalization
step that deleted the object from the category.
-/
def projectedControllerStateOperation :
    Operation controllerInputPartition reservationStatePartition :=
  Expression.denote controllerStateExpression

#guard userContextPartition.memberIndices.length == 30

#guard prepareUserContext ((.reserve, .available), .empty) ==
  some ((.reserve, .canHold), .empty)
#guard prepareUserContext ((.malformed, .available), .empty) == none

#guard planUserMutation ((.reserve, .available), .empty) == some .hold
#guard planUserMutation ((.reserve, .unavailable), .empty) == none
#guard planUserMutation ((.cancel, .unavailable), .held) == some .cancel

#guard planControllerMutation (.inl (.inl ((.reserve, .available), .empty))) ==
  some .hold
#guard planControllerMutation (.inl (.inr (.authorized, .held))) ==
  some .markPaid
#guard planControllerMutation (.inr (.fired, .held)) == some .expire

-- Concrete concurrency-review witness: both paths can observe Held and disagree.
#guard planPaymentMutation (.authorized, .held) == some .markPaid
#guard planExpiryMutation (.fired, .held) == some .expire

#guard paymentStateUpdate (.authorized, .held) == some .paid
#guard expiryStateUpdate (.fired, .held) == some .expired

#guard paymentWrite (.authorized, .held) == some .setPaid
#guard expiryWrite (.fired, .held) == some .setExpired

#guard publishMutation .markPaid == some .reservationPaid
#guard inventoryEffect .markPaid == none
#guard inventoryEffect .expire == some .releaseUnits

#guard forgetInventoryMutationDetail .cancel == some .release
#guard forgetInventoryMutationDetail .expire == some .release
#guard (Operation.firstFiberConflict
  forgetInventoryMutationDetail inventoryEffect).isNone
#guard (Operation.firstFiberConflict
  forgetInventoryMutationDetail publishMutation).isSome

end ArchiScriptExamples.ReservationController