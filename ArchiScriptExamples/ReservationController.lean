import ArchiScriptExamples.ProofSupport
import ArchiScript

/-!
A compact algebra, Presentation and linear-route stress example.

Three declared symbolic entry channels describe observations of the same logical
reservation resource. The user path tensors request, inventory and state factors
and their local member maps. The full products do not prove joint availability
or identify actual producer occurrences.

This fixture declares no controller ArchitectureSignature or DeclaredArchitecture
and claims no CertifiedDeclaredArchitecture. Such a certificate needs recursive
RootCoherent suppliers, inputSources for every generator, universal coherent
input contracts, effectCoverage and a ConeStatus for every Cause. Observable
ConeValid requires an actual nonempty effect.Position and a reachable tuple;
NoObservableEffect instead proves empty Effect incoming images and contract.
BoundariesComplete supplies that proof or a structural boundary path. These
obligations do not follow from the algebraic equalities below.

The model deliberately separates:
* semantic next-state selection,
* persistence commands,
* outbox commands,
* inventory commands.

All are ordinary member-level Operations. `none` denotes an undefined member
mapping. None proves that a runtime side effect executed successfully.

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

instance : MemberEnumeration UserTrigger where
  indices := [.malformed, .reserve, .cancel]
  complete := by intro i; cases i <;> simp

abbrev userTriggerPartition : Partition :=
  Partition.closed UserTrigger "UserTrigger"
    (⟨[.malformed, .reserve, .cancel], by intro i; cases i <;> simp⟩) (⟨.malformed⟩)

inductive UserIntent where
  | reserve
  | cancel
  deriving DecidableEq, Repr

instance : MemberEnumeration UserIntent where
  indices := [.reserve, .cancel]
  complete := by intro i; cases i <;> simp

abbrev userIntentPartition : Partition :=
  Partition.closed UserIntent "UserIntent"
    (⟨[.reserve, .cancel], by intro i; cases i <;> simp⟩) (⟨.reserve⟩)

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

instance : MemberEnumeration InventoryObservation where
  indices := [.unavailable, .available]
  complete := by intro i; cases i <;> simp

abbrev inventoryObservationPartition : Partition :=
  Partition.closed InventoryObservation "InventoryObservation"
    (⟨[.unavailable, .available], by intro i; cases i <;> simp⟩) (⟨.unavailable⟩)

inductive InventoryPlan where
  | blocked
  | canHold
  deriving DecidableEq, Repr

instance : MemberEnumeration InventoryPlan where
  indices := [.blocked, .canHold]
  complete := by intro i; cases i <;> simp

abbrev inventoryPlanPartition : Partition :=
  Partition.closed InventoryPlan "InventoryPlan"
    (⟨[.blocked, .canHold], by intro i; cases i <;> simp⟩) (⟨.blocked⟩)

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

instance : MemberEnumeration ReservationState where
  indices := [.empty, .held, .paid, .cancelled, .expired]
  complete := by intro i; cases i <;> simp

abbrev reservationStatePartition : Partition :=
  Partition.closed ReservationState "ReservationState"
    (⟨[.empty, .held, .paid, .cancelled, .expired], by intro i; cases i <;> simp⟩) (⟨.empty⟩)

inductive ReservationMutation where
  | hold
  | markPaid
  | cancel
  | expire
  deriving DecidableEq, Repr

instance : MemberEnumeration ReservationMutation where
  indices := [.hold, .markPaid, .cancel, .expire]
  complete := by intro i; cases i <;> simp

abbrev reservationMutationPartition : Partition :=
  Partition.closed ReservationMutation "ReservationMutation"
    (⟨[.hold, .markPaid, .cancel, .expire], by intro i; cases i <;> simp⟩) (⟨.hold⟩)

/-- Declared user/inventory/state observation product: 3 × 2 × 5 = 30 members. -/
abbrev userContextPartition : Partition :=
  (userTriggerPartition.tensor inventoryObservationPartition).tensor
    reservationStatePartition

/-- The corresponding normalized local-plan context. -/
abbrev userDecisionContextPartition : Partition :=
  (userIntentPartition.tensor inventoryPlanPartition).tensor
    reservationStatePartition

/-- Tensor the local maps and carry state unchanged in its own slot. -/
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

instance : MemberEnumeration PaymentTrigger where
  indices := [.authorized, .failed]
  complete := by intro i; cases i <;> simp

abbrev paymentTriggerPartition : Partition :=
  Partition.closed PaymentTrigger "PaymentTrigger"
    (⟨[.authorized, .failed], by intro i; cases i <;> simp⟩) (⟨.authorized⟩)

abbrev paymentContextPartition : Partition :=
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

instance : MemberEnumeration ExpiryTrigger where
  indices := [.fired]
  complete := by intro i; cases i; simp

abbrev expiryTriggerPartition : Partition :=
  Partition.closed ExpiryTrigger "ExpiryTrigger"
    (⟨[.fired], by intro i; cases i; simp⟩) (⟨.fired⟩)

abbrev expiryContextPartition : Partition :=
  expiryTriggerPartition.tensor reservationStatePartition

/-- Expiry-channel planning; no joint availability or ordering proof is asserted. -/
def planExpiryMutation :
    Operation expiryContextPartition reservationMutationPartition where
  run
    | (.fired, .held) => some .expire
    | _ => none

/--
The fixture declares three entry channels. Each symbolic carrier covers its
enumerated constructors; this does not establish real-world Cause completeness.
Coproduct aggregates these tagged alternatives, not simultaneous consequences.
-/
abbrev controllerInputPartition : Partition :=
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

instance : MemberEnumeration ReservationWrite where
  indices := [.setHeld, .setPaid, .setCancelled, .setExpired]
  complete := by intro i; cases i <;> simp

abbrev reservationWritePartition : Partition :=
  Partition.closed ReservationWrite "ReservationWrite"
    (⟨[.setHeld, .setPaid, .setCancelled, .setExpired], by intro i; cases i <;> simp⟩) (⟨.setHeld⟩)

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

instance : MemberEnumeration OutboxMessage where
  indices := [.requestPayment, .reservationPaid, .reservationCancelled, .reservationExpired]
  complete := by intro i; cases i <;> simp

abbrev outboxMessagePartition : Partition :=
  Partition.closed OutboxMessage "OutboxMessage"
    (⟨[.requestPayment, .reservationPaid, .reservationCancelled, .reservationExpired], by intro i; cases i <;> simp⟩) (⟨.requestPayment⟩)

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

instance : MemberEnumeration InventoryCommand where
  indices := [.reserveUnits, .releaseUnits]
  complete := by intro i; cases i <;> simp

abbrev inventoryCommandPartition : Partition :=
  Partition.closed InventoryCommand "InventoryCommand"
    (⟨[.reserveUnits, .releaseUnits], by intro i; cases i <;> simp⟩) (⟨.reserveUnits⟩)

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
instance : MemberEnumeration InventoryMutationView where
  indices := [.reserve, .noCommand, .release]
  complete := by intro i; cases i <;> simp

def inventoryMutationViewPartitionRegions : InventoryMutationView → Domain ReservationMutation
  | .reserve => fun x => x = .hold
  | .noCommand => fun x => x = .markPaid
  | .release => fun x => x = .cancel ∨ x = .expire

def inventoryMutationViewPartitionLookup : ReservationMutation → InventoryMutationView
    | .hold => .reserve
    | .markPaid => .noCommand
    | .cancel | .expire => .release

theorem inventoryMutationViewPartitionLookup_correct : ∀ i x, inventoryMutationViewPartitionLookup x = i ↔ inventoryMutationViewPartitionRegions i x := by
  intro i x
  cases i <;> cases x <;> simp [inventoryMutationViewPartitionLookup, inventoryMutationViewPartitionRegions]

theorem inventoryMutationViewPartitionLookup_inhabited : ∀ i : InventoryMutationView, ∃ x : ReservationMutation, inventoryMutationViewPartitionLookup x = i := fun
    | .reserve => ⟨.hold, rfl⟩
    | .noCommand => ⟨.markPaid, rfl⟩
    | .release => ⟨.cancel, rfl⟩

abbrev inventoryMutationViewPartition : Partition :=
  partitionOfRegions ReservationMutation InventoryMutationView "inventoryMutationViewPartition" inventoryMutationViewPartitionRegions
    (⟨[.reserve, .noCommand, .release], by intro i; cases i <;> simp⟩) inventoryMutationViewPartitionLookup inventoryMutationViewPartitionLookup_correct
    (by
      intro i
      obtain ⟨x, hx⟩ := inventoryMutationViewPartitionLookup_inhabited i
      exact ⟨x, (inventoryMutationViewPartitionLookup_correct i x).mp hx⟩)
    ⟨.reserve⟩

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
  change mutation = i at hx
  subst mutation
  cases i <;> simp [Partition.member, inventoryMutationViewPartition, partitionOfRegions, Subdomain.root, inventoryMutationViewPartitionRegions, mutationToInventoryView]

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

/-- Per-channel planners compose with the same semantic next-state map. -/
def userStateUpdate :
    Operation userContextPartition reservationStatePartition :=
  nextReservationState.comp planUserMutation

def paymentStateUpdate :
    Operation paymentContextPartition reservationStatePartition :=
  nextReservationState.comp planPaymentMutation

def expiryStateUpdate :
    Operation expiryContextPartition reservationStatePartition :=
  nextReservationState.comp planExpiryMutation

/-- Per-channel planners compose with write commands for one logical resource. -/
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
Algebraic Presentation stress coverage.

The Operations above remain the semantic category. The declarations below keep
selected presentation syntax without changing any VDP or Operation identity.
Each Presentation has typed source and target VDPs; the selected family groups
consequence views without tensoring their outputs or proving Cone completeness.
-/

def prepareUserContextPresentation :
    Presentation userContextPartition userDecisionContextPartition :=
  .tensor
    (.tensor (.atom parseUser) (.atom planInventory))
    (.identity reservationStatePartition)

def planUserMutationPresentation :
    Presentation userContextPartition reservationMutationPartition :=
  .comp (.atom decideUserMutation) prepareUserContextPresentation

def planPaymentMutationPresentation :
    Presentation paymentContextPartition reservationMutationPartition :=
  .atom planPaymentMutation

def planExpiryMutationPresentation :
    Presentation expiryContextPartition reservationMutationPartition :=
  .atom planExpiryMutation

/--
The controller Presentation keeps the actual tensor/composition/coproduct
presentation instead of wrapping the already-composed semantic Operation as one
opaque atom.
-/
def controllerPlanPresentation :
    Presentation controllerInputPartition reservationMutationPartition :=
  .copair
    (.copair planUserMutationPresentation planPaymentMutationPresentation)
    planExpiryMutationPresentation

example :
    Presentation.denote prepareUserContextPresentation = prepareUserContext := rfl

example :
    Presentation.denote planUserMutationPresentation = planUserMutation := rfl

example :
    Presentation.denote controllerPlanPresentation = planControllerMutation := rfl

def controllerStatePresentation :
    Presentation controllerInputPartition reservationStatePartition :=
  .comp (.atom nextReservationState) controllerPlanPresentation

def controllerWritePresentation :
    Presentation controllerInputPartition reservationWritePartition :=
  .comp (.atom persistMutation) controllerPlanPresentation

def controllerPublishPresentation :
    Presentation controllerInputPartition outboxMessagePartition :=
  .comp (.atom publishMutation) controllerPlanPresentation

def controllerInventoryPresentation :
    Presentation controllerInputPartition inventoryCommandPartition :=
  .comp (.atom inventoryEffect) controllerPlanPresentation

/--
One source, several selected consequence presentations. This depicts possible
fan-out without `Operation.tensor`, actual Effect positions or a joint contract.
No order or parallel runtime schedule is asserted between sibling consequences.
-/
def controllerPresentationFamily : Presentation.Family where
  source := controllerInputPartition
  presentations := [
    { target := reservationMutationPartition, presentation := controllerPlanPresentation },
    { target := reservationStatePartition, presentation := controllerStatePresentation },
    { target := reservationWritePartition, presentation := controllerWritePresentation },
    { target := outboxMessagePartition, presentation := controllerPublishPresentation },
    { target := inventoryCommandPartition, presentation := controllerInventoryPresentation }
  ]
  nonempty := by simp

example :
    Presentation.denote controllerStatePresentation =
      nextReservationState.comp planControllerMutation := rfl

example :
    Presentation.denote controllerPublishPresentation =
      publishMutation.comp planControllerMutation := rfl

/--
A branch-relative coproduct simplification. The unused payment branch disappears
from this selected presentation by the coproduct law; the payment VDP and planner
remain in the architecture and may be used by other presentations.
-/
theorem userSelectedCoproductNormalization :
    Presentation.Rewrite
      (.comp
        (.copair
          planUserMutationPresentation
          planPaymentMutationPresentation)
        (.coproductInl userContextPartition paymentContextPartition))
      planUserMutationPresentation :=
  Presentation.Rewrite.copair_inl
    planUserMutationPresentation
    planPaymentMutationPresentation

theorem paymentSelectedCoproductNormalization :
    Presentation.Rewrite
      (.comp
        (.copair
          planUserMutationPresentation
          planPaymentMutationPresentation)
        (.coproductInr userContextPartition paymentContextPartition))
      planPaymentMutationPresentation :=
  Presentation.Rewrite.copair_inr
    planUserMutationPresentation
    planPaymentMutationPresentation

/--
A local coproduct simplification remains valid inside a larger Presentation:
simplify a proved subpresentation and lift the equality through composition.
-/
theorem userSelectedStateNormalization :
    Presentation.Rewrite
      (.comp
        (.atom nextReservationState)
        (.comp
          (.copair
            planUserMutationPresentation
            planPaymentMutationPresentation)
          (.coproductInl userContextPartition paymentContextPartition)))
      (.comp (.atom nextReservationState) planUserMutationPresentation) :=
  Presentation.Rewrite.comp
    (Presentation.Rewrite.refl (.atom nextReservationState))
    userSelectedCoproductNormalization

/--
The first two controller channels expose the shared ReservationState coordinate:

  ((UserTrigger ⊗ InventoryObservation) ⊗ ReservationState)
    ⊕ (PaymentTrigger ⊗ ReservationState)

is canonically isomorphic to

  ((UserTrigger ⊗ InventoryObservation) ⊕ PaymentTrigger)
    ⊗ ReservationState.

This is structural factoring only. It does not claim one database read,
transaction, cache entry, or runtime object for ReservationState.

Both sides are kept as structural presentations rather than introduced as new
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

def userPaymentPlanPresentation :
    Presentation (userContextPartition.coproduct paymentContextPartition)
      reservationMutationPartition :=
  .copair
    planUserMutationPresentation
    planPaymentMutationPresentation

def userPaymentFactoredPlanPresentation :
    Presentation
      (((userTriggerPartition.tensor inventoryObservationPartition).coproduct
          paymentTriggerPartition).tensor reservationStatePartition)
      reservationMutationPartition :=
  .comp userPaymentPlanPresentation (.iso userPaymentSourceIso.symm)

/-- The factored source presentation commutes with the original planner. -/
def userPaymentFactoringCertificate :
    Presentation.Transport userPaymentPlanPresentation
      userPaymentFactoredPlanPresentation :=
  Presentation.Transport.source userPaymentPlanPresentation userPaymentSourceIso

example :
    userPaymentFactoringCertificate.targetIso.toOperation.comp
        (Presentation.denote userPaymentPlanPresentation) =
      (Presentation.denote userPaymentFactoredPlanPresentation).comp
        userPaymentFactoringCertificate.sourceIso.toOperation :=
  userPaymentFactoringCertificate.commutes

/--
The complete three-channel controller source can be factored to one shared
ReservationState coordinate:

  ((U ⊗ I) ⊗ R) ⊕ (P ⊗ R) ⊕ (E ⊗ R)
    ≅
  (((U ⊗ I) ⊕ P) ⊕ E) ⊗ R.

This witness is the concrete nested-binary distributive shape used by the stress
test. The target remains an anonymous structural representation: normalization
does not create a replacement nominal VDP declaration.
-/
def controllerSourceFactoringIso :
    Partition.PartitionIso controllerInputPartition
      ((((userTriggerPartition.tensor inventoryObservationPartition).coproduct
          paymentTriggerPartition).coproduct expiryTriggerPartition).tensor
            reservationStatePartition) :=
  (Partition.PartitionIso.coproduct userPaymentSourceIso
      (Partition.PartitionIso.refl expiryContextPartition)).trans
    (Partition.tensorCoproductRightDistributivity
      ((userTriggerPartition.tensor inventoryObservationPartition).coproduct
        paymentTriggerPartition)
      expiryTriggerPartition
      reservationStatePartition)

def controllerFactoredPlanPresentation :
    Presentation
      ((((userTriggerPartition.tensor inventoryObservationPartition).coproduct
          paymentTriggerPartition).coproduct expiryTriggerPartition).tensor
            reservationStatePartition)
      reservationMutationPartition :=
  .comp controllerPlanPresentation (.iso controllerSourceFactoringIso.symm)

def controllerFactoringCertificate :
    Presentation.Transport controllerPlanPresentation
      controllerFactoredPlanPresentation :=
  Presentation.Transport.source controllerPlanPresentation controllerSourceFactoringIso

example :
    controllerFactoringCertificate.targetIso.toOperation.comp
        (Presentation.denote controllerPlanPresentation) =
      (Presentation.denote controllerFactoredPlanPresentation).comp
        controllerFactoringCertificate.sourceIso.toOperation :=
  controllerFactoringCertificate.commutes

/--
Composition can denote an end-to-end controller result while the nominal
ReservationMutation VDP still exists. A diagram that intentionally hides that
intermediate VDP is an architecture projection of the view, not a normalization
step that deleted the object from the category.
-/
def projectedControllerStateOperation :
    Operation controllerInputPartition reservationStatePartition :=
  Presentation.denote controllerStatePresentation

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

/-! Actual primitive mutation consumers also have linear presentations. Their
nominal targets stay distinct from algebraically equal representations.
This algebra/projection fixture does not assert producer identity from VDP or
Operation equality. In a declared Cone, one shared consumer can accept distinct
producer derivations; `Expression.supply_preserves_provenance` retains their
histories through any unmarked suffix. Coherent canonical roots, fully supplied
inputs and exact independent contracts remain separate obligations. SharedTargets
checks that case with one graph and complete scoped certificates. No analytical
product here declares an extra join or a Cone certificate for this controller. -/
namespace Linear

inductive Object where | mutation | state | write | publish | inventory
inductive Name where | state | write | publish | inventory

abbrev objects : Object → VDP
  | .mutation => reservationMutationPartition
  | .state => reservationStatePartition
  | .write => reservationWritePartition
  | .publish => outboxMessagePartition
  | .inventory => inventoryCommandPartition

abbrev generators : Generators where
  Name := Name
  names := [.state, .write, .publish, .inventory]
  complete := by intro n; cases n <;> simp
  Object := Object
  object := objects
  source := fun _ => .mutation
  target | .state => .state | .write => .write | .publish => .publish | .inventory => .inventory
  operation
    | .state => nextReservationState
    | .write => persistMutation
    | .publish => publishMutation
    | .inventory => inventoryEffect

def stateRoute : Expression generators .mutation .state :=
  Expression.step (G := generators) .state (Expression.identity (G := generators) Object.mutation)

def inventoryRoute : Expression generators .mutation .inventory :=
  Expression.step (G := generators) .inventory (Expression.identity (G := generators) Object.mutation)

theorem state_denotation : stateRoute.denote = nextReservationState := by
  simp [stateRoute, Expression.denote]
theorem inventory_denotation : inventoryRoute.denote = inventoryEffect := by
  simp [inventoryRoute, Expression.denote]

end Linear

end ArchiScriptExamples.ReservationController
