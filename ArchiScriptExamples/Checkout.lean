import ArchiScriptExamples.ProofSupport
import ArchiScript

/-!
A multi-VDP checkout example for README and skill demonstrations.

Two independently justified input VDPs are combined only through tensor. Their
local member maps tensor as well. A later ordinary operation makes the
cross-factor checkout decision, and a final partial operation demonstrates that
member maps do not imply runtime effects.
-/
namespace ArchiScriptExamples.Checkout
open ArchiScript

/-- Payment data at the chosen boundary. The carrier is not preclassified into cases. -/
structure PaymentRequest where
  amountCents : Nat
  paymentToken : String
  deriving Repr

inductive PaymentInputMember where
  | invalidAmount
  | missingToken
  | eligible
  deriving DecidableEq, Repr

def invalidAmount : Domain PaymentRequest :=
  fun x => x.amountCents = 0

def missingToken : Domain PaymentRequest :=
  fun x => x.amountCents ≠ 0 ∧ x.paymentToken = ""

def eligiblePayment : Domain PaymentRequest :=
  fun x => x.amountCents ≠ 0 ∧ x.paymentToken ≠ ""

instance : MemberEnumeration PaymentInputMember where
  indices := [.invalidAmount, .missingToken, .eligible]
  complete := by intro i; cases i <;> simp

def paymentInputPartitionLookup (x : PaymentRequest) : PaymentInputMember :=
    if x.amountCents = 0 then .invalidAmount
    else if x.paymentToken = "" then .missingToken
    else .eligible

def paymentInputMembers : PaymentInputMember → Domain PaymentRequest
  | .invalidAmount => invalidAmount
  | .missingToken => missingToken
  | .eligible => eligiblePayment

theorem paymentInputPartitionLookup_correct : ∀ i x, paymentInputPartitionLookup x = i ↔ paymentInputMembers i x := by
  intro i x
  rcases x with ⟨amountCents, paymentToken⟩
  cases i <;>
    by_cases ha : amountCents = 0 <;>
    by_cases ht : paymentToken = "" <;>
    simp [paymentInputPartitionLookup, paymentInputMembers,
      invalidAmount, missingToken, eligiblePayment, ha, ht] at *


theorem paymentInputPartitionLookup_inhabited : ∀ i : PaymentInputMember, ∃ x : PaymentRequest, paymentInputPartitionLookup x = i := fun
    | .invalidAmount => ⟨⟨0, ""⟩, rfl⟩
    | .missingToken => ⟨⟨100, ""⟩, rfl⟩
    | .eligible => ⟨⟨100, "tok"⟩, rfl⟩

abbrev paymentInputPartition : Partition :=
  partitionOfRegions PaymentRequest PaymentInputMember "paymentInputPartition" paymentInputMembers
    (⟨[.invalidAmount, .missingToken, .eligible], by intro i; cases i <;> simp⟩) paymentInputPartitionLookup paymentInputPartitionLookup_correct
    (by
      intro i
      obtain ⟨x, hx⟩ := paymentInputPartitionLookup_inhabited i
      exact ⟨x, (paymentInputPartitionLookup_correct i x).mp hx⟩)
    (by
      obtain ⟨x, _⟩ := paymentInputPartitionLookup_inhabited (Classical.choice (show Nonempty PaymentInputMember from ⟨.invalidAmount⟩))
      exact ⟨paymentInputPartitionLookup x⟩)

theorem paymentInput_has_members : paymentInputPartition.HasMembers paymentInputMembers := by
  intro i x
  rfl

abbrev paymentInputSemantic : SemanticPartition where
  partition := paymentInputPartition
  members := paymentInputMembers
  hasMembers := paymentInput_has_members

/-- Inventory facts are a second, independent carrier. -/
structure InventoryObservation where
  requestedUnits : Nat
  availableUnits : Nat
  deriving Repr

inductive InventoryMember where
  | invalidDemand
  | shortfall
  | sufficient
  deriving DecidableEq, Repr

def invalidDemand : Domain InventoryObservation :=
  fun x => x.requestedUnits = 0

def inventoryShortfall : Domain InventoryObservation :=
  fun x => x.requestedUnits ≠ 0 ∧ ¬ x.requestedUnits ≤ x.availableUnits

def inventorySufficient : Domain InventoryObservation :=
  fun x => x.requestedUnits ≠ 0 ∧ x.requestedUnits ≤ x.availableUnits

instance : MemberEnumeration InventoryMember where
  indices := [.invalidDemand, .shortfall, .sufficient]
  complete := by intro i; cases i <;> simp

def inventoryObservationPartitionLookup (x : InventoryObservation) : InventoryMember :=
    if x.requestedUnits = 0 then .invalidDemand
    else if x.requestedUnits ≤ x.availableUnits then .sufficient
    else .shortfall

def inventoryMembers : InventoryMember → Domain InventoryObservation
  | .invalidDemand => invalidDemand
  | .shortfall => inventoryShortfall
  | .sufficient => inventorySufficient

theorem inventoryObservationPartitionLookup_correct : ∀ i x, inventoryObservationPartitionLookup x = i ↔ inventoryMembers i x := by
  intro i x
  rcases x with ⟨requestedUnits, availableUnits⟩
  cases i <;>
    by_cases hz : requestedUnits = 0 <;>
    by_cases hle : requestedUnits ≤ availableUnits <;>
    simp [inventoryObservationPartitionLookup, inventoryMembers,
      invalidDemand, inventoryShortfall, inventorySufficient, hz, hle] at *


theorem inventoryObservationPartitionLookup_inhabited : ∀ i : InventoryMember, ∃ x : InventoryObservation, inventoryObservationPartitionLookup x = i := fun
    | .invalidDemand => ⟨⟨0, 0⟩, rfl⟩
    | .shortfall => ⟨⟨2, 1⟩, rfl⟩
    | .sufficient => ⟨⟨1, 1⟩, rfl⟩

abbrev inventoryObservationPartition : Partition :=
  partitionOfRegions InventoryObservation InventoryMember "inventoryObservationPartition" inventoryMembers
    (⟨[.invalidDemand, .shortfall, .sufficient], by intro i; cases i <;> simp⟩) inventoryObservationPartitionLookup inventoryObservationPartitionLookup_correct
    (by
      intro i
      obtain ⟨x, hx⟩ := inventoryObservationPartitionLookup_inhabited i
      exact ⟨x, (inventoryObservationPartitionLookup_correct i x).mp hx⟩)
    (by
      obtain ⟨x, _⟩ := inventoryObservationPartitionLookup_inhabited (Classical.choice (show Nonempty InventoryMember from ⟨.invalidDemand⟩))
      exact ⟨inventoryObservationPartitionLookup x⟩)

theorem inventoryObservation_has_members : inventoryObservationPartition.HasMembers inventoryMembers := by
  intro i x
  rfl

abbrev inventoryObservationSemantic : SemanticPartition where
  partition := inventoryObservationPartition
  members := inventoryMembers
  hasMembers := inventoryObservation_has_members

inductive PaymentPlan where
  | rejectAmount
  | rejectToken
  | authorize
  deriving DecidableEq, Repr

instance : MemberEnumeration PaymentPlan where
  indices := [.rejectAmount, .rejectToken, .authorize]
  complete := by intro i; cases i <;> simp

abbrev paymentPlanPartition : Partition :=
  Partition.closed PaymentPlan "PaymentPlan"
    (⟨[.rejectAmount, .rejectToken, .authorize], by intro i; cases i <;> simp⟩) (⟨.rejectAmount⟩)

abbrev paymentPlanSemantic : SemanticPartition where
  partition := paymentPlanPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

inductive InventoryPlan where
  | rejectDemand
  | backorder
  | reserve
  deriving DecidableEq, Repr

instance : MemberEnumeration InventoryPlan where
  indices := [.rejectDemand, .backorder, .reserve]
  complete := by intro i; cases i <;> simp

abbrev inventoryPlanPartition : Partition :=
  Partition.closed InventoryPlan "InventoryPlan"
    (⟨[.rejectDemand, .backorder, .reserve], by intro i; cases i <;> simp⟩) (⟨.rejectDemand⟩)

abbrev inventoryPlanSemantic : SemanticPartition where
  partition := inventoryPlanPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

/-- Local member map for the payment factor. -/
def planPayment : Operation paymentInputPartition paymentPlanPartition where
  run
    | .invalidAmount => some .rejectAmount
    | .missingToken => some .rejectToken
    | .eligible => some .authorize

/-- Local member map for the inventory factor. -/
def planInventory : Operation inventoryObservationPartition inventoryPlanPartition where
  run
    | .invalidDemand => some .rejectDemand
    | .shortfall => some .backorder
    | .sufficient => some .reserve

/-- Independent aggregation of the two local maps. -/
def planCheckoutFactors :
    Operation
      (paymentInputPartition.tensor inventoryObservationPartition)
      (paymentPlanPartition.tensor inventoryPlanPartition) :=
  planPayment.tensor planInventory

inductive CheckoutAction where
  | rejectPayment
  | rejectInventoryRequest
  | waitForStock
  | placeOrder
  deriving DecidableEq, Repr

instance : MemberEnumeration CheckoutAction where
  indices := [.rejectPayment, .rejectInventoryRequest, .waitForStock, .placeOrder]
  complete := by intro i; cases i <;> simp

abbrev checkoutActionPartition : Partition :=
  Partition.closed CheckoutAction "CheckoutAction"
    (⟨[.rejectPayment, .rejectInventoryRequest, .waitForStock, .placeOrder], by intro i; cases i <;> simp⟩) (⟨.rejectPayment⟩)

abbrev checkoutActionSemantic : SemanticPartition where
  partition := checkoutActionPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

inductive FulfillmentView where
  | noCommand
  | submit
  deriving DecidableEq, Repr

/--
A coarser view of the same CheckoutAction carrier for consumers that only care
whether a fulfillment command exists.
-/
instance : MemberEnumeration FulfillmentView where
  indices := [.noCommand, .submit]
  complete := by intro i; cases i <;> simp

def fulfillmentViewPartitionRegions : FulfillmentView → Domain CheckoutAction
  | .submit => fun x => x = .placeOrder
  | .noCommand => fun x => x ≠ .placeOrder

def fulfillmentViewPartitionLookup : CheckoutAction → FulfillmentView
    | .placeOrder => .submit
    | .rejectPayment | .rejectInventoryRequest | .waitForStock => .noCommand

theorem fulfillmentViewPartitionLookup_correct : ∀ i x, fulfillmentViewPartitionLookup x = i ↔ fulfillmentViewPartitionRegions i x := by
  intro i x
  cases i <;> cases x <;> simp [fulfillmentViewPartitionLookup, fulfillmentViewPartitionRegions]

theorem fulfillmentViewPartitionLookup_inhabited : ∀ i : FulfillmentView, ∃ x : CheckoutAction, fulfillmentViewPartitionLookup x = i := fun
    | .noCommand => ⟨.rejectPayment, rfl⟩
    | .submit => ⟨.placeOrder, rfl⟩

abbrev fulfillmentViewPartition : Partition :=
  partitionOfRegions CheckoutAction FulfillmentView "fulfillmentViewPartition" fulfillmentViewPartitionRegions
    (⟨[.noCommand, .submit], by intro i; cases i <;> simp⟩) fulfillmentViewPartitionLookup fulfillmentViewPartitionLookup_correct
    (by
      intro i
      obtain ⟨x, hx⟩ := fulfillmentViewPartitionLookup_inhabited i
      exact ⟨x, (fulfillmentViewPartitionLookup_correct i x).mp hx⟩)
    ⟨.noCommand⟩

def checkoutActionToFulfillmentView :
    checkoutActionPartition.MemberIndex → fulfillmentViewPartition.MemberIndex
  | .placeOrder => .submit
  | .rejectPayment | .rejectInventoryRequest | .waitForStock => .noCommand

theorem checkoutAction_refines_fulfillmentView :
    checkoutActionPartition.RefinesVia
      fulfillmentViewPartition checkoutActionToFulfillmentView := by
  refine ⟨rfl, ?_⟩
  intro i action hx
  change action = i at hx
  subst action
  cases i <;> simp [Partition.member, fulfillmentViewPartition, partitionOfRegions, Subdomain.root, fulfillmentViewPartitionRegions, checkoutActionToFulfillmentView]

def forgetCheckoutActionDetail :
    Operation checkoutActionPartition fulfillmentViewPartition :=
  Partition.coarseningOperation checkoutActionToFulfillmentView

/-- Cross-factor policy is explicit here, after the independent tensor product. -/
def chooseCheckoutAction :
    Operation (paymentPlanPartition.tensor inventoryPlanPartition) checkoutActionPartition where
  run
    | (.rejectAmount, _) => some .rejectPayment
    | (.rejectToken, _) => some .rejectPayment
    | (.authorize, .rejectDemand) => some .rejectInventoryRequest
    | (.authorize, .backorder) => some .waitForStock
    | (.authorize, .reserve) => some .placeOrder

def decideCheckout :
    Operation
      (paymentInputPartition.tensor inventoryObservationPartition)
      checkoutActionPartition :=
  chooseCheckoutAction.comp planCheckoutFactors

inductive FulfillmentCommand where
  | submitOrder
  deriving DecidableEq, Repr

instance : MemberEnumeration FulfillmentCommand where
  indices := [.submitOrder]
  complete := by intro i; cases i; simp

abbrev fulfillmentCommandPartition : Partition :=
  Partition.closed FulfillmentCommand "FulfillmentCommand"
    (⟨[.submitOrder], by intro i; cases i; simp⟩) (⟨.submitOrder⟩)

/-- Only one semantic checkout action has a fulfillment-command mapping. -/
def requestFulfillment :
    Operation checkoutActionPartition fulfillmentCommandPartition where
  run
    | .placeOrder => some .submitOrder
    | .rejectPayment | .rejectInventoryRequest | .waitForStock => none

def requestFulfillmentAtCoarseResolution :
    Operation fulfillmentViewPartition fulfillmentCommandPartition where
  run
    | .noCommand => none
    | .submit => some .submitOrder

theorem requestFulfillment_factorizes :
    requestFulfillmentAtCoarseResolution.comp forgetCheckoutActionDetail =
      requestFulfillment := by
  apply Operation.ext
  intro action
  cases action <;> rfl

theorem requestFulfillment_factorsThrough :
    Operation.FactorsThrough forgetCheckoutActionDetail requestFulfillment :=
  ⟨requestFulfillmentAtCoarseResolution, requestFulfillment_factorizes⟩

def checkoutToFulfillment :
    Operation
      (paymentInputPartition.tensor inventoryObservationPartition)
      fulfillmentCommandPartition :=
  requestFulfillment.comp decideCheckout

abbrev checkoutInputSemantic : SemanticPartition :=
  paymentInputSemantic.tensor inventoryObservationSemantic

abbrev checkoutPlanSemantic : SemanticPartition :=
  paymentPlanSemantic.tensor inventoryPlanSemantic

#guard (paymentInputPartition.tensor inventoryObservationPartition).memberIndices.length == 9
#guard planPayment .invalidAmount == some .rejectAmount
#guard planPayment .missingToken == some .rejectToken
#guard planPayment .eligible == some .authorize
#guard planInventory .invalidDemand == some .rejectDemand
#guard planInventory .shortfall == some .backorder
#guard planInventory .sufficient == some .reserve

#guard decideCheckout (.invalidAmount, .sufficient) == some .rejectPayment
#guard decideCheckout (.missingToken, .shortfall) == some .rejectPayment
#guard decideCheckout (.eligible, .invalidDemand) == some .rejectInventoryRequest
#guard decideCheckout (.eligible, .shortfall) == some .waitForStock
#guard decideCheckout (.eligible, .sufficient) == some .placeOrder

#guard checkoutToFulfillment (.eligible, .sufficient) == some .submitOrder
#guard checkoutToFulfillment (.eligible, .shortfall) == none
#guard forgetCheckoutActionDetail .rejectPayment == some .noCommand
#guard forgetCheckoutActionDetail .waitForStock == some .noCommand
#guard forgetCheckoutActionDetail .placeOrder == some .submit

example :
    decideCheckout =
      chooseCheckoutAction.comp (planPayment.tensor planInventory) := rfl

end ArchiScriptExamples.Checkout