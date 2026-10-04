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

def paymentInputPartition : Partition where
  Carrier := PaymentRequest
  MemberIndex := PaymentInputMember
  carrierNonempty := ⟨⟨0, ""⟩⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.invalidAmount, .missingToken, .eligible]
  memberIndices_complete := by intro i; cases i <;> simp
  classify x :=
    if x.amountCents = 0 then .invalidAmount
    else if x.paymentToken = "" then .missingToken
    else .eligible
  member_inhabited
    | .invalidAmount => ⟨⟨0, ""⟩, rfl⟩
    | .missingToken => ⟨⟨100, ""⟩, rfl⟩
    | .eligible => ⟨⟨100, "tok"⟩, rfl⟩

def paymentInputMembers : PaymentInputMember → Domain PaymentRequest
  | .invalidAmount => invalidAmount
  | .missingToken => missingToken
  | .eligible => eligiblePayment

theorem paymentInput_has_members :
    paymentInputPartition.HasMembers paymentInputMembers := by
  intro i x
  rcases x with ⟨amountCents, paymentToken⟩
  cases i <;>
    by_cases ha : amountCents = 0 <;>
    by_cases ht : paymentToken = "" <;>
    simp [Partition.member, paymentInputPartition, paymentInputMembers,
      invalidAmount, missingToken, eligiblePayment, ha, ht] at *

def paymentInputSemantic : SemanticPartition where
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

def inventoryObservationPartition : Partition where
  Carrier := InventoryObservation
  MemberIndex := InventoryMember
  carrierNonempty := ⟨⟨0, 0⟩⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.invalidDemand, .shortfall, .sufficient]
  memberIndices_complete := by intro i; cases i <;> simp
  classify x :=
    if x.requestedUnits = 0 then .invalidDemand
    else if x.requestedUnits ≤ x.availableUnits then .sufficient
    else .shortfall
  member_inhabited
    | .invalidDemand => ⟨⟨0, 0⟩, rfl⟩
    | .shortfall => ⟨⟨2, 1⟩, rfl⟩
    | .sufficient => ⟨⟨1, 1⟩, rfl⟩

def inventoryMembers : InventoryMember → Domain InventoryObservation
  | .invalidDemand => invalidDemand
  | .shortfall => inventoryShortfall
  | .sufficient => inventorySufficient

theorem inventoryObservation_has_members :
    inventoryObservationPartition.HasMembers inventoryMembers := by
  intro i x
  rcases x with ⟨requestedUnits, availableUnits⟩
  cases i <;>
    by_cases hz : requestedUnits = 0 <;>
    by_cases hle : requestedUnits ≤ availableUnits <;>
    simp [Partition.member, inventoryObservationPartition, inventoryMembers,
      invalidDemand, inventoryShortfall, inventorySufficient, hz, hle] at *

def inventoryObservationSemantic : SemanticPartition where
  partition := inventoryObservationPartition
  members := inventoryMembers
  hasMembers := inventoryObservation_has_members

inductive PaymentPlan where
  | rejectAmount
  | rejectToken
  | authorize
  deriving DecidableEq, Repr

def paymentPlanPartition : Partition where
  Carrier := PaymentPlan
  MemberIndex := PaymentPlan
  carrierNonempty := ⟨.rejectAmount⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.rejectAmount, .rejectToken, .authorize]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def paymentPlanSemantic : SemanticPartition where
  partition := paymentPlanPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

inductive InventoryPlan where
  | rejectDemand
  | backorder
  | reserve
  deriving DecidableEq, Repr

def inventoryPlanPartition : Partition where
  Carrier := InventoryPlan
  MemberIndex := InventoryPlan
  carrierNonempty := ⟨.rejectDemand⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.rejectDemand, .backorder, .reserve]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def inventoryPlanSemantic : SemanticPartition where
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

def checkoutActionPartition : Partition where
  Carrier := CheckoutAction
  MemberIndex := CheckoutAction
  carrierNonempty := ⟨.rejectPayment⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.rejectPayment, .rejectInventoryRequest, .waitForStock, .placeOrder]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def checkoutActionSemantic : SemanticPartition where
  partition := checkoutActionPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

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

def fulfillmentCommandPartition : Partition where
  Carrier := FulfillmentCommand
  MemberIndex := FulfillmentCommand
  carrierNonempty := ⟨.submitOrder⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.submitOrder]
  memberIndices_complete := by intro i; cases i; simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

/-- Only one semantic checkout action has a fulfillment-command mapping. -/
def requestFulfillment :
    Operation checkoutActionPartition fulfillmentCommandPartition where
  run
    | .placeOrder => some .submitOrder
    | .rejectPayment | .rejectInventoryRequest | .waitForStock => none

def checkoutToFulfillment :
    Operation
      (paymentInputPartition.tensor inventoryObservationPartition)
      fulfillmentCommandPartition :=
  requestFulfillment.comp decideCheckout

def checkoutInputSemantic : SemanticPartition :=
  paymentInputSemantic.tensor inventoryObservationSemantic

def checkoutPlanSemantic : SemanticPartition :=
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

example :
    decideCheckout =
      chooseCheckoutAction.comp (planPayment.tensor planInventory) := rfl

end ArchiScriptExamples.Checkout
