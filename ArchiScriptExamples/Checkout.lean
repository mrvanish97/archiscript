import ArchiScript

/-!
A compact multi-VDP example for README and skill demonstrations.

The two input factors are modeled independently. Their local planning operations
are tensored, then an ordinary sequential operation consumes the joint plan.
Nothing here claims runtime parallelism or effects.
-/
namespace ArchiScriptExamples.Checkout
open ArchiScript

inductive PaymentInput where
  | invalid
  | eligible
  deriving DecidableEq, Repr

def paymentInputPartition : Partition where
  Carrier := PaymentInput
  MemberIndex := PaymentInput
  carrierNonempty := ⟨.invalid⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.invalid, .eligible]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def paymentInputSemantic : SemanticPartition where
  partition := paymentInputPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

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

def inventoryObservationSemantic : SemanticPartition where
  partition := inventoryObservationPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

inductive PaymentPlan where
  | reject
  | authorize
  deriving DecidableEq, Repr

def paymentPlanPartition : Partition where
  Carrier := PaymentPlan
  MemberIndex := PaymentPlan
  carrierNonempty := ⟨.reject⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.reject, .authorize]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def paymentPlanSemantic : SemanticPartition where
  partition := paymentPlanPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

inductive InventoryPlan where
  | blocked
  | ready
  deriving DecidableEq, Repr

def inventoryPlanPartition : Partition where
  Carrier := InventoryPlan
  MemberIndex := InventoryPlan
  carrierNonempty := ⟨.blocked⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.blocked, .ready]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def inventoryPlanSemantic : SemanticPartition where
  partition := inventoryPlanPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

def planPayment : Operation paymentInputPartition paymentPlanPartition where
  run
    | .invalid => some .reject
    | .eligible => some .authorize

def planInventory : Operation inventoryObservationPartition inventoryPlanPartition where
  run
    | .unavailable => some .blocked
    | .available => some .ready

/-- Independent aggregation of the two local planning maps. -/
def planCheckoutFactors :
    Operation
      (paymentInputPartition.tensor inventoryObservationPartition)
      (paymentPlanPartition.tensor inventoryPlanPartition) :=
  planPayment.tensor planInventory

inductive CheckoutAction where
  | rejectPayment
  | waitForStock
  | placeOrder
  deriving DecidableEq, Repr

def checkoutActionPartition : Partition where
  Carrier := CheckoutAction
  MemberIndex := CheckoutAction
  carrierNonempty := ⟨.rejectPayment⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.rejectPayment, .waitForStock, .placeOrder]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def checkoutActionSemantic : SemanticPartition where
  partition := checkoutActionPartition
  members := fun i x => x = i
  hasMembers := by intro i x; rfl

/-- Ordinary sequential decision over the joint semantic plan. -/
def chooseCheckoutAction :
    Operation (paymentPlanPartition.tensor inventoryPlanPartition) checkoutActionPartition where
  run
    | (.reject, _) => some .rejectPayment
    | (.authorize, .blocked) => some .waitForStock
    | (.authorize, .ready) => some .placeOrder

def decideCheckout :
    Operation
      (paymentInputPartition.tensor inventoryObservationPartition)
      checkoutActionPartition :=
  chooseCheckoutAction.comp planCheckoutFactors

def checkoutInputSemantic : SemanticPartition :=
  paymentInputSemantic.tensor inventoryObservationSemantic

def checkoutPlanSemantic : SemanticPartition :=
  paymentPlanSemantic.tensor inventoryPlanSemantic

#guard (paymentInputPartition.tensor inventoryObservationPartition).memberIndices.length == 4
#guard planCheckoutFactors (.eligible, .available) == some (.authorize, .ready)
#guard planCheckoutFactors (.invalid, .available) == some (.reject, .ready)

#guard decideCheckout (.invalid, .unavailable) == some .rejectPayment
#guard decideCheckout (.invalid, .available) == some .rejectPayment
#guard decideCheckout (.eligible, .unavailable) == some .waitForStock
#guard decideCheckout (.eligible, .available) == some .placeOrder

example :
    decideCheckout =
      chooseCheckoutAction.comp (planPayment.tensor planInventory) := rfl

end ArchiScriptExamples.Checkout
