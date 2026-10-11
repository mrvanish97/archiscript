import ArchiScriptExamples.ReservationController

namespace ArchiScriptTests.ProofEngineering

open ArchiScript
open ArchiScriptExamples.ReservationController

/-!
These regressions check that a previously verified local consumer
factorization can be lifted through an arbitrary producer. Neither the source
partition nor the consumer's semantic distinctions are changed.

The outbox counterexample prevents reusing the same invalid cut for another
consumer. This file is a correctness regression, not a timing benchmark.
-/

/-- Reuse the checked local equality rather than splitting every producer member. -/
theorem inventory_after_any_producer
    {S : Partition}
    (producer : Operation S reservationMutationPartition) :
    inventoryEffect.comp producer =
      inventoryEffectAtCoarseResolution.comp
        (forgetInventoryMutationDetail.comp producer) := by
  rw [← inventoryEffect_factorizes]
  exact Operation.comp_assoc
    inventoryEffectAtCoarseResolution
    forgetInventoryMutationDetail
    producer

/-- Specialize the generic result to the three-entry reservation controller. -/
example :
    inventoryEffect.comp planControllerMutation =
      inventoryEffectAtCoarseResolution.comp
        (forgetInventoryMutationDetail.comp planControllerMutation) :=
  inventory_after_any_producer planControllerMutation

/-- The outbox distinguishes cancel from expire, so the same cut is invalid. -/
example :
    ¬ Operation.FactorsThrough forgetInventoryMutationDetail publishMutation :=
  publishMutation_does_not_factorThrough_inventoryView

/-- Keep the independent tensor composite symbolic rather than enumerating pairs. -/
example (P P' P'' Q Q' Q'' : Partition)
    (f₁ : Operation P P') (f₂ : Operation P' P'')
    (g₁ : Operation Q Q') (g₂ : Operation Q' Q'') :
    (f₂.comp f₁).tensor (g₂.comp g₁) =
      (f₂.tensor g₂).comp (f₁.tensor g₁) :=
  Operation.tensor_comp f₁ f₂ g₁ g₂

end ArchiScriptTests.ProofEngineering
