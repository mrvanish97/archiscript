# Compositional Lean proofs

Use this example when a theorem requires a large case split. The goal is
to reuse verified local statements and prove **the original theorem**.

## Example: shared reservation decision

In `ArchiScriptExamples/ReservationController.lean`:

- `planControllerMutation` combines user, payment, and expiry entry paths.
- `inventoryEffect_factorizes` already proves:
  `inventoryEffectAtCoarseResolution.comp forgetInventoryMutationDetail = inventoryEffect`.
- `Operation.comp_assoc` lifts that result through any producer of a
  `ReservationMutation`, without enumerating the producer's source members.

The following is a template to check in Lean before using it in a model:

```lean
import ArchiScriptExamples.ReservationController

open ArchiScript
open ArchiScriptExamples.ReservationController

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
```

The same `InventoryMutationView` is **not** a valid cut for the outbox:
`publishMutation_does_not_factorThrough_inventoryView` is a checked
counterexample. Never reuse a coarsening-based split for a different
consumer without proving its factorization.

## Choose an assembly law

| Goal structure | Existing Lean mechanism |
| --- | --- |
| Equality of Operations | `Operation.ext` |
| Sequential composition | `Operation.comp_assoc` |
| Independent tensor composition | `Operation.tensor_comp` |
| Rewriting an Expression subtree | `Expression.Rewrite.comp`, `.tensor`, `.copair`, `.trans` |
| Changed endpoint representatives | `Expression.Transport` with an explicit `PartitionIso` |
| Consumer of a coarsened VDP | Prove `Operation.FactorsThrough`; use `firstFiberConflict` to reject invalid candidates |

Only use a row when its theorem matches the goal. If no structural law
applies, a direct finite proof is acceptable. Keep the source theorem,
carriers, partiality, and independent tensor members unchanged.

## Verify the result

Run `lake build` and the normal project checks. For each difficult
proof, retain the checked theorem name and any reusable local lemmas.
For performance comparisons, use the same original statement and record
actual Lean check time and AI retries; do not claim a speedup without a run.
