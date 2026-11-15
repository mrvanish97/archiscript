# Composing proofs without changing the model

Keep the intended proposition and carrier fixed. A smaller proof is useful only
when the same mathematical conclusion follows.

## Reuse algebraic facts

`Operation.comp_assoc`, `tensor_comp`, coproduct injection/copairing laws and the
monoidal coherence laws avoid repeated source-member enumeration. Refinement
is semantic containment on the same carrier. A consumer factors through a
coarsening only when it respects every collapsed fiber; `firstFiberConflict`
returns a concrete obstruction.

The [ReservationController algebra fixture](../../../ArchiScriptExamples/ReservationController.lean)
retains successful inventory
factorization and rejected outbox factorization. Its nonlinear examples now
use `Presentation`. It is an algebra/projection example, not a complete Cone
certificate. Its selected `Presentation.Family` establishes no exhaustiveness.

`Presentation.Rewrite` certifies equality of denoted Operations with unchanged
endpoints. `Presentation.Transport` requires explicit endpoint `PartitionIso`
values and a commuting square. Canonical distributivity is an isomorphism,
never definitional equality. Hiding an intermediate nominal object is an
architecture projection, not a theorem that composition erased that object.

## Reuse semantic invariants

`DeclaredArchitecture.evaluate_of_assignment` proves a particular node-value
invariant from root agreement, all generator equations and availability.
It does not assert stationary values for arbitrary cycles. The correlated-join
example uses this lemma to preserve common-source correlation across fan-out.
Its independently authored join contract is checked against the reference
relation for every derived input term.

`evaluate_inputContract` proves that replacing `admissibleInput` does not alter
producer evaluation. It supports comparing different independent proposed
contracts against the same reference semantics; it supplies no agreement proof.
E requires every reachable tuple to be admitted and **every admitted tuple to
be reachable**, including impossible tuples a proposed contract mistakenly adds.

`Evaluates.supplier` projects an already proved full-tuple evaluation. It must
not be used to redefine independently required incoming images from accepted
join tuples. Those images are obtained from the actual suppliers first.

Reuse root and source proofs at their actual scope. `RootCoherent.supplier`
preserves canonical origins at each position. `Term.fromSuppliers_coherent`
assembles coherent suppliers, and `supplier_fromSuppliers` recovers each exact
producer. Neither construction declares a copying or join Operation.
`isInputContext_iff_coherent` derives the local ownership witness;
`input_consequence_inCone` puts its result in the output owner's Cone. Check
all Causes recursively, not only the owner. Raw evaluation and equal VDPs do
not establish that scope; [RootCoherence.lean](../../../ArchiScriptTests/RootCoherence.lean)
keeps canonical fan-out and cross-Cone joins while rejecting nested mixed roots.

`inputSources_of_catalog` reuses `ProvenanceAnalysis.Valid` and
`SourcesPresent g` to prove per-generator `InputSources.grounded`. If instead
all independent `supplierImage`s are empty, prove `InputSources.unreachable`.
A missing supplier at one position cannot justify the latter when another
has an incoming value. Preserve universal `inputs` over **all** coherent full
contexts; chosen grounding witnesses do not delimit them.
`CertifiedDeclaredArchitecture.input_partner` then provides a full supported
context and an Adm-and-Reach partner for each independently incoming member.
It does not assert reachability of every Cartesian combination.

For cycles, prove the reference boundary image before optimizing saturation.
The cyclic example relates finite provenance derivations to an independently
stated alternating-member law and supplies `ExactAbstraction` for its finite
closure. Reachable sets stabilize while Operation powers keep alternating.

A fixed-point calculation on a reduced state space requires an exactness
proof. Keep all root identity and correlations needed by the final query.
Memoizing only an Operation and one member is not generally sufficient.

`ProvenanceAnalysis.Valid` needs each Cause's canonical origin in its root list,
not every value of `RootInstance`. Reuse `Seeded`, `Closed` and `Realized` proofs
for a cache that retains the complete supported normalized histories. A finite
list of member values or origins alone does not establish that closure.

For an observable Effect, `effect_image_of_assignment` now explicitly needs
`observed : Nonempty (model.effect c).Position` as well as terminal suppliers,
origin/provenance and availability proofs. Keep that witness when reusing
stationary evaluation and projection lemmas; a nominal boundary list is not
the derived position type.

Handle `ConeStatus` by its alternatives. `.observable` supplies `ConeValid`;
`.unobservable` supplies `NoObservableEffect`. `NoObservableEffect.not_reachable`
and `.exact` reuse the empty incoming images and empty independent contract;
their equality of empty relations is not inhabited success. `hasCone` supplies
a status only. With a separately proved reachable tuple,
`ConeStatus.valid_of_reachable` yields `ConeValid`. `BoundariesComplete` takes
the proved-unobservable alternative or an actual structural boundary path.
Neither branch removes per-generator source obligations or universal inputs.

`Term.history_injective` recovers typed producer terms from their structural
history. `Expression.supply_preserves_provenance` lifts distinct histories
through any finite unmarked shared suffix; every downstream Operation is still
declared once. Operation equality, equal member images and local algebraic
normalization do not identify those histories. `SharedTargets` provides complete
scoped certificates; `SharedTargetJoin` separately proves the full input-context
obligations of an explicitly supplied C ⊗ C → R.
