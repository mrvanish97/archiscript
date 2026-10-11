# Stage 3 — Compositional proof authoring

This is an **AI-agent working procedure**, not a new ArchiScript calculus.
Stage 3 retains the meaning of `Partition`, `Operation`, `Expression`,
tensor, coproduct, refinement, and the original architecture theorem. The
human reviews architecture diagrams, contract claims, evidence, and unknowns;
the agent authors Lean and Lean checks it.

## Success criterion

Given a declared architecture theorem `G`, construct a Lean proof of **that
same `G`** from smaller, explicitly proved claims when helpful. A shorter
statement or reduced carrier is not a successful optimization. Prefer lowering
the time to the first fully checked proof, including AI retries and Lean
verification, over minimizing source lines or generating more lemmas.

This procedure has no universal optimum: the agent must exercise mathematical
judgment. A direct proof remains valid if splitting does not help.

## Authoring loop

1. **Fix the original goal.** Preserve its types, definitions, and assumptions.
   Identify precisely what it says; distinguish architectural semantics from
   unmodeled runtime effects.
2. **Inspect rather than expand.** Look at the source `Expression` tree, the
   operation's intermediate codomains, tensor coordinates, coproduct summands,
   consumer-specific resolution maps, and already compiled theorem names.
   Use actual public API names, not guessed helper theorems.
3. **Choose candidate cuts by the goal.** Prefer an intermediate VDP already
   declared in the architecture, a genuine independent tensor factor, an
   explicit coproduct branch, or a proved factorization of the relevant
   consumer. Do not choose a cut merely because it makes a diagram smaller.
4. **State the smallest useful obligations.** Write what must be shown locally
   and the existing structural law that would assemble the result. If the
   assembly law is missing, either prove a reusable law from current semantics
   or choose another route. Avoid implicit assumptions.
5. **Prove and check locally.** Use `intro`, `cases`, `simp`, `rfl`,
   `decide`, or extensionality on bounded, well-chosen obligations. Do not
   globally expand a product unless genuinely needed. Prefer a named theorem
   for a reusable mathematical fact.
6. **Assemble the original theorem.** Use existing composition, monoidal,
   coproduct, refinement, factorization, and `Expression.Rewrite` laws.
   Check that the final theorem is literally the required claim; no
   `sorry`, `admit`, invented axioms, or proof by narrowing the carrier.
7. **Review and measure.** Run `lake build`; for skill or public API changes,
   also run `lake env lean skills/archiscript/examples/CurrentApi.lean`.
   Record any unverified steps honestly. Present the meaning of the checked
   result and remaining engineering questions without requiring the human
   to read the Lean derivation.

## The key nontrivial example: ReservationController

The checked example
[`ArchiScriptExamples/ReservationController.lean`](../../../ArchiScriptExamples/ReservationController.lean)
provides three entry routes (user, payment, expiry) to a common
`reservationMutationPartition`. The consumer
`inventoryEffect` factors through `forgetInventoryMutationDetail`:

- `inventoryEffect_factorizes` proves the **local** equality involving
  just the reservation-mutation members.
- For a larger source `S` and producer `p : Operation S
  reservationMutationPartition`, composing this equality with `p` and
  using `Operation.comp_assoc` proves the corresponding **global**
  equality. The proof need not enumerate all source input combinations.
- But `publishMutation_does_not_factorThrough_inventoryView` proves
  that the **same** cut cannot be used for the outbox consumer: cancelling
  and expiring lead to different messages. The cut depends on the
  consumer and its proved mathematical property.

This is a guide to discovering local proofs, not permission to collapse
architectural states or assert a global factorization without proof.

## Existing assembly mechanisms

- `Operation.ext`: reduce operation equality to pointwise equality.
- `Operation.comp_assoc` and `Operation.tensor_comp`: build from
  composition and independent factors.
- `Expression.Rewrite.{comp,tensor,copair,trans}`: lift local
  denotation-preserving rewrites through expression constructors.
- `Expression.Transport`: use only with explicit endpoint isomorphisms
  and its commuting condition.
- `Operation.FactorsThrough`, `Operation.ConstantOnFibers`, and
  `Operation.firstFiberConflict`: reason about whether a particular
  consumer admits a given coarsening; a conflict is evidence *against*
  that decomposition, not a reason to delete the offending cases.

Do not assume that an arbitrary proposition has a tensor/coproduct
congruence theorem. The agent must locate or prove the exact assembly
lemma for the property at hand.

## What to avoid

- Turning every declaration into a theorem or every `rfl` into a
  named architectural guarantee.
- Replaying expensive proofs instead of importing established results.
- Using `Operation.tensor` to duplicate a single shared input for
  multiple consumers; it requires independent source coordinates.
- Treating `Operation.run = none` as an impossible input state.
- Replacing a global theorem with an easier theorem that assumes its
  desired conclusion.
- Creating a new architectural VDP or changing architectural boundaries
  solely to simplify tactics.
- Adding a generic proof planner, `archi_decompose` tactic, BDD, or tensor
  network as a prerequisite for this phase.

## Evidence and incremental evaluation

Start with real model obligations, especially `ReservationController`
and other architectural examples. For each selected *same-statement*
comparison, keep the Lean version and environment fixed and record:

- the original theorem and unchanged model revision;
- whether the method is direct, local/compositional, or a deliberate
  fallback;
- wall-clock time to a checked result, including unsuccessful agent
  iterations, and the Lean build/check time measured separately;
- the local lemmas introduced or reused and whether they have a genuine
  consumer.

Use the Lean profiler or heartbeats when diagnosing a hotspot, not as
an oracle predicting the best proof split. Comparisons require actual runs;
do not fabricate speedups or infer asymptotic guarantees from a single
example. An AI-generated proof is complete only when Lean has accepted it.
