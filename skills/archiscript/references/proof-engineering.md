# Proof engineering: Lean tactic discipline and diagnostics

Read this reference when constructing, repairing, or evaluating a nontrivial
ArchiScript Lean proof. The main [skill](../SKILL.md) owns the mathematical
authoring method; this file covers **how to prove its unchanged obligations
efficiently**. It does not define a second calculus, revise the architecture,
or authorize new axioms.

## Freeze the goal before choosing tactics

Record the full proposition (source and target VDPs, hypotheses, implicit
parameters, and partiality), relevant definitions, and model revision.
Optimizing a proof must not narrow carriers, delete tensor members, invent
factorization, turn `none` into an impossible source, or strengthen assumptions.
If the model needs revision, treat that as architecture design and review, not
as proof optimization.

## Goal triage: structure before unfolding

For a nontrivial goal, use this order as a **default**, not a rigid tactic
language:

1. **Find an applicable theorem.** Inspect exact imported declarations and
   theorem signatures first. Common candidates: `Operation.comp_assoc`,
   `Operation.tensor_comp`, coproduct injection/copair laws,
   `Expression.Rewrite` congruence, and proved `PartitionIso` transports.
2. **Decompose only where mathematically justified.** State the local
   premises and the law that will reconstruct the *original* global claim.
   A joint consumer is not a tensor of separate consumers merely because its
   input is a tensor.
3. **Reuse or prove meaningful local lemmas.** Place them at existing semantic
   interfaces. Avoid one named lemma per `rfl` or structural field.
4. **Assemble before unfolding.** Prefer `exact`, `apply`, `rw`, and short
   `calc` chains. Use `Operation.ext` for operation equality when an existing
   structural theorem does not close the goal.
5. **Reduce locally.** Use `change` or `simp only` with the needed definitions
   on the remaining atomic obligation. Prefer targeted rewrites over repeated
   wholesale unfolding of `Expression.denote`, `Partition.tensor`, or
   `Operation.tensor`.
6. **Enumerate last.** Use `cases`, `by_cases`, or `decide` for genuinely
   small, irreducible finite goals. Keep product indices abstract as long as
   the proof can use a structural law.

An existing compositional proof may be *both* shorter and easier for Lean to
check, but never assert a performance gain without measurement. Some goals
really do depend on cross-factor cases; a direct finite proof is legitimate.

## Tactic choices by goal

| Shape | First useful technique |
| --- | --- |
| Exact category or tensor law | `exact` / `rw` using the library law |
| Equality of two `Operation` values | `Operation.ext` and one abstract source member |
| Composition of independent tensor maps | `Operation.tensor_comp` before splitting a product member |
| Coproduct injection followed by copairing | Existing copair/injection equation |
| Expression subtree rewrite | `Expression.Rewrite.comp`, `.tensor`, `.copair`, `.trans` |
| Structural endpoint transport | Proven `PartitionIso` with `Expression.Transport` |
| Consumer coarsening | `Operation.FactorsThrough` or conflict analysis, with correct theorem direction |
| Small classifier predicate | Targeted cases and `simp only` on local definitions |

Do not treat `FactorsThrough` and `ConstantOnFibers` as interchangeable
without the required hypotheses and direction. A valid coarsening for inventory
may fail for outbox. See [compositional-proofs.md](compositional-proofs.md) and
the compiled `ArchiScriptTests/ProofEngineering.lean` regressions.

## Investigate an expensive proof

When the elaborator times out, heartbeats are exceeded, or a compile becomes
slow:

1. Identify the *specific* theorem or command, not just the failing module.
2. Inspect the relevant goal shape, repeated unfolding, and product/branch
   case splits. Avoid guessing that the entire model is too large.
3. Isolate and check meaningful local lemmas; reuse the checked results in
   the original theorem.
4. Where useful, inspect Lean's available profiling diagnostics (for example,
   `set_option trace.profiler true in` around a particular command; verify the
   option on the pinned toolchain before relying on it).
5. Retry with targeted rewrites or theorem application. Only consider
   increasing `maxHeartbeats`, recursion limits, or memory after diagnosing
   a legitimately costly residual goal. Record the rationale and effect.
6. Recheck the **same** proposition, imports, model and assumptions.

Do not turn a proof failure into `sorry`, `admit`, an invented axiom, a
narrower source, or an unchecked `opaque` shortcut. A failing factorization
may be important architectural evidence, not a performance defect.

## Verify incrementally

- Check local assertions before incorporating them into a deep controller proof.
- Build the full project with `lake build`.
- Check public API smoke with
  `lake env lean skills/archiscript/examples/CurrentApi.lean` when the skill
  or authoring workflow changes.
- Preserve negative tests and the counterexample that rejects outbox
  factorization through the inventory coarsening.
- A successful compilation establishes the stated theorem in Lean, not
  adequacy of the external carrier or production conformance.

## Benchmark proof cost, not a different model

Use [../../benchmarks/proof-authoring/README.md](../../../benchmarks/proof-authoring/README.md)
for a reproducible same-goal evaluation. Record:

- Exact theorem statement, hypotheses, model revision, and Lean toolchain.
- Import/compilation cache conditions; separate prerequisite build from proof
  checking where feasible.
- Wall time and peak memory, plus profiling hotspots.
- Human/AI proof attempts and time to first successful accepted proof.
- Meaningful helper-lemma count and source size.
- Failed runs and negative results, without invented acceleration claims.

Benchmark A (direct), B (unstructured AI), and C (local-first AI) are
comparable only when they establish the *same* proposition. A controlled
synthetic tensor case may measure scaling but must not replace the real
`ReservationController` regression.

## Do not broaden the calculus

No BDD, SAT engine, tensor-network solver, probability semantics, resource
ontology, whole-architecture equivalence, or new normalization rule is part
of this proof-engineering workflow.
