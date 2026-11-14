# ArchiScript

A Lean calculus for making architectural assumptions and member consequences
explicit before implementation.

**0.7.0 semantic-core rewrite — pending architect review.**

**Global Cone/Expression coverage: NOT AUTOMATICALLY VERIFIED.** Certificates
cover the declared semantic objects and derived contexts described below.
Universal coverage of every generated path by the declared Cones is explicitly
next-version work. Real-world inventory completeness is always an author assumption.

## Semantic foundation

Declare a complete meaningful carrier, including failed, invalid and absent
cases. Declare named semantic Subdomains and their ancestry. Prove every declared
split. Select a finite nonempty family of those regions as the VDP's members.

| Concept | Enforced meaning |
| --- | --- |
| `Domain α` | Predicate; intermediate emptiness is permitted |
| `Subdomain α` | Explicit base, definition evidence, containment and inhabitant |
| `SemanticSplit parent` | Finite nonempty children covering the parent, internally disjoint |
| `VDP` / `Partition` | Declared Subdomain members with full carrier coverage and disjointness |
| `Operation X Y` | Possibly partial, non-surjective member map between whole verified VDPs |
| `Expression G X Y` | Finite linear chain of registered Operations between nominal objects |
| `Presentation` | Nonlinear algebraic presentation syntax, separate from linear routes |
| Cause / Cone | One originating Cause, explicit root instance and all supported consequences |
| Contextual Effect | Terminal boundary image or full Cone-effect tuple relation |

Different decomposition trees may share a root and overlap across trees. Flat
member selections and coarsenings remain valid. Every **named** Subdomain is
nonempty; an empty string, array or absence value is not the empty set.
`Partition.classify` is now a derived classical lookup, never a construction field.
Carriers may be infinite while member families remain finite.

The [Stage 2 project-reference regression](ArchiScriptExamples/ProjectReference.lean)
uses verified deductive splits for all eight URI success/failure leaves. Its
symbolic URI/filesystem interpretation is explicit; it is not a parser or a
proof that real filesystem observations are truthful. A counterexample rejects
promoting only the successful leaves into the full URI boundary.

## Operations, tensor and provenance

`g.comp f` composes defined member mappings. `none` denotes mathematical
undefinedness, without a runtime execution claim. Several outgoing Operations
are non-exclusive possible structural routes, with no scheduler or liveness rule.

Tensor preserves the full Cartesian carrier and member product, including self
tensor. Coproduct preserves tagged alternatives. Common-source fan-out creates
no implicit diagonal Operation. At an actual tensor use, the relevant questions are

\[
\forall i,\quad \pi_i(\operatorname{Adm})=I_i,
\qquad \operatorname{Reach}=\operatorname{Adm}.
\]

Here each incoming image is independently obtained from its actual supplier.
`Reach` and the independently authored `Adm` may be proper subsets of the full
product. Neither an Operation nor a factor is required to reach all target members.
Every complete n-ary tuple matters; pairwise checks are insufficient.

`ArchitectureSignature` closes the declared primitive, Cause, node, domain and
split inventories. `Inputs` records actual generator suppliers. Finite provenance
`Term`s retain root instances and producer histories; they are not single linear
Expressions. Equal VDP denotations do not merge nominal nodes or factor positions.
`isInputContext` derives local contexts from their real originating roots.

The reference relation includes every finite derivation from the inventory,
including recursive cross-Cone dependencies. Availability is an explicit
semantic assumption. No default physical persistence, consumption, synchronization
or resource-effect semantics is introduced.

## Cycles and proof-backed checking

A cycle needs a real typed entry and observation boundary. `Term.CycleBoundary`
records a nontrivial return with one entry hole and explicit auxiliary suppliers.
All finite traversals contribute to one boundary image. They do not create one
terminal tensor factor per iteration.

Reachable sets may stabilize while the Operation continues alternating.
[The swap example](ArchiScriptExamples/CyclicCone.lean) proves both facts and
connects its boundary image to a finite exact analysis through `ExactAbstraction`.
A finite VDP alphabet does not imply finitely many occurrence histories.
`FiniteAnalysis.certify` checks closure of the entire analyzed state before
returning an `Exact` result; an unchanged terminal projection is insufficient.

`CertifiedDeclaredArchitecture` requires a nonempty Cause inventory and proofs for all derived local input
contexts, every declared Cone's full Effect, and terminal-boundary completeness.
A verified use must have an actual reachable tuple. Proved-unreachable contexts
are separate. A Cone with no reachable full Effect cannot pass as tensor-unit
success; it remains outside this complete-effect certificate's supported scope.

Certificates establish necessary obligations of the declared model. They do not
establish missing real-world requirements, production-code conformance, fairness,
termination, races or physical concurrency.

## Algebra retained

The calculus retains partial-map identity/associativity, symmetric monoidal
coherence/naturality, coproduct universal properties, canonical tensor/coproduct
distributivity, semantic VDP isomorphisms, refinement/coarsening and conditional
consumer factorization. Isomorphisms now preserve the primary semantic predicates.

`Presentation.Rewrite` checks Operation equality; `Presentation.Transport` checks
an explicit isomorphism square. These are local algebraic facts, not Cone-effect
equivalence. Composition never deletes intermediate nominal objects; a view
hiding them is an architecture projection. Selected `Presentation.Family` values
are useful views, not completeness certificates.

## Build and trust boundary

Lean/Lake are pinned to **4.34.0**. Runtime examples need Node; repository tooling
uses Python through `uv`. Optional review PDFs use Tectonic.

```bash
uv run --no-project python scripts/verify-lean.py
uv run --no-project python -m unittest discover -s scripts -p 'test_*.py'
node --test examples/payment-webhook.test.mjs
```

The first command cleans and builds with warnings as errors, checks the public-library
skill smoke, audits compiled transitive axioms, runs intended-diagnostic negative
fixtures and invokes kernel replay with explicit module names. Reports are in
`.lake/reports/verification.json` and `.lake/reports/axioms.json`. Verification
rejects changing sources, direct/transitive `sorryAx`, custom axioms, extra trusted
computation axioms and tagged conditional certificates disguised as concrete ones.
The conventional allowlist is `propext`, `Classical.choice`, `Quot.sound`.

Tagged admissibility predicates are also checked for dependencies on the Reach
implementation. This prevents a direct self-confirming definition; mathematical
set equality cannot prove independent human business judgment.

## Examples and authoring

- [Public-only smoke](skills/archiscript/examples/CurrentApi.lean): explicit regions, split, VDP, primitive inventory and scoped certificate.
- [Correlated join](ArchiScriptExamples/CorrelatedJoin.lean): common-source diagonal and constant non-surjective supplier.
- [External cyclic supplier](ArchiScriptExamples/CrossCone.lean): one local and one external factor with typed cyclic observation.
- [Mutually dependent Cones](ArchiScriptExamples/MutualCones.lean): joint reference semantics and certified finite query analysis.
- [Distinct terminal occurrences](ArchiScriptTests/TerminalOccurrences.lean): two sinks with the same VDP retain separate correlated Effect coordinates.
- [ReservationController](ArchiScriptExamples/ReservationController.lean): retained algebraic stress model, with nonlinear Presentations and linear primitive-consumer routes.
- [Migration and release evidence](docs/0.7.0-release.md): file dispositions, assumptions, tests, gate status and limitations.
- [Next-version backlog](plans/0.8.0.md): universal coverage and scoped analysis improvements.

The [authoring skill](skills/archiscript/SKILL.md) and every reference were rewritten
for 0.7. Legacy workflow modules (`Boundary`, `Review`, `Operation.Declaration`,
registry-based parameterization) remain explicit companion imports. Their approval
and binding records are not part of mathematical certification. Existing webhook
review packs are draft projections, not new Cone certificates.

See [CONTRIBUTING.md](CONTRIBUTING.md) for the repository's PR/merge policy and
[LICENSE](LICENSE) for licensing.

Natural terminal producers must remain distinct: the mandatory
`terminalOccurrencesFaithful` proof prevents two independent arrows from being
collapsed into one unmarked terminal slot. A typed cyclic marker explicitly
selects the boundary at which repeated entries/feedback visits are aggregated.
