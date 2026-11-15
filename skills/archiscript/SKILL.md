---
name: archiscript
description: Author and verify ArchiScript 0.7 Lean architectural models, semantic Subdomains, VDPs, linear Expressions, contextual tensor uses and Cone Effects. Use for ArchiScript modeling and migration, not unrelated Lean code.
---

# ArchiScript 0.7 authoring

Model possible semantic values and member consequences explicitly. Lean checks
the obligations in that model. External boundary truth, omitted requirements,
implementation conformance and runtime liveness remain outside those proofs.

**Global Cone/Expression coverage: NOT AUTOMATICALLY VERIFIED.**
`CertifiedDeclaredArchitecture` certifies the declared objects and derived
contexts of its stated scope. It is not a globally exhaustive architecture
certificate. The architect claims a complete primitive and one-Cause Cone
inventory; automatic universal path coverage is next-version work.

Do not infer that the union of declared Cones covers every generated finite
typed Expression from successful per-Cone proofs, local `effectCoverage`, a
selected path family or a passing verification gate. State this missing global
guarantee in model handoffs alongside the actual certificate scope. Omitted
real-world Operations and requirements remain an author responsibility.

## A priori semantic modeling / anti-hidden-branching

For each nontrivial model, complete this checklist before claiming its
downstream consequences. The [README explanation](../../README.md#a-priori-possibility-space)
and [worked examples](../../README.md#click-wait-and-timeout) explain the purpose:
make an omitted distinction an explicit modeling obligation instead of hiding
it in apparent implementation behavior.

1. Name one concrete external event per Cause, its sole starting VDP
   (`start c` / `object (start c)`) and its complete **meaningful** boundary
   carrier. Record external assumptions, unavailable information and unknown
   real-world completeness. Multiple consequences of that event do not create
   multiple initial VDPs or invocations. Information may also enter from
   explicitly declared external Causes, suppliers, context and later joins;
   do not require every fact in every Cone's first VDP.
2. State the outcome-relevant distinctions **before constructing arrows**.
   Define inhabited, disjoint, exhaustive member predicates over the honestly
   scoped carrier; do not back-fit it to convenient outcomes. A singleton
   `Click` cannot support three inhabited disjoint members. A declared scenario
   carrier can include readiness history/environment without asserting that
   the program predicts it. Possible PRNG/CSPRNG output classes require neither
   predictable samples nor probability weights; a VDP contains no distribution.
3. Check every source member of every Operation: at most one defined target
   **for that Operation**. Use `Operation.single_output` to diagnose a request
   for both `i → y₁` and `i → y₂` with unequal targets. Refine meaningful input
   semantics, add an explicitly sourced factor or justify context-specific
   semantics before asserting the map. Explain deliberate partiality: `none`
   is undefinedness, not a hidden alternative or runtime non-execution.
   Preserve genuine separate outgoing Operations as non-exclusive fan-out.
4. At every declared supported tensor use, identify each actual **producer
   occurrence**, its Cause, history, availability and shared-source correlation.
   Keep the full abstract Cartesian product. Independently derive each incoming
   image $I_i$ from its supplier **before** restricting the join. Independently
   author a full-tuple $\operatorname{Adm}_t$; prove **P**:
   $\forall i,\ \pi_i(\operatorname{Adm}_t)=I_i$, then **E**:
   $\operatorname{Reach}_t=\operatorname{Adm}_t$, or report the failed/unsupported
   obligations. P is necessary coverage, not sufficient joint behavior. Apply
   both to internal and cross-Cone joins, supported cyclic contexts and terminal
   Effects. A missing factor must surface even when no complete input term can
   be built; never erase the declared use or define its images from accepted
   tuples. Do not set `Adm := Reach` or assume its proof through an unchecked axiom.
5. Diagnose in order: incoming members with no admissible full partner;
   invented incoming projections; $\operatorname{Reach}\setminus\operatorname{Adm}$
   (reachable but prohibited); $\operatorname{Adm}\setminus\operatorname{Reach}$
   (claimed realizable but impossible); n-ary correlations missed by pairwise
   checks. P may fail early; passing it never excuses skipping E. Use actual
   incoming images, not all nominal VDP members: a constant true-only supplier
   needs no partner for unreachable `false`.
6. Do not invent polling loops, scheduler steps, retries, synchronized copies
   or N parameterized Causes merely to mimic implementation waiting. Preserve
   a genuinely declared semantic cycle with its typed boundary. Coproduct OR
   cannot replace simultaneous tensor AND or conceal a missing semantic split.
   Distinct Causes may have equal initial VDPs and feed an explicit cross-Cone
   join. Two simulated invocations of the same Cause are outside the current
   single-event Cone API; a future external multiple-event composition feature
   must not be fabricated here.
7. Report **two separate verdicts**. Level A: the precise mathematical
   obligations proved for the declared local scope, including the API's
   inhabited/unreachable status obligations and named assumptions. P and E
   characterize a local formal contract defined with those obligations.
   Level B: external architectural assumptions and risks requiring human review.
   A valid declared model is necessary evidence, not sufficient proof of overall
   design correctness, completeness, security, performance, fairness or
   implementation conformance. Never infer future runtime knowledge, eventual
   timeout/liveness, or the deferred global generated-Expression guarantee.
   State **Global Cone/Expression coverage: NOT AUTOMATICALLY VERIFIED.**

For click/wait models, [PossibilitySpace.lean](../../ArchiScriptExamples/PossibilitySpace.lean)
proves a broad infinite scenario partition and functional decision map;
[HiddenWaitingBranch.lean](../../Test/Negative/HiddenWaitingBranch.lean) rejects
two distinct outputs from one Operation/source member. For joins, use
[CorrelatedJoin.lean](../../ArchiScriptExamples/CorrelatedJoin.lean),
[TensorVerification.lean](../../ArchiScriptTests/TensorVerification.lean) and
[CrossCone.lean](../../ArchiScriptExamples/CrossCone.lean) for diagonal,
orphan/parity and explicit external-supplier cases. Their current declarations
and [evaluation cases](references/evaluation-cases.md) are authoritative;
the possibility-space example alone is not an architecture certificate.

## Establish the semantics

1. Start from the complete meaningful carrier, retaining invalid, absent,
   unsupported and unsuccessful cases. A successful-leaf union cannot establish
   completeness of a broader input boundary. Carrier values may be infinite.
2. Declare `Subdomain` meanings and ancestry. Each named region requires an
   inhabitant. `Domain` expressions may be empty. Use `Subdomain.child` to retain
   parent restrictions and `Subdomain.remainder` for an explicitly based
   complement. Opaque predicates require an identified boundary and actual
   hypotheses; their names do not prove properties.
3. Prove every declared split with `SemanticSplit`. Siblings must cover their
   parent and be disjoint, with finite nonempty indices. Different trees may
   share a root and overlap across trees. Flat declarations and coarsening
   remain legitimate. `SemanticSplit.refine` proves flattened leaf coverage.
4. Construct `VDP` (the algebra also spells it `Partition`) from declared
   Subdomains with coverage and disjointness proofs. `Partition.ofSplit` reuses
   a split of the entire carrier. `Partition.closed` supports an independently
   justified finite closed carrier. `classify` is a derived classical lookup,
   not a construction field. A candidate lookup can help prove correspondence
   with independently authored meanings; its fibers cannot replace them.
5. Declare `Operation` maps between whole VDPs. Maps may be partial and
   non-surjective. `none` means undefinedness at that member, not runtime
   non-execution. Several outgoing Operations are non-exclusive structural
   routes, without any obligation that they execute.

The public-only [CurrentApi.lean](examples/CurrentApi.lean) constructs semantic
regions, a split, VDPs, an Operation, a linear route and a complete scoped
certificate. It runs the transitive proof audit.

## Declare consequences and prove their contracts

Use `ArchitectureSignature` for the closed primitive, Cause, node, domain and
split inventories. Generator identities and automatically derived histories
preserve occurrences even when nominal nodes, VDPs and member images coincide.
Each generator contains its actual typed `Inputs`; all factor suppliers must
be accounted for by the certificate's `inputSources` field. The signature's
`localFactor` proves an input/output ownership match, not that every input has
a supplier or a reachable value.

`Expression` is exclusively a finite linear chain over registered names and
nominal objects. Repetition through a cycle is permitted. Nonlinear algebraic
syntax is `Presentation`; its finite selected `Family` is a presentation aid,
never a Cone-completeness proof.

`ArchitectureSignature.Term` records finite supplier provenance. It is not a
single linear Expression or an implicit copying Operation. `Term.RootCoherent`
recursively requires each Cause leaf to use its own designated `origin`,
including nested external suppliers. `InCone c t` requires that coherence and
`t.hasRoot c (S.origin c)`. `isInputContext g t` checks the whole input plus a
local supplier in the output owner's Cone; `isInputContext_iff_coherent` derives
that supplier witness from the signature's ownership law. Use
`input_consequence_inCone` for the corresponding Operation result. Multiple
canonical producer paths and cross-Cone joins remain valid. Noncanonical roots
of any Cause are unsupported, even when the owning Cause alone is coherent.
Raw `Term` and `evaluate` can still express such roots; evaluation is no context
or Effect certificate. Equal VDPs, root labels or values do not merge sources.

Declare boundary and availability semantics in `DeclaredArchitecture`, followed
by independently authored `admissibleInput` and `admissibleEffect` contracts.
`incoming` is calculated from each upstream supplier before the current join's
restriction. `supplierImage` independently ranges over all coherent producers
of a node before a complete input exists. Prove mandatory `inputSources` for
**every generator**: `InputSources.grounded` supplies a coherent typed producer
at every factor position, or `.unreachable` proves all independent supplier
images empty at every position. `inputSources_of_catalog` reuses `effectCoverage`
and `SourcesPresent g` for grounding. An inhabited X image with missing Y cannot
use either alternative, regardless of whether a complete term can be built.

`InputValid` requires exact tuple agreement and every coordinate projection.
E means every reachable tuple must be admitted **and every admitted tuple must
be reachable**, including any impossible tuple mistakenly admitted by the author.
Check full n-ary relations; pairwise compatibility and P alone are insufficient.
The full tensor stays unchanged when Reach and Adm are proper subsets. Neither
an Expression nor a factor must reach all target members.

The certificate's universal `inputs` still checks every full coherent context;
the grounding witnesses do not select or restrict those contexts.
`InputStatus.verified` also requires a reachable tuple. `.unreachable` requires
all actual `incoming t` images empty (`noSupplier`), no reachable tuple
(`noTuple`) and no admitted tuple (`noContract`). Report that status separately
from inhabited verification. `CertifiedDeclaredArchitecture.input_partner`
produces a supported full context and an Adm-and-Reach tuple containing each
member witnessed by an independent `supplierImage`. A bare unused product
receives no architectural verdict.

For cycles, supply a typed `Term.CycleBoundary` at the chosen observation point:
a real route with one typed entry hole and explicit auxiliary suppliers.
Repeated visits enlarge the boundary's image; they do not add tensor factors.
Reference semantics includes all finite derivations, including cross-Cone
recursive dependencies. It does not imply termination, eventual identity,
execution order or physical storage.

`effectNodes` finds boundary points; it does not enumerate complete coordinates.
Supply `effectAnalysis : ProvenanceAnalysis cyclicBoundary`, with explicit roots
and derived history entries. Certification requires `effectCoverage : Valid`:
`∀ c, S.origin c ∈ effectAnalysis.roots`, plus `Seeded`, `Closed`, `Realized`.
Do not require finiteness or enumeration of all `RootInstance` values;
`rootHistories` seeds only canonical origins even if other roots occur in the
candidate list. The finite normalized-history cache still needs closure.
Its soundness/completeness proofs cover every finite supported supplier derivation.
`effectCoordinates` pairs each boundary with each retained history; repeated C
positions are valid. `reachEffect` and `ConeValid` require
`Nonempty (model.effect c).Position`: an actual derived coordinate, not just a
nominal boundary name or the tensor unit's value. `ConeValid` also needs a
reachable full tuple, exact contract agreement and all upstream projections.

Supply `cones : ∀ c, model.ConeStatus c`. `.observable` carries `ConeValid`;
`.unobservable` carries `NoObservableEffect`: every `effectIncoming` image and
the entire Effect contract are empty. This can hold with structural positions
but no incoming values; it never claims reached unit success. `BoundariesComplete`
requires, for each owned node, that `NoObservableEffect` proof or a `Depends`
path to a derived boundary. `hasCone` proves the existence of a checked
`ConeStatus`, not necessarily an observable Cone. Neither unobservable status
nor an empty Effect cache bypasses `inputSources` or universal `inputs`.
`causeNonempty` is mandatory for `CertifiedDeclaredArchitecture`; an empty Cause
inventory cannot pass as a complete architecture.

A finite computation needs a complete enumeration of semantic configurations,
not merely finite VDP members. `Reachability.FiniteAnalysis.certify` returns an
exact result only after checking closure. `ExactAbstraction` must connect it to
the architectural relation. An unchanged terminal image is not a stopping test.
The provenance basis also needs canonical-origin coverage and closure of
normalized histories; finite VDP members do not imply that condition. If a model
cannot supply this basis, report the unsupported analysis scope and the outstanding obligation;
do not restrict the carrier, drop producer histories or claim certification.
The optional `derive_provenance([roots], fuel)` helper
(import `ArchiScript.Provenance.Derive`) caches candidate data only. Too little
fuel fails the required coverage proof; no domain claim or proof is generated.

## Verify and communicate

```bash
uv run --no-project python scripts/verify-lean.py
```

This runs the pinned build, public smoke, transitive axiom audit, negative
fixtures and kernel replay. Reports under `.lake/reports` identify checked
sources and commands. The PR Gate CI job runs the same script and saves those
reports as `lean-proof-reports`, including on failure. Cite the checked revision
and report when communicating verification results.

Constructing `CertifiedDeclaredArchitecture` does not itself run the audit or
prove that a contract was independently authored. Run the gate before describing
a concrete model as audited. Builds treat warnings as errors. Audit rejects
direct or transitive `sorryAx`, unauthorized axioms and tagged conditional certificates.
Actual installed input/effect contracts of closed model and certificate
declarations in the checked imports are inspected regardless of tags, including
inline, indirect and opaque aliases. Include the concrete declarations in those
imports; an unimported model is outside that audit run.
Uninspectable closed records are rejected. Tags additionally check standalone
predicates and conditional results. The check conservatively follows transitive
implementation dependencies; it cannot establish independent business meaning.

Use **draft** for incomplete declarations, **conditional** for conclusions with
unsupplied assumptions, and **certified declared contexts** only for completed,
audited concrete certificates. Review approval is not a proof. State the global
coverage exception separately on every complete-model handoff.

## References by task

- Construction, fields and theorem names: [lean-api.md](references/lean-api.md).
- Algebraic reuse and normalization: [compositional-proofs.md](references/compositional-proofs.md).
- Compiler feedback and axiom checks: [proof-engineering.md](references/proof-engineering.md).
- Regression scenarios: [evaluation-cases.md](references/evaluation-cases.md).
- Human-facing views: [review-diagrams.md](references/review-diagrams.md).
- Optional legacy review tooling: [review-packs.md](references/review-packs.md).

Shared targets preserve distinct producer derivations automatically. One C
and one shared h;k declaration can yield two Effect coordinates of the same VDP;
equal members, images or suffixes do not merge those coordinates. Only an
explicit, fully supplied tensor-source Operation performs an architectural join.
The candidate Effect tensor is an analytical product, not that Operation.
`effectCoverage` checks a seeded, closed and realized finite provenance basis;
`EffectProvenance` prevents substituting a different producer in a coordinate.
Typed cyclic markers separately aggregate repeated traversals of their actual
return routes, while reference reachability retains every finite traversal.
