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
preserve occurrences even when nominal nodes, VDPs and member images coincide. Each generator contains its actual typed
`Inputs`; all factor suppliers must exist. Its local-factor proof is required.

`Expression` is exclusively a finite linear chain over registered names and
nominal objects. Repetition through a cycle is permitted. Nonlinear algebraic
syntax is `Presentation`; its finite selected `Family` is a presentation aid,
never a Cone-completeness proof.

`ArchitectureSignature.Term` records finite supplier provenance. It is not a
single linear Expression or an implicit copying Operation. Root instances and
producer histories remain distinct. `DeclaredArchitecture.isInputContext`
derives local use contexts from actual source occurrences and the Cone's root.

Declare boundary and availability semantics in `DeclaredArchitecture`, followed
by independently authored `admissibleInput` and `admissibleEffect` contracts.
`incoming` is calculated from each upstream supplier before the current join's
restriction. Check complete n-ary tuples: pairwise compatibility is insufficient.
The full tensor remains unchanged even when both `Reach` and `Adm` are proper
subsets. Neither an Expression nor a factor must reach all target members.

`InputValid` requires exact tuple agreement and every coordinate projection.
Certification quantifies over derived contexts, not a selected list.
`InputStatus.verified` also requires a reachable tuple. Proved-unreachable uses
are reported separately. A bare unused product receives no architectural verdict.

For cycles, supply a typed `Term.CycleBoundary` at the chosen observation point:
a real route with one typed entry hole and explicit auxiliary suppliers.
Repeated visits enlarge the boundary's image; they do not add tensor factors.
Reference semantics includes all finite derivations, including cross-Cone
recursive dependencies. It does not imply termination, eventual identity,
execution order or physical storage.

`effectNodes` finds boundary points; it does not enumerate complete coordinates.
Supply `effectAnalysis : ProvenanceAnalysis cyclicBoundary`, with explicit roots
and derived history entries. Certification requires `effectCoverage : Valid`:
all roots, seeds, every full-source expansion and realized normalized histories.
Its soundness/completeness proofs cover every finite supported supplier derivation.
`effectCoordinates` pairs each boundary with each retained history; repeated C
positions are valid. `BoundariesComplete` and `ConeValid` require nonempty effects,
exact full-tuple agreement and independent upstream projections.
`causeNonempty` is mandatory for `CertifiedDeclaredArchitecture`; an empty Cause
inventory cannot pass as a complete architecture.

A finite computation needs a complete enumeration of semantic configurations,
not merely finite VDP members. `Reachability.FiniteAnalysis.certify` returns an
exact result only after checking closure. `ExactAbstraction` must connect it to
the architectural relation. An unchanged terminal image is not a stopping test. The provenance basis also
needs finite roots and closure of normalized histories; finite VDP members do
not imply that condition. The optional `derive_provenance([roots], fuel)` helper
(import `ArchiScript.Provenance.Derive`) caches candidate data only. Too little
fuel fails the required coverage proof; no domain claim or proof is generated.

## Verify and communicate

```bash
uv run --no-project python scripts/verify-lean.py
```

This runs the pinned build, public smoke, transitive axiom audit, negative
fixtures and kernel replay. Reports under `.lake/reports` identify checked
sources and commands. Builds treat warnings as errors. Audit rejects direct or
transitive `sorryAx`, unauthorized axioms and tagged conditional certificates.
Actual installed input/effect contracts of all closed models and certificates
are checked regardless of tags, including inline, indirect and opaque aliases.
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
