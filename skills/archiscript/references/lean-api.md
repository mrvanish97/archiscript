# Implemented 0.7 API

The compiled [public smoke](../examples/CurrentApi.lean) is the executable
construction example. These names refer to real Lean declarations, not the
historical TypeScript notation.

## Semantic declarations

| API | Required evidence / meaning |
| --- | --- |
| `Domain α` | Predicate; intermediate emptiness is allowed |
| `DomainDerivation α meaning` | Definition evidence indexed by its exact predicate; `.named` retains semantic identity, `.opaque` records an assumption boundary |
| `Subdomain α` | `name`, `base`, `parent`, `meaning`, `contained`, `definition`, `nonempty` |
| `Subdomain.root` | Explicit meaning, definition evidence and inhabitant |
| `Subdomain.child` | Parent intersection with the remaining criterion; inhabitant required |
| `Subdomain.remainder` | Parent-relative complement, containment and inhabitant required |
| `SemanticSplit parent` | Finite nonempty `Index`; declared `children`, `within`, `covers`, `disjoint` |
| `SemanticSplit.complement` | Positive region and nonempty parent remainder form one proved split |
| `SemanticSplit.refine` | Flatten verified child splits with inherited coverage/disjointness |
| `VDP` / `Partition` | Carrier type, finite nonempty member indices, declared Subdomains, `coverage`, `disjoint` |
| `Partition.ofSplit` | Split plus proof that its parent is the entire carrier type |
| `Partition.closed` | Exhaustive finite carrier enumeration, constructor-equality meanings |

`Partition.member` is the declared member predicate. `member_nonempty`,
`member_unique`, `coverage` and `disjoint` concern those predicates directly.
`Partition.classify` is noncomputable and derived from coverage; `classify_spec`
and `self_member` prove its correspondence. `lookup` additionally needs a
computable member enumeration and decidable membership. It is not a VDP field.

## Algebra and linear paths

`Operation.run` maps source indices to `Option` target indices. `id`, `comp`,
`tensor`, `copair`, coproduct injections, associator, unitors, symmetry and
canonical distributivity keep their mathematical meaning. `Operation.image`
restricts to specified inputs; `image_comp` proves image composition and
`single_output` rejects member-level nondeterminism.

`Partition.PartitionIso` contains carrier and member-index isomorphisms plus
`preserves`, the semantic-member correspondence. Its `classify_commutes` is now
a derived theorem. `RefinesVia`, `coarseningMap_surjective`, `FactorsThrough`,
`ConstantOnFibers` and the proved factorization APIs remain available.

`Generators` associates registered names with nominal `Object`s, semantic
`object` VDPs, `source`, `target` and `operation`. `Expression G X Y` has only
`identity` and `step`. `append`, `denote_append` and `image` preserve linearity.
Nominal objects remain distinct even if their VDP denotations coincide.

The old tree-shaped syntax is `Presentation`, with `denote`, `Family`,
`Rewrite` and `Transport`. Equality of Operations or a commuting VDP-isomorphism
square certifies a local algebraic rewrite. It does not establish Cone-effect
or provenance equivalence.

## Declared architecture and consequences

`ArchitectureSignature` contains exhaustive lists for `Node`, `Cause` and
`Generator`, verified `object` VDPs, the closed `domains` and `splits` inventories,
`memberDeclared`, `RootInstance`, `origin`, `start`, `owner`, typed generator
`input`/`output`/`operation`, `generatorDecidableEq`, and `localFactor`.

`Inputs` is supplier syntax on an existing generator: `unit`, `node`, `tensor`.
`vdp` gives the full mathematical object; `Position`, `nodeAt`, `coordinate`
and `coordinate_assign` retain individual factors. No tensor-specific nominal
entity is declared.

`ArchitectureSignature.Occurrence` specializes `Term` to have no holes. Its
constructors are `cause`, `operation`, `tensor`, `unit`. Root instances and full
producer derivations preserve provenance. `Term.supplier` selects a factor.
`Term.CycleBoundary` uses a typed hole family solely to witness a genuine cyclic
entry/observation route; `oneEntry` and `nontrivial` are mandatory.

`DeclaredArchitecture` supplies `boundary`, `boundaryNonempty`, `context`,
`admissibleInput`, `cyclicBoundary`, `effectAnalysis`, `effectContext`, `admissibleEffect`.
`evaluate` is a noncomputable reference denotation of finite derivations;
`Evaluates` is its relational form. `Evaluates.deterministic`,
`Evaluates.supplier` and `defined_consequence` are proved. `InCone` requires the
specified originating root and preserves its identity.

`isInputContext` derives ownership from real supplier provenance. `incoming`
is independent of current join acceptance. `reachInput` includes the stated
availability context. `InputValid` requires exact agreement and projections;
`InputStatus` distinguishes inhabited verification from proved unreachability.

`effectNodes` derives boundary nodes. `Term.history` is injective on typed
occurrences (`history_injective`). `Term.provenance` normalizes only matched
marked typed returns; it preserves other producer histories.
`Expression.supply_preserves_provenance` proves preservation through any finite
unmarked shared suffix, with one declaration of every downstream Operation.

`ProvenanceAnalysis` contains roots and a finite cache of (Cause, Node, History).
`Valid` requires root completeness plus `Seeded`, `Closed`, `Realized`; `complete`
and `sound` connect the cache to all finite local-root supplier derivations.
`effectCoordinates` derives (Node, History) positions, and `effectInputs` their
full tensor. `EffectProvenance` binds each actual supplier to its position;
`effectIncoming` and `reachEffect` require it. `terminal_positions` proves that
every supported boundary derivation has a coordinate. `effect_realized` gives
actual typed suppliers, without claiming reachable values or runtime execution.
`ConeValid` and `BoundariesComplete` retain the full semantic obligations.
Empty effects cannot receive a successful certificate through the tensor unit.

`CertifiedDeclaredArchitecture` requires `model`, `causeNonempty`, universal `inputs`, `cones`
and `boundariesComplete`, plus `effectCoverage : model.effectAnalysis.Valid`. Its scope is declared contexts. **Global
Cone/Expression coverage: NOT AUTOMATICALLY VERIFIED.**

`CertifiedDeclaredArchitecture.hasCone` proves the existence of an actual valid
Cone; an absent Cause inventory cannot acquire a vacuous complete certificate.

## Computation and trust

`Reachability.Reach` is inductive finite-transition closure.
`FiniteAnalysis.compute` is bounded saturation; `compute_sound` and
`compute_complete_of_closed` prove correctness. `certify` returns an `Exact`
result only after closure is checked. `ExactAbstraction` and
`certified_abstraction` connect an analysis to architectural semantics.

`Verification.missing`, `unexpected` and `unpartnered` return concrete tuples
or upstream members, with witness theorems. `checkAgreement_correct` needs a
complete tuple enumeration and decidability of both relations.

Development tools import `ArchiScript.ProofAudit` explicitly. Tag concrete
closed results with `@[archiscript_certificate]` and independent predicates with
`@[archiscript_contract]`. `#audit_archiscript` inspects all project declarations,
including private declarations, and rejects unauthorized transitive axioms.
Conventional `propext`, `Classical.choice`, `Quot.sound` are the only allowlist.

Shared targets preserve distinct producer derivations automatically. One C
and one shared h;k declaration can yield two Effect coordinates of the same VDP;
equal members, images or suffixes do not merge those coordinates. Only an
explicit, fully supplied tensor-source Operation performs an architectural join.
The candidate Effect tensor is an analytical product, not that Operation.
`effectCoverage` checks a seeded, closed and realized finite provenance basis;
`EffectProvenance` prevents substituting a different producer in a coordinate.
Typed cyclic markers separately aggregate repeated traversals of their actual
return routes, while reference reachability retains every finite traversal.

The optional `ArchiScript.Provenance.Derive` import provides
`derive_provenance([roots], fuel)`. It normalizes candidate data one cached layer
at a time; `Valid` is still proved by ordinary kernel reduction. A finite closed
normalized-history basis is a supported-fragment obligation, separate from
finite member values and from the deferred global Cone/Expression coverage.
The audit exposes actual admissibility fields of every closed declared model
and certificate, follows opaque/indirect aliases, and rejects uninspectable
records. Attributes do not opt a closed record out of this check. Conditional
factories are inspected at their concrete closed instantiations.
