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

### Canonical origins and supported contexts

`ArchitectureSignature.Term.RootCoherent` recursively requires `root = S.origin c`
at every `cause c root` leaf, including nested external suppliers. One Cause has
one designated event occurrence; multiple producer paths from that occurrence
remain legitimate. Distinct Causes may have equal VDPs and equal root labels
without becoming the same source. A noncanonical root of **any** Cause makes a
derivation unsupported, even if the output-owning Cause has only canonical roots.

`DeclaredArchitecture` supplies `boundary`, `boundaryNonempty`, `context`,
`admissibleInput`, `cyclicBoundary`, `effectAnalysis`, `effectContext`, `admissibleEffect`.
`evaluate` is a noncomputable reference denotation of finite derivations;
`Evaluates` is its relational form. `Evaluates.deterministic`,
`Evaluates.supplier` and `defined_consequence` are proved. Raw `Term` and
`evaluate` still admit noncanonical roots; evaluating such a term does not prove
it is a supported context or Cone consequence. `evaluate_inputContract` proves
that changing `admissibleInput` does not change reference evaluation.

`InCone c t` is `t.hasRoot c (S.origin c) ∧ t.RootCoherent`.
`isInputContext g t` requires whole-input coherence and a supplier in the
output owner's Cone. The signature's `localFactor` proof lets
`isInputContext_iff_coherent` derive that ownership witness for every coherent
full input. `input_consequence_inCone g t context` puts the corresponding
Operation result in its owner's Cone. These are provenance/scope facts, not
proofs of reachable values or independent tuple-contract validity.

### Generator sources and tuple contracts

| API | Required evidence / meaning |
| --- | --- |
| `supplierImage n member` | Some coherent upstream producer of `n` evaluates to `member` in an allowed boundary world; no complete join input is needed |
| `InputSources.grounded` | A coherent typed supplier exists at **every** factor position of the declared generator |
| `InputSources.unreachable` | Every independent `supplierImage` at every input position is empty |
| `inputSources_of_catalog` | A valid provenance cache plus `SourcesPresent g` supplies the `grounded` evidence |
| `incoming t i member` | Image of the actual supplier `t.supplier i`, independent of the current join's admissibility |
| `reachInput g t tuple` | Complete input evaluates in a boundary world satisfying the stated availability `context` |
| `InputValid g t` | Exact full-tuple Reach/Adm agreement and all coordinate projection equalities |
| `InputStatus.verified` | `InputValid` plus a reachable full tuple |
| `InputStatus.unreachable` | `noSupplier`: every actual `incoming t` image empty; `noTuple`: no reachable full tuple; `noContract`: no admissible full tuple |

Exactness quantifies over **every** full tuple: each reachable tuple is admitted
and each admitted tuple is reachable. An impossible tuple admitted by mistake
lies in Adm minus Reach and fails E; it is not excluded from the comparison.

The per-generator source obligation is separate from universal checks over full
coherent contexts. `grounded` is structural evidence, not a joint-reachability
proof or a selected list of contexts. A supplied X with unsourced Y cannot pass
either source alternative: Y prevents grounding, while X refutes global image
emptiness. `localFactor` alone establishes neither alternative.

`CertifiedDeclaredArchitecture.input_partner g i member supplied` takes an
independent `supplierImage` witness and produces a supported **full** input
context, an admissible and reachable full tuple, and its matching coordinate.
The supplied member is thus accounted for even before a complete input was
chosen. The theorem does not assert that all Cartesian combinations are
reachable or require surjectivity onto every nominal VDP member. Its concrete
statement is in [Consequence.lean](../../../ArchiScript/Consequence.lean).

### Effect provenance and status

`effectNodes` derives boundary nodes. `Term.history` is injective on typed
occurrences (`history_injective`). `Term.provenance` normalizes only matched
marked typed returns; it preserves other producer histories.
`Expression.supply_preserves_provenance` proves preservation through any finite
unmarked shared suffix, with one declaration of every downstream Operation.

`ProvenanceAnalysis` contains roots and a finite cache of (Cause, Node, History).
`Valid` requires `∀ c, S.origin c ∈ analysis.roots`, plus `Seeded`, `Closed`,
`Realized`. The cache need not enumerate all values of `RootInstance` or prove
that type finite. `rootHistories` seeds only designated origins even if the
list contains other roots. `complete` and `sound` connect the cache to coherent
finite supplier derivations, including cross-Cone dependencies.
The [infinite-root regression](../../../ArchiScriptTests/SourceCoverage.lean)
proves `infiniteRootBasis_valid` for `RootInstance := Nat` with cache roots `[0]`.
`effectCoordinates` derives (Node, History) positions, and `effectInputs` their
full tensor. `EffectProvenance` binds each actual supplier to its position;
`effectIncoming` and `reachEffect` require it. `terminal_positions` proves that
every supported boundary derivation has a coordinate. `effect_realized` gives
actual typed suppliers, without claiming reachable values or runtime execution.

`reachEffect c tuple` also requires `Nonempty (model.effect c).Position`.
These are actual derived positions, not merely nominal boundary names or an
inhabited tensor-unit value. `effect_image_of_assignment` requires this explicit
`observed` premise along with a complete terminal supplier, origin/provenance
proofs, a proved stationary interpretation and availability.
`effect_projection_of_assignment` reuses full Effect exactness and that
interpretation; neither helper applies to arbitrary occurrence-sensitive cycles.

| Status API | Required evidence |
| --- | --- |
| `ConeValid c` | Nonempty **actual** Effect positions, a reachable full tuple, exact independent contract agreement, and every upstream coordinate projection |
| `NoObservableEffect c` | All `effectIncoming` images empty and every `admissibleEffect` tuple false |
| `ConeStatus.observable` | A `ConeValid` proof |
| `ConeStatus.unobservable` | A `NoObservableEffect` proof; no reached unit Effect is claimed |
| `BoundariesComplete` | For every owned node, either `NoObservableEffect` for its Cause or a structural `Depends` path to a derived boundary |

`NoObservableEffect.not_reachable` rules out full Effect reachability;
`NoObservableEffect.exact` proves the two empty relations agree without proving
inhabitation. Unobservable status can apply even when actual positions exist
but all their incoming images are empty. A missing full tuple alone is not
enough. `ConeStatus.valid_of_reachable` recovers `ConeValid` from a checked
status and an actual reachable tuple.

### Complete declared certificate

`CertifiedDeclaredArchitecture` has these mandatory fields:

| Field | Obligation |
| --- | --- |
| `model` | The declared interpretation and independent contracts |
| `causeNonempty` | At least one declared Cause |
| `effectCoverage` | `model.effectAnalysis.Valid` |
| `inputSources` | `∀ g, model.InputSources g`, before any complete-input quantification |
| `inputs` | `∀ g t, model.isInputContext g t → model.InputStatus g t` |
| `cones` | `∀ c, model.ConeStatus c` |
| `boundariesComplete` | The structural-path or proved-unobservable alternative above |

`CertifiedDeclaredArchitecture.hasCone` proves `∃ c, model.ConeStatus c`, not
the existence of an observable `ConeValid`. A source-only event can receive
explicit unobservable status while an empty Cause inventory remains forbidden.
Neither that status nor an empty Effect basis bypasses `inputSources` or `inputs`.
The scope is the declared supported contexts. **Global Cone/Expression coverage:
NOT AUTOMATICALLY VERIFIED.**

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
`@[archiscript_contract]`. `#audit_archiscript` inspects project declarations in
the checked imports, including private declarations, and rejects unauthorized
transitive axioms.
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
The audit exposes actual admissibility fields of closed model and certificate
declarations in the checked imports, follows opaque/indirect aliases, and rejects
uninspectable records. Attributes do not opt a closed record out of this check.
Import concrete declarations instantiating factories to audit their installed
contracts; constructing a certificate alone does not execute the audit.
