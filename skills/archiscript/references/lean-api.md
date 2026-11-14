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
`input`/`output`/`operation`, and `localFactor`.

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
`admissibleInput`, `cyclicBoundary`, `effectContext`, `admissibleEffect`.
`evaluate` is a noncomputable reference denotation of finite derivations;
`Evaluates` is its relational form. `Evaluates.deterministic`,
`Evaluates.supplier` and `defined_consequence` are proved. `InCone` requires the
specified originating root and preserves its identity.

`isInputContext` derives ownership from real supplier provenance. `incoming`
is independent of current join acceptance. `reachInput` includes the stated
availability context. `InputValid` requires exact agreement and projections;
`InputStatus` distinguishes inhabited verification from proved unreachability.

`effectNodes` derives terminal and cyclic-boundary occurrences from the closed
inventory. `effect`, `effectIncoming`, `reachEffect`, `ConeValid` and
`BoundariesComplete` expose the required Cone obligations. Empty effects cannot
receive a successful certificate through the tensor unit.

`CertifiedDeclaredArchitecture` requires `model`, `causeNonempty`, universal `inputs`, `cones`
and `boundariesComplete`, plus `terminalOccurrencesFaithful` for distinct natural
terminal producers. Its scope is declared contexts. **Global
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

Natural terminal producers must remain distinct: the mandatory
`terminalOccurrencesFaithful` proof prevents two independent arrows from being
collapsed into one unmarked terminal slot. A typed cyclic marker explicitly
selects the boundary at which repeated entries/feedback visits are aggregated.
