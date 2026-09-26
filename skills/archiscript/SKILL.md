---
name: archiscript
description: Author or review ArchiScript architectural contracts in Lean using deductive domain refinement, categorical composition, operation and branch ownership, parameterized routing, and proportionate proofs. Use for ArchiScript modeling, not unrelated Lean programming.
---

# ArchiScript model authoring

ArchiScript makes architectural intent into a checkable implementation contract.
Use it to discover missing cases, incompatible paths, hidden assumptions, and
unclear responsibility before writing the implementation. The deliverable is a
design people and agents can reason from. Lean checks that declared design; it
cannot discover requirements omitted from the carrier or prove conformance of
production code that is not modeled.

## Think in objects, arrows, and composition

- **Objects** are VDPs: complete classifications of an independently given value
  universe into finitely many nonempty semantic subdomains. They express the
  distinctions that matter to the architecture, not a list of desired outputs.
- **Arrows** are operations: partial functions on member sets. Each source
  member has at most one target. `none` means undefined, while `some` of a failure
  member is a defined outcome. Apparent nondeterminism calls for better source
  distinctions or explicit context, not a weaker operation law.
- **Paths** are compositions. For `f : Operation X Y` and `g : Operation Y Z`,
  `g.comp f` requires the same middle object and propagates undefinedness.
  Identity and associativity are supplied by the library. The underlying
  calculus is partial functions between finite member sets,
  $\operatorname{Par}(\mathbf{FinSet})$; carrier values need not be finite.

Start by asking what can enter from outside, what semantic distinctions affect
the available transformations, and which paths must compose or agree. Derive
objects from the boundary and connect them with arrows. Do not begin by copying
an implementation's functions, services, or execution order into a graph.
An external appearance is a boundary assumption, not a fabricated producer
operation; the Lean core currently has no appearance registry.

Keep subdomain relationships distinct from the operation graph. Subdomains
describe regions and their containment; operations connect VDPs at a chosen
resolution. Neither prescribes a runtime schedule. In larger models, organizing
declarations around a result VDP and its inbound operations follows the docs'
codomain-oriented design; it is an authoring convention here, not a Lean
file-layout requirement.

## Start with the carrier

Use this order:

1. Identify the actual independent input universe and its prerequisites.
2. State the carrier without deleting empty, invalid, missing, unsupported, or
   unresolved cases that can occur at that boundary.
3. Define subdomains using the narrowest meaningful parents, predicates,
   intersections, and relative complements. Record the laws and containment
   relationships that justify their meanings.
4. Choose the VDP's resolution: group semantic regions into finite nonempty,
   exhaustive, disjoint members. Give them `MemberIndex` labels and connect
   separately defined predicates to the classifier using `Partition.Realizes`.
5. Supply the required enumeration and inhabitance evidence. Reuse
   `Partition.coverage` and `Partition.disjoint`; do not reprove them per model.
6. Only narrow the carrier when an explicit upstream guarantee or requirement
   justifies the narrower boundary.

Never construct the carrier by enumerating convenient successful leaves merely
to make coverage tautological. A coverage proof shows that the classifier
covers the carrier that was declared; it does not prove that the carrier is
adequate for the intended external problem.

Respect independently specified closed protocol domains. Unions are not
intrinsically wrong; assess what the carrier means instead of warning on a
keyword.

## Subdomains and VDPs have different obligations

A subdomain is one semantic region. Supporting subdomains may overlap, have
several parents through intersection, and leave other values unclassified.
Exhaustiveness and disjointness become mandatory only for the selected members
of one VDP. Do not demand a global taxonomy or a binary refinement tree.

The same carrier can have different VDPs at different resolutions. For example,
two field predicates induce four combinations; a consumer may expose all four
or group three failure regions into one `invalid` member. This coarsening changes
the exposed distinctions, not the carrier values. A flat member list is a valid
declaration when its semantic regions have the required partition properties.
Trees may illustrate a derivation but are not additional semantic objects.

## Deduction and unjustified generalization

Prefer general domains and laws from which narrower membership follows.
Also accept domains defined by explicitly exhaustive constructors, including
closed protocols, recursive types, and finite labels. Mathematical induction
is legitimate too.

Flag **unjustified generalization** when convenient examples or successful
leaves are promoted into a carrier, complement boundary, or completeness claim
without an independently defined parent or explicit constructor closure. A
named alias for that leaf union does not justify it. Do not warn merely because
there is a union, a flat declaration, or Lean `inductive` syntax. Assess the
boundary's meaning and evidence, not its presentation.

## Boundary examples

BAD — success-only project locators (pseudocode):

```text
ProjectLocator := ValidDirectory | ValidPackageJson | ValidIndex
```

This erases unsupported schemes, wrong filenames, and missing siblings before
modeling begins. Defending this boundary tends to require extra “resolution”
partitions and unjustified parameters just to restore failures that were
removed from the carrier.

GOOD — begin from the independently supplied `Uri`; classify scheme and form,
then split `FileUri` using subdomains and relative complements. Successful
directory/package/index cases are deductive leaves alongside every relevant
failure.

BAD — accepted users define all user input (pseudocode):

```text
UserInput := NewUser | ExistingUser
```

GOOD — begin from an independently specified raw user-input boundary (its
source and possible forms must be stated), then classify malformed/invalid,
valid-new, and valid-existing members. Adding an `invalid` constructor is not
by itself evidence that the carrier is adequate. If a named carrier such as
`Email` or `FileUri` already means the valid concept, do not silently broaden
it; use a generic input/carrier name for the boundary that admits failures.

## A priori states and observation

A `Partition` declares a priori possible states. It does not assert that
validation has executed. Unknown membership is observer knowledge, not a new
semantic member and not evidence that one value occupies several members.

Do not invent hydration or classification operations solely to “materialize”
knowledge. A consumer observation may consult a filesystem, database, or other
environment, but expose that context and its assumptions in propositions and
contracts. Never hide environmental dependence or weaken the single-valued
partial-member-function law for observation.

“Quantum superposition” is at most a bounded teaching analogy for unresolved
observer knowledge. It is not implemented ArchiScript semantics.

## Use the current Lean API

Use the public vocabulary exactly:

- `Partition`, with finite labels in `MemberIndex` and semantic subdomains in
  `Partition.member`;
- `Domain`, `Domain.complement`, and `Domain.relativeComplement` for predicates
  and remainders within an explicit parent;
- `Partition.Realizes` for checked correspondence with selected region predicates;
- `Operation` for partial member mappings, with scoped `Operation.id` and
  right-to-left `Operation.comp`;
- `ParameterizedPartition` for specialization by finite parameter members.

Before writing code, inspect the installed package's imports and source API.
Do not revive legacy TypeScript marker recipes or obsolete VDP/PVDP Lean names.

When writing, repairing, or checking Lean source, read
[references/lean-api.md](references/lean-api.md) before editing. It documents
the current branch and routing APIs and points to a compilable smoke example.

## Parameterization and routing

Use a `ParameterizedPartition` only when a parameter member changes which
canonical outbound operations are available. The parameter is itself a
`Partition`; specialization is indexed by its finite `MemberIndex`, never by
arbitrary raw carrier values.

Same route counts can still differ when destinations or canonical operations
differ. Changing ordinary values, results, configuration, or environment is
not enough. Prefer a sound ordinary partition when its outbound topology is
constant.

Nested parameterization resolves inside-out through finite, well-founded
specializations. Do not claim that normalization into tagged data preserves
routing topology.

## Canonical branches and effects

Within an `Operation.Registry`, branch identity is always the pair
`(OperationName, scoped BranchName)`. Resolve branches through the registry.
Aliases reuse the same operation name and branch address; never introduce a
fresh arbitrary key as identity. Routing a whole operation is distinct from
addressing one branch.

Put responsibility tags in `Operation.Declaration.owners`. A branch inherits
them when `branchOwners` returns `none`, or replaces them with `some tags`;
`some []` explicitly leaves it unassigned. Resolve effective tags through
`Registry.resolveBranchOwners`. Tags are metadata, not new operation identities,
effect evidence, access permissions, or a claim about deployment. Keep them
separate from the source-file ownership convention.

A member mapping proves only a partial map between partition members. It proves
no database, filesystem, network, or allocation effect. State effect premises
in typed branch contracts. A branch theorem verifies an implication from those
premises; it does not prove that production code conforms to the contract.

## Spend proofs on design constraints

Supply fields Lean requires to construct valid partitions, branches, routes, and
other checked structures. Add named theorems when they harden a requirement:
preserved invariants, meaningful path equivalence, routing relevance, or an
effect-contract consequence needed downstream. Use existing core laws directly.

Do not turn each definition into an `rfl` theorem, restate structure fields, or
package assumptions into near-tautological conclusions merely to look verified.
A short proof can still protect an important boundary; judge its architectural
value, not its length. Keep simple API regression checks in tests rather than
presenting them as new guarantees about the system.

## Verification and scope

- Run `lake build` and meaningful negative checks.
- Check the chosen VDP members against their declared predicates. Do not impose
  partition obligations on every supporting subdomain or require a tree.
- Treat `unjustified-generalization` as a review finding; the Lean core does not
  yet infer parent-domain provenance or emit this diagnostic automatically.
- Do not use `sorry`, `admit`, or invented axioms to silence obligations.
- Report missing assumptions and unsupported checks honestly.
- Preserve the user's requested scope; do not implement production behavior
  merely because the architecture model mentions it.

For maintaining or evaluating this skill itself, use the realistic cases in
[references/evaluation-cases.md](references/evaluation-cases.md). Do not load
that file for ordinary model authoring.
