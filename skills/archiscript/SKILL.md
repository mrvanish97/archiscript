---
name: archiscript
description: Author, review, or implement from ArchiScript architectural contracts in Lean, with canonical branch bindings and focused human review diagrams. Use for ArchiScript work, not unrelated Lean programming.
---

# ArchiScript model authoring

ArchiScript makes architectural intent into a checkable implementation contract.
The AI agent explores the architecture and proposes carriers, semantic regions,
VDP members, operations, independent factors, and open questions. Lean checks
the explicit obligations of that proposed model. It cannot choose the right
carrier, invent missing requirements, or establish unmodeled production behavior.
Proof success is necessary evidence for the declared model and still needs human
engineering review before implementation. Treat Lean as the executable
implementation of those necessary correctness criteria, not as an architecture
search engine or general model checker: the agent proposes the architecture;
Lean prevents the agent from hand-waving over the obligations ArchiScript has
made formal.

**The wide carrier is the first and most important modeling obligation.** Begin
with the full universe of values that can reach the chosen boundary, including
outcome-relevant preexisting state, environment, and observation context. Then
deduce semantic subdomains and select the VDP members. If a relevant factor is
omitted, every later coverage, `HasMembers`, and operation proof can be green
while the architecture misses a real case. Treat that as an incomplete model,
not as a successful simplification.

A carrier is the collection of things being classified. It can be a broad
primitive type, record/product, union, or other practical type; it does not
need constructor-by-constructor semantic cases. Strict completeness belongs to
the selected VDP members: they must be nonempty, disjoint, and cover every
carrier value. Constructor closure can describe a legitimate finite carrier,
but cannot justify that the collection matches an external input boundary.

Lean is the machine-checkable source of truth. Human engineering review is a
required architecture workflow stage. Review packs and diagrams are projections
of the model for people, and implementation bindings navigate to production
code. A compiling model is not an approved model. Neither a diagram nor a source
location proves code conformance.

## Think in objects, arrows, and composition

- **Objects** are VDPs: complete classifications of an independently given value
  universe into finitely many nonempty semantic subdomains. They express the
  distinctions that matter to the architecture, not a list of desired outputs.
- **Arrows** are operations: partial functions on member sets. Each source
  member has at most one target. `none` means undefined, while `some` of a failure
  member is a defined outcome. Apparent nondeterminism calls for better source
  distinctions or explicit context, not a weaker operation law.
- **Expressions** preserve finite presentation syntax over those arrows. Every
  expression has exactly one source and one target, even when its syntax tree
  branches through tensor or copairing. Linear composition is only one special
  expression shape. For `f : Operation X Y` and `g : Operation Y Z`,
  `g.comp f` requires the same middle object and propagates undefinedness.
  Identity and associativity are supplied by the library. The underlying
  semantic calculus is partial functions between finite member sets,
  $\operatorname{Par}(\mathbf{FinSet})$; carrier values need not be finite.
- **Tensor** is independent aggregation. `P.tensor Q` has carrier
  `P.Carrier × Q.Carrier` and every pair of selected members. `f.tensor g`
  combines partial member maps componentwise and is undefined if either side
  is undefined. Tensor does not mean runtime parallel execution.
- **Coproduct** is lossless structural alternative aggregation.
  `P.coproduct Q` has carrier `Sum P.Carrier Q.Carrier` and preserves the
  summand tag and original member identity. Use it only when the alternatives
  are closed by architecture at design time, never to enumerate cases that are
  discovered by inspecting runtime data.

The mathematical VDP comes first: $P:C_P\twoheadrightarrow\mathcal M_P$,
where $\mathcal M_P$ is a finite family of nonempty semantic subdomains of
$C_P$ that covers it without overlap. Lean's `MemberIndex` and `classify`
represent this partition and make its obligations practical to check. A VDP is
more than an index-valued function.

Use `g.comp f` for sequential member transformation and `f.tensor g` for
independent product transformation. The tensor is a full Cartesian product:
never prune a pair because it seems irrelevant or impossible. `P.tensor P`
still has two independently valued carrier slots. Equal carrier types do not
imply equal values. Common refinement, a diagonal of one shared value, and
correlated resources require separate explicit models. If the factors appear
jointly without a clear reason, ask: **Why are they considered together, and
is their independence intentional?** A mathematically valid tensor is not
rejected because this review question is open.

The associator, unitors, and symmetry change grouping and order through
canonical isomorphisms; they do not change which product member pairs exist.
State review questions about joint use in a way that survives rebracketing or
swapping independent factors, unless explicit roles make order relevant.

Start by asking what can enter from outside, what semantic distinctions affect
the available transformations, and which paths must compose or agree. Derive
objects from the boundary and connect them with arrows. Do not begin by copying
an implementation's functions, services, or execution order into a graph.
An external appearance is a boundary assumption, not a fabricated producer
operation. `Operation X Y` is a partial function from members of `X` to members
of `Y`; it is never a function between carrier values and cannot establish the
origin of `Y`.

Keep subdomain relationships distinct from the operation graph. Subdomains
describe regions and their containment; operations connect VDPs at a chosen
resolution. Neither prescribes a runtime schedule. In larger models, organizing
declarations around a result VDP and its inbound operations follows the docs'
codomain-oriented design; it is an authoring convention here, not a Lean
file-layout requirement.

## Justify the boundary and define meaning

Keep three rules visible during authoring: a carrier is not justified by the
cases one wants to handle; a semantic name is not a semantic definition; and a
classifier is not evidence for its own meaning. State what supplies values at
the boundary, which upstream contracts exclude cases, and what remains
unresolved. A narrow carrier is sound when an independently specified upstream
contract actually guarantees it. "Wide" means complete for the stated boundary,
not the entire system universe.

Before choosing a carrier, ask: **Can two situations with identical request
data require different architectural outcomes?** If so, find the differing
fact and include it in the carrier or establish a checked upstream derivation
or explicitly trusted guarantee that fixes it. Common factors are existing
records, configuration or policy revision, ownership and lease epoch, capacity
reservations, time context, and the state of external services. Do not turn
these into unexplained flags or pretend they arrived in the request payload.
Give each factor its own source and state when it was observed.

For example, a webhook payload may be
`{eventId, status}` while a ledger observation is
`{alreadyRecorded}`. The input carrier for the decision is their product:

```lean
structure Input where
  payload : WebhookPayload
  ledger : LedgerObservation

def firstSuccess : Domain Input := fun x =>
  x.payload.eventId ≠ "" ∧
  x.payload.status = "success" ∧
  x.ledger.alreadyRecorded = false

def duplicateSuccess : Domain Input := fun x =>
  x.payload.eventId ≠ "" ∧
  x.payload.status = "success" ∧
  x.ledger.alreadyRecorded = true
```

The same payload can therefore occupy different VDP members when paired with
different ledger states. The product shape states what the model considers; it
does not establish that the observation is current or stays stable until an
effect occurs. Carry that question as an assumption or open obligation.

For a capacity decision, put arithmetic in semantic predicates over a carrier
containing the observation, rather than inside a member operation:

```lean
structure AllocationContext where
  capacity : Nat
  requestA : Nat
  requestB : Nat

def aFits : Domain AllocationContext := fun x => x.requestA ≤ x.capacity
def bFits : Domain AllocationContext := fun x => x.requestB ≤ x.capacity
def jointlyFits : Domain AllocationContext :=
  fun x => x.requestA + x.requestB ≤ x.capacity

-- The checked model may compose these with intersection and relative complement.
def contended : Domain AllocationContext := fun x =>
  aFits x ∧ bFits x ∧ ¬ jointlyFits x
```

See `ArchiScriptExamples/Asphalt.lean` for the checked
`contendedDerivation` and its containment proof. An operation should consume
the resulting VDP distinction; if it must inspect `jointlyFits` to choose its
architectural target, reconsider the source VDP resolution.

Use this order:

1. Identify the actual independent input universe, prerequisites, and boundary
   evidence. State excluded cases and the contracts responsible for them.
2. State the carrier without deleting empty, invalid, missing, unsupported, or
   unresolved cases that can occur at that boundary. Include relevant
   preexisting state or environment as separate product factors. For example,
   a webhook decision may classify `WebhookPayload × LedgerObservation`;
   duplicate delivery is a relation to the ledger observation, not a property
   of the payload alone.
3. Define each meaningful subdomain's membership predicate independently of
   the classifier. Use the narrowest meaningful base, intersections, and
   relative complements. Record containment laws and the parent of each
   complement. If membership depends on mutable environmental state, name the
   fixed snapshot or context assumed during classification.
4. Choose the VDP's resolution: group semantic regions into finite nonempty,
   exhaustive, disjoint members. Give them `MemberIndex` labels and connect
   separately defined predicates to the classifier using `Partition.HasMembers`.
5. Supply the required enumeration and inhabitance evidence. Reuse
   `Partition.coverage` and `Partition.disjoint`; do not reprove them per model.
6. Only narrow the carrier when an explicit upstream guarantee or requirement
   justifies the narrower boundary.

Never construct the carrier by enumerating convenient successful leaves merely
to make coverage tautological. Never drop a state factor just because it makes
the member formulas harder. A coverage proof shows that the classifier covers
the carrier that was declared; it does not prove that the carrier is adequate
for the intended external problem. If the complete carrier cannot yet be
specified, mark the boundary unresolved and do not present the VDP as a
complete handoff.

For implementation handoff, package each selected partition in an
`ArchitecturalPartition`. Its `carrierOrigin` records an external root, an
explicit external narrowing guarantee, or an architecture-defined semantic
domain. It never records a value-producing operation.
Use `externalRoot` for the independently given appearance universe. A trusted
post-validator boundary is `externalNarrowing` and must retain its upstream
origin; do not relabel it as a root to erase rejected inputs. The external
guarantee remains a premise about an identified source, scope, and revision.
Use `architecturalDomain` for an internally defined semantic universe. It does
not claim that an operation produced values of that type. `carrierClosure`
separately proves finite constructor exhaustiveness *inside* an already
justified carrier. It cannot establish that a production boundary emits only
that type. An operation's member mapping alone cannot establish narrowing;
preserve the wider carrier and refine meaning with typed subdomains instead.

Give each `selectedMembers` entry an independently stated `meaning` predicate
and a `DomainDerivation` indexed by that exact predicate. Use `.predicate p`
for a Lean-defined atomic predicate `p`; use `.intersection`, `.union`, and
`.relativeComplement` to record deductions, including containment proof for
the latter. Do not place a prose summary in the definition field and call it a
formula. Human descriptions are review annotations only. Use
`.opaque reason (by decide) p` when the extension `p` is declared but no
defining formula is available; Lean requires the reason to be nonempty.
Do not pass an opaque Lean constant to `.predicate` merely to obtain a stronger
review label. The type index checks denotation equality; it cannot decide
whether an atomic predicate was independently motivated or inspectable.
Supply a reason and surface an opaque warning for any derived domain depending
on that leaf. Opaque is
valid, but weakens what the model can establish and prompts the author to
consider a more precise formula or an external obligation. `HasMembers` still
checks classifier correspondence. An opaque meaning supplies no formula-derived
consequences without additional assumptions or proofs.
Do not use `members i := P.member i`, `classify`,
or a mechanical restatement of the classifier as the member definitions this
proof is meant to validate. Classifier fibers may be useful as derived views,
but they are not independent semantic evidence. Lean checks the correspondence;
reviewers must assess the independence and adequacy of the predicates.
For a justified closed enum carrier whose constructors are the semantic cases,
constructor equality may define its members; a simple `id` classifier and
`rfl` proof are legitimate. State why that enum is the actual boundary.

Respect independently specified closed protocol domains. Unions are not
intrinsically wrong; assess what the carrier means instead of warning on a
keyword. A practical carrier may be a record, product, sum, union, JSON value,
or other type justified by the actual boundary. Deductively define its semantic
subdomains and selected VDP members; do not confuse the carrier's representation
with the proof that the selected members cover it.

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

In 0.4.0, make such resolution changes explicit with semantic containment.
For VDPs `P` and `Q` on the same carrier, a map
`q : P.MemberIndex → Q.MemberIndex` witnesses `P.RefinesVia Q q` only when
every fine member is wholly contained in its mapped coarse member. Totality and
surjectivity of labels alone are insufficient: a coarse partition may cut
through a fine semantic region. A proved refinement induces the ordinary total
`Partition.coarseningOperation q`.

For a consumer `f : Operation P Y`, use `Operation.ConstantOnFibers q f` and
the factorization API to ask whether `f` can be expressed through the coarse
view. A successful factorization gives the unique coarse consumer; a failed
finite analysis yields a concrete pair of fine members that the consumer still
distinguishes. Treat this as the checked basis for semantic zoom in diagrams,
not as a new arrow kind.

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

If omitted context determines an operation's result, refine the carrier or
make that context explicit. If behavior is genuinely temporal or
nondeterministic, such as races or timeouts, record the limitation or use a
complementary formalism. Do not invent fictional source information just to
force a deterministic member map.

“Quantum superposition” is at most a bounded teaching analogy for unresolved
observer knowledge. It is not implemented ArchiScript semantics.

## Use coproduct only for design-time closed alternatives

`Partition.coproduct P Q` is the categorical coproduct of two VDPs. It is a
lossless structural OR: the carrier is `Sum P.Carrier Q.Carrier`, the member
family is the tagged sum of the factor members, and the source tag remains
available. `Operation.coproductInl`, `Operation.coproductInr`, and
`Operation.copair` implement the standard coproduct universal property.

The public claim is **binary coproduct**. Because every `Partition` requires a
nonempty carrier, ArchiScript has no empty/initial VDP in this calculus. Do not
silently strengthen the API into arbitrary finite coproducts that include a
nullary coproduct.

The authoring discipline is intentionally stricter than the bare mathematical
construction. **Use coproduct only when the set of summands is already fixed by
the architecture before runtime values are materialized.**

GOOD — the software has exactly two independently defined entry channels:

```text
BrowserInput ⊕ CliInput
```

The program topology itself supplies the alternatives: a browser entry point and
a CLI entry point. Each summand must still have its own complete carrier and VDP.

BAD — inspect an external runtime value, recognize two currently known shapes,
then declare:

```text
ExternalInput := PaymentMessage ⊕ RefundMessage
```

This is an inductive completeness backdoor unless an independent design-time
boundary contract already states that the external universe is exactly that
tagged sum. Runtime parsing, validation, protocol decoding, filesystem
inspection, database lookup, or other materialization must not manufacture
coproduct summands after the fact. Start from the full runtime carrier and
deductively define a complete VDP, including invalid, unsupported, malformed,
unknown, and other relevant cases.

Always remember:

```text
P ⊕ Q is exhaustive over Carrier(P) + Carrier(Q).
It does not prove that this sum exhausts an external boundary.
```

A collapsed coproduct node in a diagram hides presentation detail only. It does
not coarsen semantic members. Use coarsening, not coproduct, when distinctions
are intentionally forgotten.

## Compose independent factors with tensor

Use `Partition.tensor P Q` only with its established meaning: independent
aggregation. The result always has carrier `P.Carrier × Q.Carrier` and the full
member product. Never prune a pair because it looks semantically inconvenient,
never collapse `P.tensor P` to one carrier value, and never reinterpret tensor
as same-carrier intersection or common refinement.

This is a symmetric monoidal tensor, **not a categorical product** in the
partial-map calculus. Do not invent canonical projections or a universal
pairing operation: partial maps into two factors may have different domains of
definition, and the tensor unit is not terminal because there are many partial
maps into it.

The mathematical tensor is permissive. `Account(A) ⊗ Payment(B)` is a valid
VDP construction even when the architectural reason for considering those
factors together is unclear. Do not make such a pair fail to compile merely
because it looks unrelated. Preserve the full product and raise a human-review
question about joint relevance when the model supplies no clear reason.

Use `SemanticPartition.tensor` when both factors already carry independently
stated member meanings; it derives product meanings and correspondence rather
than asking the author to restate them. Use `Operation.tensor` to combine
independent partial member maps. This is algebraic independence of slots and
mappings, not a runtime scheduling claim.

Do not use tensor to model fan-out from one semantic decision. If one mutation
has both a persistence contract and an outbox contract, model two arrows from
the same source VDP. `persist.tensor publish` would require two independent
mutation slots and therefore says something different.

Fan-out does not encode an execution order. Several arrows from one source VDP
are therefore potentially parallel at runtime, but ArchiScript does not assert
that they actually run concurrently. Sequential behavior must be represented by composition through an intermediate
VDP, for example `A -> B -> C`, so the output classification of the first
operation is the source classification of the second. A linear path is an
informal view of that expression, not a separate foundational syntax.

Treat rebracketing and factor order as representation choices governed by the
canonical associator and symmetry. A finding that concerns only the set of
tensor factors should not appear or disappear merely because the author wrote
`(P ⊗ Q) ⊗ R` instead of `P ⊗ (Q ⊗ R)`, or swapped factors through the
declared symmetry.

## Preserve expression syntax; normalize locally

Version 0.5.0 separates category semantics from architecture presentation
syntax. The ArchiScript category supplies VDP objects, `Operation` morphisms,
composition, tensor, coproduct, and their laws. `Expression X Y` records one
finite well-typed presentation of a morphism and
`Expression.denote : Expression X Y → Operation X Y` gives its semantics.

Keep nominal architecture identity out of the mathematical `Partition` value.
A Lean declaration symbol can identify an architectural VDP even when another
declaration denotes an extensionally equal partition. Do not add a `name :
String` field to `Partition` merely to serve presentation or normalization,
and do not infer architectural identity from equal carriers or classifiers.
Which named operation declarations are primitive architectural generators versus
derived aliases remains presentation-level policy and is intentionally
non-blocking in 0.5.0.

When structural normalization needs a VDP isomorphism, use
`Partition.PartitionIso`: it carries a carrier equivalence, a member-index
equivalence, and classifier commutation. An invertible member-level `Operation`
alone is too weak because it cannot distinguish unrelated carriers with
isomorphic finite member sets.

Do not make normalization search for arbitrary carrier bijections merely because
a `PartitionIso` could exist mathematically. Normalization should use known,
proved structural isomorphisms such as associativity, unitors, symmetry, and
distributivity. Mathematical isomorphism and the chosen orientation of a
normalization rule are separate concerns.

Every expression has **exactly one source and exactly one target**:

```text
e : X → Y
```

Its syntax can still be tree-shaped. `f.tensor g` combines two independent
subexpressions into one morphism, and `copair f g` combines two alternative
source branches into one morphism. Do not call such an expression a
multi-source or multi-target path. Use "expression"; a sequence or graph path is
only the linear composition special case.

An `Expression.Family` is finite and nonempty. All selected expressions in one
family share one source; their targets may differ. This represents one
consequence question from one materialized source context without inventing
`Trigger`, `Source`, or `Terminal` VDP kinds. The same nominal VDP may be
the source of one family, a target of another, and an intermediate VDP in a
third.

Build that single source structurally. Simultaneously required independent facts
belong in tensor coordinates; design-time closed alternative entry channels
belong in coproduct summands. Do not introduce a multi-source family. Likewise,
do not split one consequence question into separate families merely because its
source is a coproduct: branch-specific consequences can remain partial
expressions from the common coproduct source. Use separate families when the
analysis question or materialization boundary is genuinely different, not as a
replacement for tensor/coproduct structure.

The current Lean `Expression.Family` uses a `List` only as finite storage.
Do not infer execution order, priority, or stable architectural identity from
list position. Set-like versus explicitly indexed family identity remains an
open presentation question; 0.5.0 assigns no semantics to list order.

Architecture may contain cycles. Each selected expression remains finite.
Never define a family as an enumeration of every finite traversal of a cycle,
and never infer a runtime loop, retry schedule, or temporal recurrence merely
from categorical cyclicity.

### Distinguish normalization from architecture projection

Composition creates a composite morphism; it does **not** delete its
intermediate object from the category. If

```text
A ──f──▶ B ──g──▶ C
```

then `g.comp f : Operation A C` exists while the nominal VDP `B` still
exists. Rewriting expression syntax with composition is therefore not evidence
that `B` disappeared from the architecture.

If a human or generated view intentionally keeps only selected nominal VDPs and
hides `B`, classify that as an **architecture projection**. Do not call it
ordinary normalization and do not introduce an `Anchor` primitive merely to
control it. The 0.5.0 normalizer preserves the nominal VDP boundary set in its
scope; a future projection layer may deliberately choose a smaller view.

Local normalization does not require a complete whole-architecture isomorphism
theory. Use the smallest explicit certificate that proves the rewrite:

- for unchanged endpoints, require equality of the denoted Operations;
- when structural endpoint representatives change, use explicit
  `PartitionIso` witnesses and a commuting transport square.

Local really means local: once a subexpression rewrite is certified, lift it
through surrounding composition, tensor, or copairing with
`Expression.Rewrite.comp`, `.tensor`, or `.copair`. Do not reprove an
end-to-end equality when ordinary congruence already transports the smaller
certificate.

`Expression.Rewrite` records the first form.
`Expression.Transport` records the second. Whole-architecture equivalence is
deferred until transformations actually need to merge/split families, remove
nominal VDPs, replace architectural generators, or create new shared nominal
boundaries.

### Use distributivity only through proved structural isomorphisms

The canonical 0.5.0 distributivity shape is

```text
(A ⊗ R) ⊕ (B ⊗ R)  ≅  (A ⊕ B) ⊗ R
```

with the left-handed analogue. The two bundled `Partition` values are not
definitionally equal: their carrier types have different shapes. Use
`Partition.tensorCoproductRightDistributivity` or
`Partition.tensorCoproductLeftDistributivity`, together with the induced
Operations and naturality theorems, rather than pretending the expressions are
equal by reduction.

Factoring a repeated `R` exposes one common **structural coordinate**. It does
not prove one database read, one cache lookup, one transaction, one runtime
object, or any scheduling property. Conversely, `A ⊗ R ⊗ R` still contains
two independent `R` slots and must not be collapsed to one.

### Derive dependency before provenance

A tensor coordinate required in the materialized family source can be an
independent dependency. Tensor syntax does not create a missing coordinate:
there is no canonical `X → X ⊗ R`. An internal expression
`f.tensor g : A ⊗ B → C ⊗ D` is valid because both source coordinates are
already present. If an independent `R` seems to appear only midway through an
analysis, either an ordinary preceding Operation explicitly produced that
paired value or the family source is missing an exogenous dependency. Make the
dependency explicit in the source instead of treating tensor as acquisition.

Coproduct behaves differently: from `A → A ⊕ B` through the left injection,
no value of `B` is required merely because `B` occurs in the target type.
Never infer dependency from codomain structure alone.

A source such as

```text
(A ⊗ S) ⊕ B
```

means structurally "(A AND S) OR B", not the flat dependency set
`{A, S, B}`. The exact public result shape for richer dependency analysis is
intentionally non-blocking in 0.5.0; do not erase the tensor/coproduct structure
just to force a simple set API.

Identify that a family needs the current `S` before asking which family might
have produced it. Producer provenance is a second, architecture-wide query.
Because tensor is not a categorical product, an expression ending in
`X ⊗ S` is not automatically a producer of `S`: there is no canonical
projection onto the `S` coordinate.

Coproduct equations support branch-relative expression simplification. For
example,

```text
[f,g] ∘ ι₁ = f
```

justifies normalizing that selected expression. It does not globally delete the
`B` summand, the operation `g`, or any nominal coproduct VDP used elsewhere.
If the family source itself is `A ⊕ B`, both tagged alternatives remain valid
source alternatives.

Graphs come after these semantics. Dependency graphs, provenance graphs, and
cycle/SCC views are derived projections of already-defined relations; they are
not the architecture foundation.

The remaining questions about generator-versus-alias metadata, indexed versus
set-like families, shared-subexpression storage, member-level reachability,
global rewrite ordering, and whole-architecture equivalence are deliberately
non-blocking for 0.5.0. Do not resolve them by adding ontology without a concrete
need.

## Review independent arrows carefully

Several branches of one `Operation` are alternative cases of one partial map.
An `if/else` distinction belongs in source VDP members and one arrow. It is
not evidence of concurrent work.

Distinct operation declarations with independently available sources can raise
a concurrency question, especially when they later concern one mutable
resource. Treat two independent source VDPs converging on one target as a
candidate review boundary, not as proof of a race. Treat a cycle as an ordinary
sequential feedback/retry path unless independent source provenance and shared
mutable effects make interference possible.

Use the following as **concurrency-review signals**, not automatic diagnostics:

- two or more independently available source VDPs can reach operations that
  concern the same logical mutable resource;
- two paths can observe the same state member and request different or
  potentially noncommuting next states or write commands;
- a state/retry cycle can be entered from an independent source while work on
  the same resource may still be in progress;
- repeated delivery, retries, or duplicate triggers can re-enter an effectful
  path and idempotency is not established;
- ordering, serialization, compare-and-swap/version checks, atomicity,
  commutativity, or transaction boundaries are absent or explicitly unknown.

The strongest useful review pattern is:

```text
independent source provenance
+ shared mutable resource
+ potentially noncommuting effects
+ no serialization evidence
=> concurrency hazard to review
```

A common target, graph fan-in, or cycle alone does not prove a race, deadlock,
or commutativity result. Record ordering, atomicity, idempotency, commutativity,
and repeated-effect safety as `UNKNOWN` or review findings until an explicit
resource/effect model or external analyzer supports a stronger claim. Tensor
expresses independent semantic slots and member maps, not scheduling.

## Use the current Lean API

Use the public vocabulary exactly:

- `Partition`, with finite labels in `MemberIndex` and semantic subdomains in
  `Partition.member`;
- `Domain`, `Domain.complement`, and `Domain.relativeComplement` for predicates
  and remainders within an explicit parent;
- `Partition.HasMembers` for checked correspondence with selected region predicates;
- `SemanticPartition` for member predicates, correspondence proof, and named
  coverage, disjointness, and nonemptiness theorems over the declared carrier;
- `CarrierOrigin`, `CarrierClosure`, `DomainDerivation`, and
  `ArchitecturalPartition` for reviewable origins, internal closure, and
  selected-member definitions;
- `ArchitecturalOperation` and `Architecture` to list handoff operations with
  evidence for both endpoints;
- `Operation` for partial member mappings, with scoped `Operation.id` and
  right-to-left `Operation.comp`;
- `Partition.tensor`, `Partition.unit`, `SemanticPartition.tensor`, and
  `Operation.tensor` for independent product composition, plus canonical
  associator, unitors, and symmetry in `ArchiScript.Monoidal`;
- `Partition.coproduct`, `SemanticPartition.coproduct`,
  `Operation.coproductInl`, `Operation.coproductInr`, `Operation.copair`,
  and `Operation.coproductMap` for design-time closed tagged alternatives;
- `Partition.RefinesVia`, `Partition.Refines`,
  `Partition.coarseningOperation`, and the `Operation` factorization helpers
  for checked semantic resolution changes;
- `Partition.PartitionIso.refl`, `.symm`, `.trans`, `.tensor`, and
  `.coproduct` for composing already-proved classified-carrier
  isomorphisms without rebuilding carrier/member proofs by hand;
- `Partition.tensorCoproductRightDistributivity`,
  `Partition.tensorCoproductLeftDistributivity`,
  `Operation.distributeRight`, `Operation.distributeLeft`, and their
  naturality laws for canonical tensor/coproduct structural transport;
- `Expression`, `Expression.denote`, `Expression.Family`,
  `Expression.Rewrite`, and `Expression.Transport` for finite presentation
  syntax and certified local normalization;
- `ParameterizedPartition` for specialization by finite parameter members.

Version 0.5.0 retains the concrete symmetric-monoidal API and adds typed
expressions, expression families, distributivity witnesses, and local
normalization certificates. Do not assume a separate Mathlib
`MonoidalCategory` instance or invent abstractions that are not present in the
installed API; use the concrete `Partition.tensor`, `Operation.tensor`,
structural isomorphisms, expression constructors, and theorems the package
actually exports.

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

## Canonical branches, responsibility, and implementation

Within an `Operation.Registry`, branch identity is always the pair
`(OperationName, scoped BranchName)`. Resolve branches through the registry.
Aliases reuse the same operation name and branch address; never introduce a
fresh arbitrary key as identity. Routing a whole operation is distinct from
addressing one branch.

Put organizational responsibility tags in
`Operation.Declaration.responsibilityOwners`. A branch inherits them when
`branchResponsibilityOwners` returns `none`, or replaces them with `some tags`;
`some []` explicitly leaves it unassigned. Resolve effective tags through
`Registry.resolveBranchResponsibility`. These tags are independent of both the
architectural declaration file and the production source location.

Record one implementation disposition per production-relevant branch. An
operation-level `implementation` is a default; `branchImplementation` overrides
it. Resolve through `Registry.resolveBranchImplementation`, including for aliases.
Use `planned` for an intended site, `resolved` only after inspecting real source,
`external` or `intentionallyAbstract` with a reason, and `unimplemented` when work
remains. A missing disposition is a finding, not a synonym for unimplemented.
For a binding, specify one primary `SourceRef`; supporting references and
`EvidenceRef`s are optional. The source identity is repository, path, and
optional symbol; revision and line range are navigation metadata. Source
bindings declare where code is believed to implement a branch. They do not
prove that code exists, that a symbol still resolves, or that its effects conform.
Evidence references are leads for review, not automatically proofs.

Keep `branchNames` and `operationNames` exhaustive and duplicate-free. Use
`Registry.branchAddresses`, `branchesWithoutResponsibility`, and
`branchesWithoutImplementation` for whole-model review; use `branchesAt` for
reverse navigation from a declared source identity. An enumerable registry
checks only its declared scope. Use `Declaration.definedMappingsWithoutBranch`
to expose defined member mappings omitted by optional named branches before
claiming a whole-operation handoff. The example review generators require a
coverage row for every registry operation and reject unnamed defined mappings.
Do not claim that it discovers all production
code or validates source paths. A source member mapped to `none` is not a typed
`Branch` in the current API; review that undefined mapping through the operation
itself and show it explicitly in relevant diagrams.

A member mapping proves only a partial map between partition members. It proves
no database, filesystem, network, or allocation effect. State effect premises
in typed branch contracts. A branch theorem verifies an implication from those
premises; it does not prove that production code conforms to the contract.

## Implement from a checked model

For new architecture, proceed from justified carrier and semantic regions to a
checked partition, canonical operations and branches, responsibility and
implementation dispositions, explicit value/effect obligations, Lean proofs,
and a focused human review projection. When code exists, inspect the bound sites
and attach evidence separately from architectural proof. Mark conditional and
unknown obligations rather than promoting them to proved claims.

For a nontrivial model, check that every selected member has an independently
stated predicate; relevant containment and complement parents are explicit;
environment-dependent predicates name their context; selected members are
inhabited, exhaustive, and disjoint; and `Partition.HasMembers` connects the
predicates to the classifier. Apply these checks to selected VDP members,
without demanding that all supporting subdomains form a partition.

Before accepting those proofs, audit carrier completeness separately. Name the
source of each input factor and each relevant preexisting-state factor. Give a
counterexample candidate for every excluded factor: hold the modeled carrier
fixed and vary the excluded fact. If the required member or downstream action
could change, add that fact to the carrier or record a justified upstream
guarantee that makes the variation impossible. Review unions, products, and
records by their admitted values, not by their syntax. Keep unknown acquisition,
staleness, and concurrency guarantees visible in the review pack.

For the architecture-to-implementation workflow, check the review record before
implementation. `draft`, `ready-for-review`, `changes-requested`, and
`superseded` do not authorize implementation. `approved` applies only to the
recorded model revision and reviewer, with no open change requests. If approval
is absent or stale, prepare the review pack and report the gate as closed;
obtain engineering approval before dispatching implementation work. Follow any
explicit user direction about the workflow while making the review state clear.

When asked to write or repair production code, resolve each affected canonical
`(OperationName, BranchName)` first. Read its source and target members, relevant
path and effect/value contracts, effective responsibility, and implementation
disposition. Inspect the bound code and change that site rather than creating a
parallel handler. If the binding is planned, missing, stale, or refers to external
code, report that fact and update it only from observed source. Preserve the
architectural contract; do not weaken it to make implementation easier. Add or
update explicit evidence, and state which code conformance questions remain
unknown. Never report a branch implemented without its canonical address,
location, obligation, and remaining unknowns.

For code changes, report affected branches, resolved locations, changes,
evidence, preserved obligations, and conditional or unknown conformance.
Separate architecture status, binding status, and code conformance status.

## Project for human review

For a nontrivial architecture review, produce a two-pass review pack that an
engineer unfamiliar with Lean can criticize without opening a `.lean` file.
The fast pass exposes scope, all carrier factors and their sources, boundary,
topology, major assumptions, owners, changes since the prior revision, and open
questions. The deep pass exposes
semantic distinctions and coarsenings, all relevant branch and `none` mappings,
effects, bindings, proof references, conditional claims, unknowns, and findings.
Make questionable choices visible rather than smoothing them away. Attach every
finding to a canonical carrier, partition, member, operation, branch, effect
contract, or implementation binding ID. Store review state and findings outside
the generated PDF; treat the PDF as a versioned reading snapshot.

Identify the review question and produce a focused diagram from the Lean model.
Do not independently author semantic facts in Mermaid. Preserve canonical
operation, branch, and member names; mark display-only groupings. Distinguish
member mappings from runtime calls, render relevant `none` outcomes explicitly,
and put assumptions, proved claims, and unknowns beneath the graph. State the
diagram level, focus, and omissions.

Use one visual grammar consistently:

- define elementary VDPs before showing products built from them;
- draw object construction with unoriented factor/summand lines into the
  constructor node and one directed construction edge from the constructor to
  the constructed VDP:

  ```text
  P ---┐
       ⊗ --▶ P ⊗ Q
  Q ---┘

  P ---┐
       ⊕ --▶ P ⊕ Q
  Q ---┘
  ```

  The arrowhead after `⊗` or `⊕` shows the reading direction of the
  construction, not an `Operation`. Do not add arrowheads from the factors
  into `⊗`: tensor has no canonical injections. Do not label structural
  coproduct construction lines as coproduct injections; canonical injections
  are actual Operations and should be drawn separately only when they are the
  review subject;
- a VDP is a labeled container and its actual members are nodes inside it;
- reserve VDP containers for actual VDPs only; do not use the same container
  grammar for "factor groups", stages, or collections of operations;
- use the repository's established/default diagram theme. Do not assign
  semantic meaning to hard-coded colors; containment, node shape, labels, and
  arrow direction carry the meaning;
- `∅` is outside every VDP and denotes one operation being undefined for a
  source member;
- a tensor VDP still contains the full Cartesian member product. A focused view
  may replace omitted tuples with a box such as
  `[display group: other 8 members]`, but the caption must say that it is not
  a model member and enumerate or otherwise account for the hidden members;
- when only some members are shown, state both the total VDP cardinality and
  how many are expanded/collapsed;
- never draw a VDP-container-to-`∅` edge. Partiality belongs to member
  mappings, not to the container as a whole;
- show tensor operations factored by default. First show the elementary maps
  `f : P → P′` and `g : Q → Q′`, then state/show the induced compact arrow
  `f ⊗ g : P ⊗ Q → P′ ⊗ Q′`. Do not expand the mechanically induced
  Cartesian family unless those product branches are the review question;
- if a dedicated operation-algebra picture is useful, use operation-shaped
  nodes and label it as an operation-algebra view so those nodes cannot be
  mistaken for VDPs or members;
- ordinary fan-out from one VDP is several arrows with the same source, not
  `Operation.tensor`. Such arrows have no modeled order and may correspond to
  potentially parallel runtime work; do not claim actual parallel execution
  without runtime evidence;
- sequential operations must form a path through an intermediate VDP. Do not
  describe two sibling outgoing arrows as sequential merely because an
  implementation happens to call them in some order;
- show coproduct as structural aggregation of already-established design-time
  alternative VDPs. Keep the summands visible or explicitly named; a collapsed
  coproduct node must not look like evidence that runtime cases were exhaustively
  discovered;
- show coarsening as a resolution-change arrow between VDPs on the same carrier,
  distinct from tensor/coproduct construction;
- collapse a fine VDP to a coarse VDP for a consumer only when factorization is
  proved. When factorization fails, show the conflicting fine members or state
  the conflict directly instead of drawing an invalid coarse consumer.

Keep a diagram to about eight major nodes when possible and split broad reviews
into complementary views rather than exploding mechanically induced detail.
When the question does not imply a level, start with Level 1 and one focused
Level 2 branch map.

For a repository-level or release-level **stress example**, do the opposite of
feature-island documentation: exercise the current calculus compositionally in
one realistic model. Prefer an existing model that already has meaningful
independent factors, alternative entry channels, partial operations, and
multiple consumers. Add new algebraic structure only where its mathematical
meaning is genuinely present.

The canonical repository stress test is
`ArchiScriptExamples/ReservationController.lean`. Its review projection should
make the interactions between sequential composition, tensor, design-time
coproduct, refinement/coarsening, successful factorization, failed
factorization, partiality, expression syntax/denotation, one-source
multi-target expression families, distributive source factoring, local
normalization certificates, architecture projection boundaries, and
independent-source review questions visible in one coherent model. New calculus
features should be integrated into this stress test when they naturally apply,
not demonstrated only in isolated toy files.

Read [references/review-diagrams.md](references/review-diagrams.md) when drawing
or reviewing diagrams. It defines Levels 0–4 and Mermaid conventions.
Read [references/review-packs.md](references/review-packs.md) when creating or
revising a review pack or processing engineering findings.

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
- When changing the public API or this skill, also run
  `lake env lean skills/archiscript/examples/CurrentApi.lean`; the smoke file
  should exercise semantic partitions, tensor/coherence, architectural handoff,
  canonical declarations, routed parameterization, and the review gate.
- Check the chosen VDP members against their declared predicates. Do not impose
  partition obligations on every supporting subdomain or require a tree.
- Require carrier provenance in review/handoff objects. Treat
  `unjustified-generalization` as a review finding; Lean records declared
  provenance but cannot infer that an external claim is true or discover every
  omitted upstream value. Do not treat a trusted premise as a proof.
- Check the wide-carrier audit with a same-request/different-state probe. If
  different prior states can demand different outcomes but the modeled carrier
  cannot distinguish them, the reviewable model is incomplete even when Lean
  compiles. Escalate the missing factor or record a scoped external guarantee.
- Show every `.opaque` selected member or supporting subdomain, including opaque
  leaves inside a composed derivation, with its reason in review. It remains
  valid but cannot support deduction from an unavailable formula.
- Do not use `sorry`, `admit`, or invented axioms to silence obligations.
- Report missing assumptions and unsupported checks honestly.
- For nontrivial authoring, report boundary/carrier justification, semantic
  distinctions, checked obligations, responsibility and implementation bindings,
  a human review pack, conditional claims, and unknowns as relevant.
- Preserve the user's requested scope; do not implement production behavior
  merely because the architecture model mentions it.

For maintaining or evaluating this skill itself, use the realistic cases in
[references/evaluation-cases.md](references/evaluation-cases.md). Do not load
that file for ordinary model authoring.