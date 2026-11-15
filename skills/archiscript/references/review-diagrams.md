# Review diagrams for 0.7

A diagram is a projection of checked declarations. State the question, scope,
hidden detail and proof status in its caption.

For an architecture-wide view, apply the
[manual inventory audit](../SKILL.md#manual-audit-of-the-complete-declared-inventory).
Include disconnected declared nodes and rootless SCCs, not only Cause-rooted
paths. Show `Cause → X` and isolated `Y ↔ E` as separate components; do not omit
Y/E because `UngroundedCycle.certified` passes. Caption the architect's explicit
disposition (remove, intentional unreachable/excluded, or missing dependency)
and unverified coverage assumption. A marker or owner label proves no source.
An independent component need not change rooted tuples, but can obstruct an
observable Cone's `BoundariesComplete`. Layout is not inventory-grounding proof.

| View | Nodes | Edges / annotations |
| --- | --- | --- |
| Semantic decomposition | Declared Subdomains | Proved containment and each particular exhaustive split |
| VDP topology | Whole nominal VDPs | Named whole-VDP Operations |
| Member mapping | Members inside VDPs | Defined source-to-target mappings; `none` shown outside the VDP |
| Linear Expression | One typed Operation sequence | Explicit start and Effect boundary, including cyclic entry |
| Cone / dependencies | Derived occurrence identities with a canonical origin per Cause | Non-exclusive routes and actual local/external suppliers; recursive `RootCoherent` scope |
| Contextual tensor | Full factor/member product | Independently derived images, full-tuple Reach and Adm |

A decomposition view may show several trees with the same root. Only siblings
within one proved split must be disjoint. Every named region is nonempty;
intermediate set expressions may be empty.

For a tensor, display full cardinality even when the reachable relation is
smaller. For example, a Boolean self tensor has four members; a common-source
join may reach only two diagonal tuples. Label `Reach = Adm` with the actual
proof and owning context. A diagram must not prune mathematical members or
create an Operation from common-source fan-out to a product.

Show both E failure directions: a reachable tuple outside Adm and an admitted
tuple outside Reach. **Every admitted tuple must be reachable**; a tuple that
the contract mistakenly admits remains part of the comparison. P is the
necessary projection check, not a substitute for the full relation.

Label a source by its Cause and designated origin, such as `c @ origin c`.
Two paths from that same event may diverge and explicitly rejoin. Two distinct
Causes may have equal VDPs and equal root labels while remaining different
sources. A noncanonical root of any Cause, including inside a nested external
producer, makes the full input unsupported. Draw such a raw term as rejected
scope even if it evaluates to the same value as a supported term. A local
factor or an owner-only root annotation cannot certify the whole tree. The
[root regression](../../../ArchiScriptTests/RootCoherence.lean) supplies these
contrasting cases.

Display the two independent input obligations and the Effect status explicitly:

| Certificate field / alternative | Required diagram annotation |
| --- | --- |
| `inputSources g`: `grounded` | A coherent typed supplier at every position, identified before forming complete tuples |
| `inputSources g`: `unreachable` | All independent `supplierImage`s empty, not merely one missing factor |
| `inputs g t`: `verified` | This context's P/E proofs and a reachable tuple |
| `inputs g t`: `unreachable` | This context's actual incoming images all empty, no reachable tuple, no admitted tuple |
| `cones c`: `observable` | `ConeValid`, including an actual derived Effect position, a reachable full tuple, P and E |
| `cones c`: `unobservable` | `NoObservableEffect`: every Effect incoming image empty and the whole Effect contract empty |

Grounding witnesses do not choose the universally checked contexts. Show an
unsourced factor at its declared generator even if no complete input term
exists; X incoming / Y absent is a failed source obligation, not an omitted
diagram node. `input_partner` ensures an independently incoming member of a
certified generator has a full supported Adm-and-Reach partner. Structural
supplier lines are evidence for the input declaration, not new runtime actions.

For an observable Effect, show actual `(Node, History)` coordinates and the
proof of `Nonempty (model.effect c).Position`; a nonempty nominal boundary list
does not establish them. An empty tensor's unit value is not an observed Effect.
An unobservable status can instead have real positions whose incoming images
are all empty. Caption it as proved unobservable, with no claimed successful
unit tuple. `BoundariesComplete` supplies that proof or a structural path for
each owned node. `hasCone` guarantees a checked status, not an observable one.

Keep one declared C and one shared h;k in the topology view. A derived-path
view may annotate the f/p and g/q histories, but those labels are explanatory,
not mandatory named uses or cloned nodes. Show two terminal positions of C (or
E after the shared suffix), together with the proved joint relation even when
their images agree. An analytical Effect product does not add a join Operation;
show an actual C ⊗ C → R arrow only when registered and fully supplied.

Use distinct explanatory labels for two occurrences with the same VDP. A prior `B`, an
external producer's `B`, and a cyclic generation of `B` are separate provenance
claims. Derived dependency edges through a tensor factor are not categorical
composition and do not establish a return cycle.

A proof-cache annotation lists each Cause's designated origin, not all possible
`RootInstance` values. Its `Valid` evidence must also cover seeds, closure and
realized histories. No graph caption should infer finite histories from finite
origins or VDP member sets.

Mark cyclic observation at the real boundary chosen by the architect. Repeated
visits enlarge its member image, not the number of effect coordinates. A finite
linear Expression may revisit an object; a branching supplier trace is not a
single Expression. `Presentation.Family` remains a selected view, not complete
Cone discovery.

Coproduct is tagged OR. Its injections are actual Operations; structural lines
into a tensor constructor are not injections. A coproduct cannot conceal a
simultaneous structural join.

Composition and a local `Presentation.Rewrite` do not delete intermediate
nominal VDPs. A view hiding them is an architecture projection. Distributivity
uses a proved canonical isomorphism; no read count, transaction, caching or
scheduling conclusion follows from it.

Place external assumptions, proved statements and unknowns beside the diagram.
Several arrows, feedback or fan-in alone prove no execution, fairness, race or
ordering property. **Global Cone/Expression coverage: NOT AUTOMATICALLY
VERIFIED** accompanies any complete-model review based on the current scoped
certificate.
