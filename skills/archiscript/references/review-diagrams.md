# Review diagrams for 0.7

A diagram is a projection of checked declarations. State the question, scope,
hidden detail and proof status in its caption.

| View | Nodes | Edges / annotations |
| --- | --- | --- |
| Semantic decomposition | Declared Subdomains | Proved containment and each particular exhaustive split |
| VDP topology | Whole nominal VDPs | Named whole-VDP Operations |
| Member mapping | Members inside VDPs | Defined source-to-target mappings; `none` shown outside the VDP |
| Linear Expression | One typed Operation sequence | Explicit start and Effect boundary, including cyclic entry |
| Cone / dependencies | Derived occurrence identities | Non-exclusive routes and actual local/external suppliers |
| Contextual tensor | Full factor/member product | Independently derived images, full-tuple Reach and Adm |

A decomposition view may show several trees with the same root. Only siblings
within one proved split must be disjoint. Every named region is nonempty;
intermediate set expressions may be empty.

For a tensor, display full cardinality even when the reachable relation is
smaller. For example, a Boolean self tensor has four members; a common-source
join may reach only two diagonal tuples. Label `Reach = Adm` with the actual
proof and owning context. A diagram must not prune mathematical members or
create an Operation from common-source fan-out to a product.

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
