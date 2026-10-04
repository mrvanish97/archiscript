# Changelog

## 0.4.0

- Added categorical coproducts of VDPs over tagged sum carriers, with canonical
  injections, copairing, uniqueness of the mediating operation, functorial
  mapping, and semantic-partition lifting.
- Restricted coproduct authoring to design-time closed architectural
  alternatives. Coproduct is exhaustive only relative to its sum carrier and
  must not be used to turn runtime-discovered cases into a falsely complete
  external boundary.
- Added checked refinement/coarsening for VDPs on the same carrier using whole
  fine-member containment. The canonical coarsening member map is unique and
  surjective and induces an ordinary total `Operation`.
- Added consumer factorization analysis: consumers constant on coarsening fibers
  factor uniquely through the coarse VDP; failures expose concrete conflicting
  fine members. This supplies machine-checked justification for semantic zoom
  in diagrams and review views.
- Upgraded `FormInput` to a checked refinement/coarsening example and added a
  Browser/CLI coproduct example whose alternatives come from design-time entry
  topology rather than runtime case enumeration.
- Updated the README, AI authoring skill, Lean API reference, smoke checks, and
  regression suite for the 0.4.0 semantics.

## 0.3.1

- Added checked concurrency-review and stateful stress examples covering
  independently sourced fan-in, retry/state cycles, shared state observations,
  same-resource write requests, partial operations, and downstream effect
  contracts represented as ordinary `Operation` values.
- Added `ReservationController`, including a three-factor tensor context and a
  concrete review hotspot where payment authorization and expiry can both
  observe `held` and request incompatible reservation updates. The example
  exposes the topology without claiming that a runtime race has been proved.
- Refined the review-diagram conventions: define elementary VDPs before tensor
  products, reserve VDP containers for actual VDPs, keep members as nodes inside
  those containers, and use separate operation-shaped nodes for operation
  algebra views.
- Tensor operations are now shown factored by default instead of mechanically
  expanding every induced Cartesian member arrow. Product members remain full
  and unpruned; focused views may collapse omitted members into an explicitly
  labeled display group with the hidden members documented nearby.
- Updated the AI skill and evaluation cases to teach the refined visualization
  grammar and explicit concurrency-review signals: independent source
  provenance, shared mutable resources, potentially noncommuting updates, and
  missing ordering/atomicity evidence. Fan-in or cycles alone remain review
  signals, not automatic race or deadlock proofs.

## 0.3.0

- Added the full independent tensor of VDP carriers and semantic members,
  including self tensor with two separate coordinates, plus the Unit VDP.
- Added `SemanticPartition.tensor`, which derives product member meanings and
  their `HasMembers` proof from the factors.
- Added `Operation.tensor` for partial member maps and proved tensor identity
  and interchange with sequential composition.
- Added classification-preserving associator, left and right unitors, and
  symmetry with induced invertible member operations. Lean checks naturality,
  pentagon, triangle, involution, and symmetric hexagon coherence.
- Added monoidal examples and regression checks. Updated the AI skill, API
  reference, and smoke file to teach full-product semantics, Lean's role as a
  checker of declared obligations, and human review of joint use and possible
  concurrency. This release does not model resource effects or claim automatic
  race detection or general model checking.

## 0.2.0

- Added `Domain.relativeComplement` and `Partition.HasMembers`. A
  `SemanticPartition` carries the selected member predicates and their
  classifier correspondence proof, with named theorems for semantic member
  coverage, disjointness, and nonemptiness. An `ArchitecturalPartition` now carries
  carrier origin, optional constructor closure, and typed derivations for selected and supporting
  subdomains into review and implementation handoff.
  Supporting subdomains may overlap; selected VDP members remain nonempty,
  exhaustive, and disjoint. The FormInput example checks a four-member view
  and its two-member coarsening without requiring a taxonomy tree.
- Added explicit carrier origins: identified external roots, trusted narrowing
  guarantees, and architecture-defined semantic domains. Carrier origin is
  separate from operations and never models value-producing dataflow; operations
  map VDP members only.
  External narrowing also retains its upstream origin; a post-validator carrier
  cannot be presented as a root without an explicit trusted claim.
  Finite constructor coverage is a separate `CarrierClosure` and never supplies
  boundary origin by itself.
  External claims remain trusted premises; the model does not prove that
  production code or external validators enforce them.
- Replaced prose `.formula` labels with typed `DomainDerivation` values indexed
  by their exact Lean predicate. Atomic predicates and composition by
  intersection, union, and relative complement have checked denotations.
  Opaque leaves require a nonempty reason and propagate review warnings through composed
  definitions; English descriptions remain review annotations, not formulas.
- Added an `Architecture` handoff container whose listed operations carry
  evidence for both VDP endpoints. The webhook examples now build this object;
  low-level partitions and operations remain independent of review metadata.
- Kept the public `ArchiScript` library focused on the calculus and moved
  companion models into `ArchiScriptExamples`. The registration example now
  preserves selected-user identity in its typed contract. Removed redundant
  reflexivity and contract-field theorems.
- Added canonical operation and branch declarations with responsibility tags,
  branch overrides, implementation dispositions, source references, and
  evidence references. Whole-operation review export rejects defined member
  mappings without a named branch; a named subset remains valid when complete
  handoff is not claimed.
- Added the PaymentWebhook model and seven-VDP network showcase. Generated
  Markdown, Mermaid, TikZ source, and PDF views show topology, semantic members,
  branch mappings, review questions, code bindings, and checked claims. Detailed
  diagrams place member boxes inside their VDP containers.
- Made the webhook input carrier an explicit pair of decoded payload and
  preexisting ledger observation. Duplicate membership depends on both factors;
  the review still marks observation acquisition and consistency as unresolved.
- Added Project Asphalt's adversarial deployment-control-plane slice, seeded
  defect catalog, executable fake-adapter scenarios, and explicit unknowns.
  Its signed-count probe demonstrates a checked modeled narrowing and a
  counterexample; the benchmark reports carrier origins and an opaque security
  subdomain warning. It does not claim production safety or run comparison arms.
- Added object-addressed review findings, semantic snapshot diffs, and a
  revision-bound approval gate. The revision covers checked sources, the Lean
  projection, and substantive review metadata. Export builds imported Lean
  targets first, rejects source changes during export, and tests Lean/Python
  approval agreement. Generated packs remain drafts until an engineer records
  approval.
- Required carrier provenance and complete selected-member definitions in both
  webhook review exports. Their generated Markdown/PDF snapshots now show
  trusted origins and opaque warnings; review validation rejects missing or
  incomplete provenance, and regenerated artifacts carry new model revisions.
- Updated the README and authoring skill to distinguish model proofs, human
  architectural approval, implementation locations, evidence references, and
  code conformance. Added negative Lean checks and skill API smoke coverage.

## 0.1.0

- Introduced the Lean core: finite value-domain partitions, partial operations and composition laws, canonical branch identities, and parameterized routing.
- Added a user-registration example, positive and negative checks, and an AI authoring skill.