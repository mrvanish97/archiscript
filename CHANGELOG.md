# Changelog

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
- Added explicit carrier origins: identified external roots or narrowing
  guarantees, internal outputs tied to typed model operations and recursive
  source origins, and derived value contracts.
  External narrowing also retains its upstream origin; a post-validator carrier
  cannot be presented as a root without an explicit trusted claim.
  Finite constructor coverage is a separate `CarrierClosure` and never supplies
  boundary origin by itself.
  Derived contracts prove that emitted values come from a named upstream member,
  cover the downstream carrier, and retain the upstream carrier's provenance.
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
