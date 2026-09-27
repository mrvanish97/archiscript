# Changelog

## 0.2.0

- Added `Domain.relativeComplement` and `Partition.HasMembers`. A
  `SemanticPartition` now carries the selected member predicates and their
  classifier correspondence proof for review and implementation handoff.
  Supporting subdomains may overlap; selected VDP members remain nonempty,
  exhaustive, and disjoint. The FormInput example checks a four-member view
  and its two-member coarsening without requiring a taxonomy tree.
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
- Added object-addressed review findings, semantic snapshot diffs, and a
  revision-bound approval gate. The revision covers checked sources, the Lean
  projection, and substantive review metadata. Export builds imported Lean
  targets first, rejects source changes during export, and tests Lean/Python
  approval agreement. Generated packs remain drafts until an engineer records
  approval.
- Updated the README and authoring skill to distinguish model proofs, human
  architectural approval, implementation locations, evidence references, and
  code conformance. Added negative Lean checks and skill API smoke coverage.

## 0.1.0

- Introduced the Lean core: finite value-domain partitions, partial operations and composition laws, canonical branch identities, and parameterized routing.
- Added a user-registration example, positive and negative checks, and an AI authoring skill.
