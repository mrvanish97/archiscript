# ArchiScript 0.7 design and proof guidance

The implementation contract is
[the 0.7 handoff](../archiscript-docs/chapter-1/stage-3/archiscript-0.7.0-lean-core-rewrite-handoff.md).
Consult relevant Stage 1/2/3 sources in `../archiscript-docs` before changing
semantics. The handoff deliberately supersedes classifier-primary VDPs,
nonlinear Expression terminology and earlier universal-surjectivity proposals.
Use current Lean declarations for API names. Report unavailable design sources
or proposed departures explicitly.

## Semantic boundary

- Treat ArchiScript as **a priori semantic architecture review**, between
  high-level diagrams and existing or proposed code. Analyze complete declared
  possibility spaces and their joint member-level consequences, not observed
  runtime values, execution traces or an implementation simulator. Modeling
  does not itself prove code conformance or real-world boundary completeness.
- Distinguish the complete carrier, semantic Subdomains (including intermediate
  and supporting regions), and **selected VDP members**. A member is itself a
  chosen Subdomain of the unchanged carrier. Audit the ancestry and proof of
  each declared SemanticSplit as well as coverage, disjointness and inhabitation
  of the final selected family. In the String example, AllStrings splits into
  Invalid/Valid and Valid into ValidAndPermitted/ValidAndDenied; the three
  selected leaves cover String, while Valid remains intermediate. A coarser
  VDP may instead select Invalid/Valid and leave the permission children
  unselected: VDP members need not be the finest leaves, but overlapping
  ancestors and descendants cannot be selected together. Carrier stability
  applies within one VDP refinement, not between different Operation endpoints.
  This is logical refinement, not runtime validation. Keep flat selections and
  independent supporting trees legal; see the README String example.
- Interpret a request for two distinct outputs from one input member of one
  Operation as a missing semantic distinction or justified supplier/context
  question before proposing a nondeterministic member map. Never conceal
  necessary information behind invented outcome labels or simulated execution.
- Keep the public `ArchiScript` root focused on the calculus. Companion models
  belong in `ArchiScriptExamples`. Workflow bindings and approval metadata are
  optional imports, not mathematical acceptance criteria. The installed skill's
  smoke example imports only the public library and its proof-audit module.
- Declare semantic Subdomains first, with parent evidence and nonemptiness.
  Intermediate `Domain` predicates may be empty. Empty strings, arrays and
  absence-like values are actual values when their chosen carrier includes them.
- Supporting Subdomains may overlap and need not exhaust their parent. Every
  declared `SemanticSplit` has finite nonempty children, containment, union
  coverage and sibling disjointness proofs. Independent trees may share a root.
  Flat declarations and coarsening remain legitimate; no global taxonomy is
  required. VDP members are declared Subdomains, not manufactured classifier fibers.
- Preserve full meaningful boundary carriers, including failed and invalid cases.
  Lean cannot establish real-world exhaustiveness from an already narrowed type.
  Preserve the Stage 2 eight-leaf project-reference regression and its explicit
  URI/filesystem interpretation boundary.
- Operations connect whole verified VDPs and remain partial member maps.
  `none` is undefinedness, not runtime non-execution. Non-surjectivity is valid.
  Several outgoing Operations are non-exclusive declared possible routes; no
  execution, delivery, fairness or ordering obligation follows from declaring them.
- Keep symmetric monoidal tensor full, including self tensor. Never reinterpret
  it as common refinement, a diagonal, filtered product or runtime parallelism.
  Coproduct is tagged OR and cannot replace a simultaneous structural join.
- `Expression` is a finite linear chain over registered names and nominal objects.
  `Presentation` retains nonlinear algebraic syntax and selected families.
  A selected family is not complete Cone discovery. Equality of denoted Operations
  proves algebraic normalization, not preservation of all contextual effects.
- Composition does not delete intermediate nominal objects. Hiding one is an
  architecture projection. Structural endpoint changes require concrete
  `PartitionIso` transport and a commuting square. Distributivity is a canonical
  proved isomorphism, not definitional equality or a physical optimization.

## Consequence and verification boundary

- `ArchitectureSignature` is the claimed-complete declaration inventory.
  Keep generator identities, actual supplier structure, Cause ownership, root
  instances and producer histories. Equal nominal VDPs do not identify occurrences.
- One Cause denotes one concrete external event with one whole initial VDP.
  `Term.RootCoherent` requires the designated origin for every Cause, including
  nested external suppliers. Canonical fan-out and cross-Cone joins are valid;
  combining distinct invocations of one Cause is outside this API. Do not add
  simulated timing, event replay or repeated-event composition to repair it.
- Contexts come from existing generator inputs and actual provenance through
  `isInputContext`; do not introduce an author-declared tensor-site entity or
  certify a selected list of favorable contexts. At least one factor in an
  internal use must belong to the studied one-Cause Cone.
- Determine incoming images independently from upstream supplier semantics.
  Require every incoming member to have a full admissible partner and exact
  full-tuple `Reach = Adm`. Do not impose surjectivity onto all factor members.
  Pairwise checks do not establish an n-ary relation. Independent contract
  meaning and external boundary truth remain architect responsibilities.
- Before quantifying over complete input terms, require `inputSources` for
  every declared generator: coherent producers at every factor, or proof that
  all independent factor images are empty. A supplied X with an unsourced Y
  cannot evade the declared `X tensor Y` obligation. `input_partner` derives a
  full admissible and reachable partner for every independently incoming member.
- Cyclic entry and Effect observation points must be typed on actual declared
  routes. `Term.CycleBoundary` supplies one typed entry hole and a nontrivial
  return, with explicit auxiliary factors. All finite traversals contribute to
  the image of one boundary. They do not create one effect factor per iteration.
- Preserve recursive cross-Cone dependencies and full source correlations.
  Finite VDP member sets do not prove finite occurrence histories. A finite
  analyzer must enumerate complete semantic configurations and supply an
  `ExactAbstraction` theorem before certifying architectural reachability.
  Closure is checked on the complete analyzed state, not only terminal images.
- `CertifiedDeclaredArchitecture` requires `causeNonempty`, universal declared-context, Cone and
  terminal-boundary proofs. Proved-unreachable contexts are separate from
  inhabited verified uses. `ConeStatus.observable` requires a real derived
  Effect position and reachable full tuple. `unobservable` requires both all
  Effect incoming images and the independent contract to be empty. Preserve
  intentionally no-observable-effect Causes without inventing an observation;
  tensor-unit success and omitted input-source proofs remain invalid.
- Follow handoff §7.3.1: f/g may target the same nominal C and reuse one h;k
  declaration. Preserve automatically derived histories; never require unique
  named uses, cloned VDPs/graphs or injective generator outputs. The mandatory
  `effectCoverage` proves a seeded, closed, realized finite provenance basis;
  `EffectProvenance` binds actual suppliers to its coordinates. Equal values,
  images and suffixes do not merge positions. A genuine join needs an explicit,
  fully sourced tensor-input Operation. The analytical Effect tensor adds none.
  Typed cyclic return markers separately aggregate repeat visits; finite member
  sets alone do not prove that a finite normalized-history basis exists.
  Cache roots must include each Cause's designated origin, not every value of
  the root-instance type. The latter may be infinite.
- **Global Cone/Expression coverage: NOT AUTOMATICALLY VERIFIED.** Do not claim
  universal generated-path coverage from these scoped certificates. Automation
  is explicitly deferred to the next version. Real-world inventory completeness
  is an external modeling assumption even if a future global checker is proved.
- Manually audit the complete declared Cause/Node/Generator inventory, including
  disconnected nodes, unused declarations and rootless SCCs. Scoped certificates
  and unobservable status do not prove inventory-wide grounding. Flag unexplained
  components to the architect and record removal, intentional exclusion or model
  repair as author judgment. Unrelated components need not change rooted tuples,
  but can obstruct an observable Cone's boundary proof. Keep this limitation
  separate from mandatory local source and P/E obligations.
- Keep concurrency, persistence, transactions and implementation conformance
  conditional on separately modeled semantics. Unsupported conclusions remain
  review questions or `UNKNOWN`.

## Engineering and release checks

- Use `uv` for Python work. Do not spawn subagents without explicit user authorization.
- Preserve legitimate closed enums, `id`/`rfl` proofs, optional branch subsets and
  consumer-specific coarsenings. Regress demonstrated failures instead of adding
  speculative abstractions. Keep changes to meaning explicit.
- The standard gate is `uv run --no-project python scripts/verify-lean.py`.
  It builds first, checks the public smoke, audits actual transitive axioms,
  runs intended-diagnostic negative cases and replays kernels with explicit
  `leanchecker` module names. Reports identify checked source digests and commands.
- Builds treat warnings as errors. No local suppression outside deliberate
  negative fixtures. `sorryAx`, custom axioms and extra computation axioms are
  rejected by the audit; a source-token search is insufficient. Tag concrete
  closed certificates and independent admissibility declarations for additional
  assumption/dependency checks. The release audit also inspects actual installed
  contracts of every closed model/certificate regardless of tags, follows aliases
  and rejects uninspectable closed records. Independent business meaning remains
  a human obligation. Conditional factories are checked at closed instantiation.
- When public algebra, Expression or consequence APIs change, update the full
  authoring skill, API reference, diagrams, public-only smoke, dedicated tests
  and ReservationController presentation stress example together.
- Build imported Lean targets before any `lean --run` export. Bind review
  revisions to checked sources, projection and substantive metadata; exclude
  approval fields and reject source changes during export. Lean and Python
  workflow approval predicates must remain in executable agreement.
- A complete branch-name list covers its chosen name type only. For whole-operation
  handoff, check `Declaration.definedMappingsWithoutBranch` for every registered
  operation; review generation rejects missing coverage. Optional subsets remain
  valid when whole-operation completeness is not claimed.
- Diff review snapshots by canonical IDs and source identities, including edits
  and removals of findings, claims, bindings and evidence. Ignore meaningless
  list order and report each change once. Regenerate artifacts when exporters
  or model paths change; drafts remain draft until an engineer records approval.
- Parse GitHub remote prefixes and strip `.git` explicitly in Bash; ERE has no
  lazy `+?`. Remote/ruleset tests use local command stubs and never mutate remotes.
