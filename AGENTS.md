# ArchiScript design guidance

The sibling repository `../archiscript-docs` contains the original design.
Its Stage 2 model was carefully developed; consult it before changing modeling
semantics, adding abstractions or diagnostics, or revising the authoring skill.
Do not treat a new term or a convenient implementation pattern as a replacement
for the established design.

Start with the sources relevant to the change:

- [Stage 2 scope](../archiscript-docs/chapter-1/stage-2/scope.md): subdomain
  discipline, deduction, architectural boundaries, observation, and parameterization.
- [Stage 2 design](../archiscript-docs/chapter-1/stage-2/design/): concrete models
  that demonstrate the intended semantics.
- [Stage 2 backlog](../archiscript-docs/chapter-1/stage-2/backlog.md): unresolved
  questions and deferred work.
- [Mathematical foundation](../archiscript-docs/chapter-1/stage-1/foundation.tex)
  and [Stage 1 specification](../archiscript-docs/chapter-1/stage-1/spec.md): formal
  definitions and foundational constraints.

Preserve the distinction between supporting subdomains and VDP members.
Subdomains may overlap and need not exhaust their parent; the selected members
of a VDP must be nonempty, exhaustive, and disjoint. Flat member declarations
and coarsening are legitimate. Do not introduce a mandatory taxonomy tree.

Use the docs for design intent and the current Lean source for API names; the
older TypeScript notation is not the Lean API. Identify conflicts or proposed
departures explicitly, with references to the relevant design, rather than
silently redefining the model. Follow explicit user changes to that design.
If the sibling repository is unavailable, report that limitation before making
design-sensitive assumptions.

## Repository conventions and guardrails

- Keep the public `ArchiScript` library focused on the calculus. Put companion
  models in `ArchiScriptExamples`; the installed skill smoke file must compile
  from the public library alone. Keep operation algebra separate from branch,
  responsibility, and implementation-binding metadata.
- Treat a complete `branchNames` list as covering only its chosen name type.
  An empty missing-metadata query over named branches does not prove coverage of every
  defined member mapping. For whole-operation handoff, check
  `Declaration.definedMappingsWithoutBranch` for every registered operation and
  make review generation reject missing coverage. Named branch subsets remain
  valid when whole-operation completeness is not claimed.
- Do not infer value selection or runtime effects from member mappings. State
  needed input/output identity and state-change relations in typed contracts. A proof
  that merely returns the same contract field adds no guarantee; use a negative
  check for the bad case instead. Label preclassified API fixtures explicitly,
  and do not present their constructors as a validated raw-input boundary.
- Build imported Lean targets before `lean --run` exports. Bind review revisions
  to the checked sources, exported projection, and substantive review metadata;
  exclude approval fields to avoid circular hashes. Reject source changes during
  export. Keep Lean and Python approval predicates in executable agreement.
- Diff review snapshots by canonical IDs and source identities, covering edits
  and removals of findings, claims, bindings, and evidence. Ignore list order
  when it has no semantics, and report each change once. Regenerate review
  artifacts after changing exporters or model paths; draft packs remain draft
  until an engineer records approval.
- Parse GitHub remote prefixes and strip `.git` explicitly in Bash. Its ERE
  syntax has no lazy `+?` quantifier. Test remote parsing with local command
  stubs so tests cannot mutate remote rulesets.
- Preserve legitimate closed enums, simple `id`/`rfl` proofs, flat declarations,
  coarsening, and optional branch subsets. Add regression checks for reproduced
  failures rather than replacing the established model with a convenient new
  abstraction.
- Preserve the symmetric monoidal VDP tensor: full independent carrier and
  member products, including self tensor. Do not interpret tensor as common
  refinement, filtered product, pullback, same-value observation, or runtime
  parallelism. `Operation.tensor` maps member pairs and carries no resource
  effects. Keep one operation's alternative branches distinct from separately
  sourced operation arrows.
- Describe Lean as checking explicit necessary model obligations. It does not
  search for omitted requirements or certify a production architecture.
  Concurrency conclusions require resource/effect semantics; keep unsupported
  race or ordering claims as review questions or `UNKNOWN`.
- When the public monoidal API changes, update the authoring skill, its API
  reference and smoke example, and the monoidal regression checks together.
