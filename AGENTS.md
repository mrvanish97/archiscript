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
