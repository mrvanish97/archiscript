# Engineering review packs

The review pack is the human approval interface for an ArchiScript model. It
must make architectural criticism possible without opening Lean source. The
generated PDF is a stable snapshot; the model and structured review record hold
the canonical identities, current state, and findings.

## Review state and gate

Use `draft`, `ready-for-review`, `changes-requested`, `approved`, or
`superseded`. A passing Lean build only establishes internal checks. Approval
must name a reviewer and the exact model revision. Implementation may proceed
through the architecture workflow only when that revision matches the current
model and no open change request remains. Do not infer approval from a PDF,
test pass, or resolved code binding. Approval metadata is a workflow record,
not authenticated identity or proof of code conformance.

Attach findings to canonical IDs. Record the concern, reviewer, requested
change, and disposition (`open`, `addressed`, or `accepted`). If a reviewer
rejects a boundary, owner, or assumption, revise the model and regenerate the
pack; preserve the finding so its resolution can be checked. A new model
revision requires a new approval.

## Two reading passes

Fast pass: scope; changes since the prior revision; boundary and carrier;
Level 0 or 1 topology; major assumptions; owners; and open questions. An
engineer should be able to judge whether the direction is plausible in a few
minutes.

Deep pass: selected member meanings and coarsenings; complete relevant branch
maps including `none`; effects and environmental state; responsibility and
implementation bindings; checked claims with proof references; conditional
claims; unknowns; findings; and source anchors. Present detail to invite
disagreement, not to make approval effortless. The reviewer should be able to
challenge a missing input, unsafe merge, unstable observation, misplaced owner,
wrong code site, absent effect contract, or unsupported claim.

When revising, show semantic changes in terms of added/removed members and
branches, changed mappings, responsibilities, bindings, assumptions, and
unknowns. A Lean source diff can accompany this, but should not replace it.
Display groupings are only visual. Preserve canonical IDs in tables and
findings even when the diagram uses shorter labels.

## Current prototype

The repository's `PaymentWebhook` example has a generated Markdown review pack
and PDF snapshot produced by `scripts/build-review-pack.py`. The exporter reads
members, branch mappings, responsibility, bindings, and theorem-backed claims
from Lean. Review notes and findings live in
`review/payment-webhook.review.json`; the generator validates their subject IDs.
The model revision is a source hash. Pass `--previous` with an older generated
snapshot JSON to include a semantic and review-metadata change summary. This is a focused prototype, not a
general ArchiScript compiler or authenticated review service.
