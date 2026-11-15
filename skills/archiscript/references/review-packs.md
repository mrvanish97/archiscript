# Optional review tooling

Review approval, responsibility, source bindings and findings are workflow
metadata. They are not the mathematical acceptance boundary of 0.7.
The public calculus imports neither `Review` nor `Operation.Declaration`.
Existing prototype exporters import those companion modules explicitly.

Report three independent facts: the model's declared scope and assumptions;
its actual theorem/audit status; and any human review decision. Use **draft**
for missing declarations or proofs, **conditional** for unsupplied assumptions,
and **certified declared contexts** for a completed audited concrete certificate.
A human approval flag cannot supply a missing Lean proof.

The PaymentWebhook prototypes still generate readable review snapshots. Their
member maps and branch bindings are useful, but those snapshots are not new
Cone certificates. A partial operation's undefined mapping makes no runtime
claim about an absent write or event.

When using a prototype exporter, build its imported Lean target first. Bind
the revision to checked sources, the exported projection and substantive review
metadata; exclude approval fields. Reject sources changing during export.
Canonical IDs and source identity govern diffs; list order without semantics
must not create findings. Regenerated draft artifacts remain draft until an
engineer records approval.

A 0.7 review identifies the concrete certificate, supported analysis relation,
full tuple contracts, cyclic boundaries, external assumptions and the actual
transitive axiom report. **Global Cone/Expression coverage: NOT AUTOMATICALLY
VERIFIED.** Universal coverage automation is a next-version backlog item;
neither review approval nor a chosen presentation family replaces it.
