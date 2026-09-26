# Small evaluation set

These cases are manual decision checks, not a behavioral benchmark or proof of
automatic skill invocation. Review whether an answer makes the expected
modeling decision and exposes missing assumptions.

1. **Missing invalid input**
   - Prompt: “Model login input as either a known user or a new valid user.”
   - Expected: reject the success-only carrier unless an upstream guarantee is
     explicit. Ask what raw boundary is independently supplied and what forms
     it admits; adding an `invalid` constructor alone is not evidence of
     adequacy.

2. **Unjustified parameter**
   - Prompt: “Parameterize report generation by locale; every locale exposes
     the same generate and download operations but produces different text.”
   - Expected: use an ordinary partition/model; changed values do not change
     outbound-operation availability.

3. **Registry branch identity**
   - Prompt: “Give two operations a branch named `existing`, then refer to the
     first branch from a theorem.”
   - Expected: distinct `(OperationName, BranchName)` addresses; resolve the
     first through its registry and require explicit effect premises.

4. **Legitimate Lean inductive label**
   - Prompt: “Use `inductive RequestIndex | zero | positive` for a classifier.”
   - Expected: allow it. Explicitly closed constructor domains and proof
     induction are legitimate; unjustified generalization is the problem.

5. **Purpose before syntax**
   - Prompt: “What is ArchiScript for, and how should I model a project loader?”
   - Expected: explain a checkable architectural contract; start from supplied
     strings/URIs, derive semantic objects, then connect them with partial
     arrows. Explain how composition exposes incompatible paths and distinguish
     subdomain relationships from the operation graph and runtime order.

6. **Responsibility on one branch**
   - Prompt: “Registration belongs to the API team, but creation belongs to the
     storage team. An alias should keep those owners.”
   - Expected: operation `responsibilityOwners`, branch override via `some`,
     inheritance via `none`, canonical resolution for aliases. Keep team
     responsibility separate from `SourceRef`; no invented effect guarantee.

7. **Proportionate proofs**
   - Prompt: “Add a theorem for every branch, alias, and contract field.”
   - Expected: explain which statements harden requirements; use core laws and
     fields directly for repetitions. Honor an explicit request for API tests
     without presenting reflexivity as verification of production effects.

8. **Flat declaration with justified regions**
   - Prompt: “My string VDP lists EmptyString, InvalidUri, and Uri, each defined
     through the appropriate parent and complement. Must I add a taxonomy?”
   - Expected: no. Check the selected members' correspondence, coverage, and
     disjointness; accept the flat declaration. No extra tree or warning.

9. **Independent overlapping subdomains**
   - Prompt: “EmailPresent and NamePresent overlap. Must I change their definitions?”
   - Expected: supporting subdomains can overlap and need not exhaust their
     parent. Partition obligations apply only when selecting distinct VDP
     members; use intersections/complements or grouping at that boundary.

10. **Coarser architectural resolution**
    - Prompt: “Two field predicates induce four combinations, but the consumer
      only needs valid versus invalid.”
    - Expected: retain the carrier and group the three failing regions into one
      member. Explain that another VDP may expose all four; do not force a
      one-leaf-per-region tree onto the coarser VDP.

11. **Unjustified generalization**
    - Prompt: “The only project locators I support are directory, package.json,
      and index URIs, so their union is the entire input carrier.”
   - Expected: distinguish an explicitly closed protocol from an externally
     supplied URI boundary. In the latter case, retain unsupported and failed
     inputs using the established parent and relative complements. Explain that
     this is a review finding, not a current automatic Lean diagnostic.

12. **Circular semantic correspondence**
    - Prompt: “I set `regions i := P.member i`; `P.Realizes regions` proves the
      classifier has the right meaning. Can I hand this off?”
    - Expected: reject it as independent semantic justification. Ask for
      membership predicates motivated by the boundary and stated separately
      from `P.classify` and `P.member`; classifier fibers remain valid derived
      views.

13. **Legitimate narrow boundary**
    - Prompt: “An upstream parser supplies `ValidatedEmail` with a checked
      contract; should I replace the carrier with all strings?”
    - Expected: accept the narrow carrier if the upstream guarantee is real and
      in scope, and record that boundary evidence. Do not mechanically broaden
      every carrier.

14. **Mutable observation without context**
    - Prompt: “Classify a payment event using `alreadyRecorded(eventId)` from a
      database lookup, then act on the classification.”
    - Expected: ask which snapshot or transaction fixes membership, surface
      the race between observation and effect, and leave conformance unknown
      until the implementation contract is reviewed.

15. **Genuine temporal nondeterminism**
    - Prompt: “Model a remote call that may time out or succeed based on
      scheduler and network timing as one deterministic member mapping.”
    - Expected: distinguish missing source context from genuinely temporal
      outcomes. Do not invent fictional information solely to preserve a
      deterministic operation; state the calculus limit or use a complementary
      model.

16. **Binding without conformance**
    - Prompt: “`duplicateSuccess` points to `webhook.ts#handleWebhook`, so mark
      the implementation verified.”
    - Expected: report the declared or resolved location separately from code
      conformance. Ask for explicit evidence and retain unknown effects.

Limitations: these cases do not measure trigger reliability, token cost, or
semantic adequacy automatically. They are a compact reviewer checklist.
