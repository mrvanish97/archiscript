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
    - Prompt: “I set `members i := P.member i`; `P.HasMembers members` proves the
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

17. **Same payload, different preexisting state**
    - Prompt: “A webhook JSON object has `eventId` and `status`. Define
      `duplicateSuccess` as a property of that JSON object and partition only
      the payload.”
    - Expected: reject the payload-only carrier for a decision that depends on
      existing ledger state. Model a product such as
      `WebhookPayload × LedgerObservation`, with a stated source and observation
      context for the latter. Show that identical payloads paired with different
      ledger states reach different members. Do not claim the ledger snapshot
      remains current without an explicit contract; keep that risk visible.

18. **Practical union carrier**
    - Prompt: “The upstream protocol explicitly admits either a JSON request
      or a signed binary envelope. Is a union carrier forbidden?”
    - Expected: allow the union if that is the independently established
      boundary. Define semantic members over the full union and check coverage.
      Do not confuse a legitimate carrier union with an unjustified union of
      only the successful cases.

19. **Constructor closure sold as boundary evidence**
    - Prompt: “The real input is JSON, but my `inductive ValidInput` has only
      `newUser` and `existingUser`; I proved both constructors exhaustive, so
      the carrier is complete.”
    - Expected: reject the conclusion. `CarrierClosure` concerns values inside
      `ValidInput`; it says nothing about what the JSON boundary can emit.
      Keep the wider boundary or record a scoped upstream guarantee. The VDP
      must then cover every value of whichever carrier is justified.

20. **Opaque predicate disguised as a formula**
    - Prompt: “I declared `opaque scanPasses : Domain Input` and used
      `.predicate scanPasses` so the review says `lean-predicate`.”
    - Expected: identify the evidence laundering. Use `.opaque reason
      (by decide) scanPasses`, keep the reason visible through composed derivations, and
      do not infer a passing scan from an addressable result ID. A named Lean
      constant is not automatically an inspectable formula.

21. **Narrowing with no wider origin**
    - Prompt: “The decoder emits `Nat`; I recorded only the post-decoder type
      and called it an external narrowing from JSON.”
    - Expected: require the upstream origin in `externalNarrowing`; identify
      the external validator, scope, claim, and revision. Do not model the
      decoder as an ArchiScript carrier transformation: operations map members
      only. The guarantee remains trusted unless imported or checked, and
      rejected raw inputs do not vanish from the architecture's boundary account.

22. **Same type, different boundary**
    - Prompt: “Two services both use `Nat`. Can I reuse one service's carrier
      origin to justify a partition of the other's input?”
    - Expected: no. Lean type equality alone does not establish boundary
      identity. Tie the source, scope, and revision to the actual appearance or
      model operation; flag any unmatched identity as a review gap.

23. **Self tensor mistaken for one value**
    - Prompt: “Both factors use the same request VDP, so classify one request
      twice and drop the mixed member pairs.”
    - Expected: retain two independent carrier positions and the full member
      product. Same-value synchronization requires a separate explicit relation.

24. **Unrelated tensor factors**
    - Prompt: “Account A and Payment B seem unrelated; make their tensor fail
      to compile.”
    - Expected: allow the mathematical tensor and ask why these factors are
      jointly relevant. Record a review question without filtering members.

25. **Branches mistaken for concurrent arrows**
    - Prompt: “An operation maps `valid` and `invalid` to different outputs, so
      report a race.”
    - Expected: treat them as alternatives of one member map. Distinct arrows
      with independent sources may prompt ordering review; fan-in alone still
      cannot prove a race without resource/effect semantics.

26. **Tensor mistaken for common refinement**
    - Prompt: “Two partitions share a carrier, so tensor them by intersecting
      their members and discard empty intersections.”
    - Expected: tensor uses two carrier slots and all member pairs. A
      same-carrier common refinement is a different construction.

27. **Compilation mistaken for architectural correctness**
    - Prompt: “The Lean model compiles, so can I tell the team the architecture
      is correct?”
    - Expected: no. Explain that Lean checks the necessary obligations encoded
      by ArchiScript for the declared carrier, predicates, mappings, and laws.
      It does not discover omitted requirements, validate the real boundary, or
      prove production conformance. Keep human review and unresolved assumptions
      explicit.

28. **Rebracketing changes a review finding**
    - Prompt: “`(Request ⊗ Ledger) ⊗ Config` looks risky, but
      `Request ⊗ (Ledger ⊗ Config)` does not. Keep only the first warning.”
    - Expected: reject syntax-tree-sensitive reasoning for a factor-only concern.
      The associator makes these canonically isomorphic. Normalize the review
      question across rebracketing; similarly do not invent a semantic ordering
      from symmetric factor presentation.

29. **Concrete API replaced by an imagined category framework**
    - Prompt: “Import a generic Mathlib monoidal-category instance for VDP and
      rewrite the ArchiScript API around it.”
    - Expected: inspect the installed API first. Version 0.3.1 exposes concrete
      tensor, unit, structural isomorphisms, member operations, and coherence
      theorems. Do not invent an unimplemented abstraction merely because the
      mathematics admits one.

30. **Independent fan-in overclaimed as a race**
    - Prompt: “A manual trigger and a timer trigger both map into the same
      ReconcileMode VDP, so report a concurrency bug.”
    - Expected: recognize the independently sourced fan-in as a concurrency
      review boundary, not a proved bug. Ask whether the paths touch the same
      mutable resource and what ordering, atomicity, idempotency, or
      commutativity guarantees exist.

31. **Cycle overclaimed as concurrency**
    - Prompt: “ReconcileMode -> ReconcileNext -> ReconcileMode is a cycle, so
      this architecture is concurrent.”
    - Expected: reject the inference. A cycle can be an ordinary sequential
      retry/state-machine loop. It becomes more interesting when an independent
      source can enter the loop and the involved operations share mutable
      effects; keep the stronger concurrency claim UNKNOWN without such
      semantics.

32. **Fan-out incorrectly encoded with tensor**
    - Prompt: “One ReservationMutation should persist a write and publish an
      outbox message, so model it as
      `persistMutation.tensor publishMutation`.”
    - Expected: reject that encoding. `Operation.tensor` consumes two
      independent source slots. One semantic mutation with two downstream
      contracts is ordinary graph fan-out: two operations with the same source
      VDP.

33. **Tensor operation diagram exploded mechanically**
    - Prompt: “Draw every member arrow induced by
      `(parseUser ⊗ planInventory) ⊗ id` so reviewers can see the tensor.”
    - Expected: prefer the factored view. Show the elementary VDP member maps
      for `parseUser`, `planInventory`, and `id`, then state that their
      tensor induces the product operation. Expand Cartesian member arrows only
      when a specific product branch is the review focus. Do not hide or prune
      product members; hide only mechanically induced detail.

34. **Focused tensor view silently drops members**
    - Prompt: “PaymentTrigger ⊗ ReservationState has ten members, but only show
      the two `held` cases and omit the rest from the diagram.”
    - Expected: keep the focused view compact but account for the hidden product
      members explicitly. Label the total cardinality and add a display-only
      grouping such as `[display group: other 8 members]`; state that the group
      is not a VDP member and list or otherwise account for its contents. Never
      imply that tensor pruned those combinations.

35. **Diagram styling mistaken for semantics**
    - Prompt: “Use the same VDP container styling around three operation factors
      so the tensor looks visually grouped.”
    - Expected: reject the ambiguous visual grammar. Reserve VDP containers for
      actual VDPs. For operation algebra use operation-shaped nodes and label the
      view explicitly. Follow the established/default diagram theme; do not make
      hard-coded colors carry semantic meaning.

Limitations: these cases do not measure trigger reliability, token cost, or
semantic adequacy automatically. They are a compact reviewer checklist.
