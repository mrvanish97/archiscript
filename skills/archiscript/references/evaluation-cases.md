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
   - Expected: operation `owners`, branch override via `some`, inheritance via
     `none`, canonical resolution for aliases. No invented effect guarantee.

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

Limitations: these cases do not measure trigger reliability, token cost, or
semantic adequacy automatically. They are a compact reviewer checklist.
