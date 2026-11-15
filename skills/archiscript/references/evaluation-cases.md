# Observable authoring checks

Use the public smoke and executable repository tests to evaluate an authoring
change. Ordinary builds remain positive; negative files declare expected Lean
diagnostics and run separately.

| Scenario | Expected evidence |
| --- | --- |
| Multiple trees with a shared root | Both splits prove coverage/disjointness despite inter-tree overlap |
| Empty named region, gap, overlap, wrong parent | Construction or required proof fails; empty intermediate predicates remain legal |
| Project-reference URI boundary | Eight success/failure leaves from verified ancestry; successful leaves do not cover Uri |
| Infinite carrier / finite members | Nat example covers every natural without enumerating carrier values |
| Empty string, array and absence values | Real inhabitants of explicitly chosen predicates |
| Constant Boolean Operation | True-only image; False remains a member of the target |
| Partial map | Undefined member omitted from the image without an execution claim |
| Linear cyclic route | Finite typed walk with the expected alternating member |
| Swap loop | Cumulative closure contains both members; successive powers do not stabilize |
| Delayed terminal discovery | Stable terminal observations before closure cannot terminate the analysis |
| Shared-source join | Full product retained; off-diagonal tuples rejected by reference/contract agreement |
| Constant supplier at a join | Projections use its strict incoming image, not all target members |
| Three Boolean factors | Pairwise completeness does not certify all triples |
| Missing partner / extra or missing tuple | Witnessed orphan, `Reach` minus `Adm`, or `Adm` minus `Reach` |
| Missing supplier / false tensor return | Typed occurrence or composition fails |
| Infinite histories | No finite configuration enumeration follows from finite member alphabets |
| Missing context certificate | Public certificate construction fails |
| Missing Cause inventory | Mandatory `causeNonempty` prevents an empty architecture certificate |
| Direct or transitive missing proof / custom axiom | Compiled dependency audit rejects the result |
| Conditional result labeled concrete | Certificate audit rejects unsupplied parameters |
| Admissibility defined from Reach | Actual-field audit rejects untagged, indirect, inline and opaque complete certificates; negatives allow only CONTRACT_AUDIT errors |
| Selected family claims completeness | Scoped certificate and explicit unverified global status remain distinct |
| Two arrows targeting the same nominal C | Certified one-Cause Cone, two derived positions; equal/different images and correlated joint relation |
| One shared multi-step h;k suffix | Both histories survive one authored downstream graph |
| Collapsed coordinate or fake shared-target join | Missing basis closure, wrong producer provenance or missing tensor supplier fails |
| Entry plus feedback at a marked boundary | Typed return allows one deliberate observation; repeated visits enlarge its image |

The shipped gate is:

```bash
uv run --no-project python scripts/verify-lean.py
```

Its machine-readable report records actual command outcomes, declaration audit
and checked-source digest. No claims about production conformance or external
business truth follow merely from these tests.
