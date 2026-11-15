# Observable authoring checks

Use the public smoke and executable repository tests to evaluate an authoring
change. Ordinary builds remain positive; negative files declare expected Lean
diagnostics and run separately.

## Possibility-space and local-contract checks

The [README's worked explanation](../../../README.md#click-wait-and-timeout)
connects these cases to the architectural error: introducing an unexplained
distinction after choosing an inadequate carrier or member map. These are
observable mathematical checks, not runtime simulation tests.

| Scenario | Positive evidence / rejected shortcut |
| --- | --- |
| Adversarial reviewer confuses future scenario classification with runtime knowledge | **Reject as a category error:** "the click handler cannot yet know the future readiness time, therefore `ShortWait / LongWait / Timeout` is invalid hidden nondeterminism." `PossibilitySpace.lean` partitions the whole declared `Scenario` carrier; it does **not** assert that the handler observes `readyAfter` before it occurs, or prove waiting/liveness. **Accept as potentially legitimate** a concrete claim of missing semantic outcomes, invented supplier availability, unsupported environment assumptions or false model-to-code correspondence. Require a precise cited contract or assumption. See the [dedicated FAQ](../../../README.md#does-a-future-outcome-vdp-require-the-running-program-to-know-the-future). This row is a **reviewer-reasoning evaluation**, not a Lean error regression. |
| Network/AZ failure erroneously rejected for lack of an external time simulator | **Reject as a category error:** "Network failure can happen after request arrival, therefore ArchiScript cannot analyze it unless time is simulated." A network/status Cause or justified scenario context can supply `NetworkStatus VDP`, possibly alongside `ZoneStatus VDP`, as factors of an explicit request tensor. Require real supplier histories and full contextual P/E, and permit correlated failures. **Do not claim** that the illustrative network/AZ schema is already a compiled certificate, nor that it proves runtime freshness, delivery or liveness. See the [network-failure FAQ](../../../README.md#can-network-outages-or-availability-zone-failures-be-analyzed-without-a-network-simulator) and [Pattern B.1](../SKILL.md#pattern-b1--network-and-availability-zone-failure-as-external-cone-factors-illustration). |
| One click; short, long and timeout scenarios | [PossibilitySpace.lean](../../../ArchiScriptExamples/PossibilitySpace.lean): `Scenario` retains every natural budget and optional readiness delay; `scenarioSplit` proves inhabited, exhaustive, disjoint regions; `decide` is functional. Includes immediate readiness, deadline equality, late arrival and no arrival. This is a declared scenario boundary, not raw-input validation or a Cone certificate. |
| One `Waiting` member; one Operation; two unequal outputs | [HiddenWaitingBranch.lean](../../../Test/Negative/HiddenWaitingBranch.lean): the successful branch compiles; the timeout branch on the same `decide` and `()` fails at its mapping proof. `PossibilitySpace.no_hidden_branch` proves the general contradiction using `Operation.single_output`. Do not invent a polling loop or reinterpret `none` to repair it. |
| Multiple outgoing Operations | [CorrelatedJoin.lean](../../../ArchiScriptExamples/CorrelatedJoin.lean): distinct `.left` and `.right` generators share `sourceTrace`; `leftTrace` and `rightTrace` are legitimate producer paths, not the same-Operation contradiction or multiple invocations. |
| Correlated diagonal join | In `CorrelatedJoin`, `input_exact id` and `input_valid id` establish the diagonal relation and both projections at the explicit `.join`. All four pairs remain in the mathematical tensor. A full-four-pair Adm would assert two unreachable tuples. |
| Actual incoming orphan | [ContractCoverage.lean](../../../ArchiScriptTests/ContractCoverage.lean): `orphan_incoming` and `orphan_has_no_partner` expose a supplied member discarded by a narrow contract; `orphan_invalid` rejects `InputValid` and `orphan_not_unreachable` rejects either `InputStatus` alternative. [TensorVerification.lean](../../../ArchiScriptTests/TensorVerification.lean) also checks the finite `Verification.unpartnered` diagnostic. |
| Invented incoming coordinate | `ContractCoverage.invented_projection` admits right-`false` although the actual right supplier is constant `true`; `invented_not_incoming` and `invented_invalid` reject that projection and typed `InputValid`. The nominal Bool VDP still contains `false`. Do not impose surjectivity or demand a partner for its unreachable member. |
| Three-factor P and all pair projections pass; E fails | `ContractCoverage.parity_unary_projection` and `parity_projections` cover all unary and pair projections. `full_reach` supplies all eight triples; `parity_invalid` and `parity_status_rejected` reject the four-triple contract through the actual typed APIs. `TensorVerification.pairwise_is_insufficient` supplies `(false,false,true)` and finite tuple-difference diagnostics. |
| Legitimate cross-Cone join | [CrossCone.lean](../../../ArchiScriptExamples/CrossCone.lean): distinct Boolean Causes have equal initial VDPs; `cValue` explicitly supplies `.join` from both, including the external cycle. `input_valid` and `certified` retain the declared boundary/availability conditions. Equal VDPs do not merge the sources. |
| Repeated invocation disguised as internal fan-out | [RootCoherence.lean](../../../ArchiScriptTests/RootCoherence.lean): `mixed_input_not_context` and `mixed_result_not_inCone` reject canonical/noncanonical roots of one Cause, while `fanout_context`, `fanout_consequence`, `fanout_provenance_distinct` and `cross_context` preserve genuine paths and distinct-Cause joins. [MixedRootContext.lean](../../../Test/Negative/MixedRootContext.lean) fails only at the impossible coherence proof. No timed simulation API is implied. |
| Nested external mixed roots | `RootCoherence.nested_owner_only_guard` shows that the owner's guard and local supplier witness pass; `nested_input_not_context` and `nested_result_not_inCone` reject the other Cause's hidden root conflict. Equal evaluations do not identify provenance or establish `RootCoherent`. |
| Rooted X; unsourced Y; declared X ⊗ Y input | [SourceCoverage.lean](../../../ArchiScriptTests/SourceCoverage.lean): `suppliedX`, `missing_sources_rejected` and `no_certificate` prove the missing full input cannot erase the per-generator `inputSources` obligation. `unit_not_reached` and `no_observable_cone` reject empty-product success; changing only the Effect contract still leaves the source fault. |
| Every independently incoming member needs a full partner | [Consequence.lean](../../../ArchiScript/Consequence.lean): `CertifiedDeclaredArchitecture.input_partner` produces a supported full context and a complete tuple in both Adm and Reach, with the supplied member at its position. Grounding witnesses do not restrict universal `inputs` to a selected context list. |
| Source-only event, explicitly unobservable | `SourceCoverage.sourceOnly` certifies `ConeStatus.unobservable` using `sourceOnly_unobservable`; the Effect contract is empty and no unit tuple is reached. `hasCone` guarantees a checked status, not an observable `ConeValid`. |
| All input images empty despite structural suppliers | [Unobservable.lean](../../../ArchiScriptTests/Unobservable.lean): `join_no_incoming` proves `InputSources.unreachable`; `input_status` supplies empty actual images, noTuple and noContract. `certified` proves unobservable status despite nonempty actual Effect positions. This is mathematical partiality, not runtime non-execution. |
| Ungrounded cyclic component | [UngroundedCycle.lean](../../../ArchiScriptTests/UngroundedCycle.lean): `ungrounded` and `source_unreachable` prove there is no coherent rooted supplier, despite a real typed return route. `certified` uses explicit unobservable status; graph arrows alone create no reachability. |
| Infinite raw roots, finite canonical-origin cache | `SourceCoverage.infiniteRootBasis_valid` proves a valid cache with `RootInstance := Nat` and roots `[0]`. Completeness covers each Cause's designated origin, not every raw root value. `RootCoherence` also checks that a cache list containing `true` still seeds only designated `false` roots. |

A useful evaluation verdict has two parts: **Level A**, the precise conditional
local obligations proved (P and E plus required inhabited/unreachable status),
and **Level B**, the external boundary, omitted-cause, domain-contract and
implementation assumptions still requiring architectural review. An independently
authored Adm must precede the equality proof; `Adm := Reach` and unchecked axioms
are not acceptable substitutes. E checks every full tuple: every reachable tuple
must be admitted and **every admitted tuple must be reachable**. Impossible
tuples admitted by mistake remain failures in Adm minus Reach. No case predicts a future PRNG/CSPRNG sample,
assigns probability weights or proves timeout delivery, overall design quality
or **global Cone/Expression coverage (NOT AUTOMATICALLY VERIFIED)**.

## Manual inventory-review cases

Apply the [skill's inventory audit](../SKILL.md#manual-audit-of-the-complete-declared-inventory)
to the complete declared inventories before making architecture-wide claims:

| Case | Required author/reviewer response |
| --- | --- |
| `Cause → X`, isolated `Y ↔ E` | [UngroundedCycle.certified](../../../ArchiScriptTests/UngroundedCycle.lean) is accepted despite no canonical producer for Y/E. Flag the component; a green build, its typed marker and empty images do not prove inventory grounding. |
| Unattached nodes without arrows | [SourceCoverage.sourceOnly](../../../ArchiScriptTests/SourceCoverage.lean) retains unrelated Y/E declarations in an accepted unobservable certificate. Enumerate these too; Cause-starting traversal alone misses them. |
| Isolated component with no connecting dependency/context | Do not claim it necessarily changes unrelated rooted Expressions' reachable tuples. Report the coverage gap explicitly. |
| Unrelated SCC owned by an observable Cone | Explain that `BoundariesComplete` may refuse the overall certificate for lack of a boundary path even when the rooted route's tuples are unchanged. A cyclic marker can change that structural result without establishing production. This is a documented limitation, not an additional compiled fixture. |
| Unexplained disconnected declaration | Ask the architect to remove an accidental leftover, document an intentional unreachable/excluded component, or repair an omitted Cause/dependency. Record the disposition as author judgment and an unverified coverage assumption. |
| Later connection to a join | Recheck mandatory source accounting and complete contextual P/E; live X with unsourced Y fails now and is not a deferred orphan/SCC diagnostic. |

Inventory-wide diagnostics and all-generated-Expression/Cone coverage are separate
[0.8.0 tasks](../../../plans/0.8.0.md). Neither is supplied by this manual audit.

## Other semantic and proof regressions

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
