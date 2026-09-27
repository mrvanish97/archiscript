# Asphalt boundary ledger

This ledger makes omissions visible before a reviewer treats
`requestReservation` as deploy eligibility. All items below are open. The Lean
model proves only its declared admission classification at one observation.

| ID | Omitted or weak fact | Why it changes the outcome | Required authority |
| --- | --- | --- | --- |
| B-01 | Artifact signature, builder identity, SBOM, source revision | Approved digest may still be untrusted | Supply-chain verifier bound to digest |
| B-02 | CI and scan *results* and tested revision | A reference can identify a failed or stale run | Result resolver, not reference presence |
| B-03 | Human approval identity, scope, expiry, revocation | Revision string is not authenticated approval | Approval service and current policy |
| B-04 | Effective IAM and delegated roles | Credentials may be denied or overprivileged | IAM graph/policy analyzer |
| B-05 | Network reachability and topology convergence | Revision number does not prove no permitted path | Network analyzer plus observed dataplane |
| B-06 | Tenant, regional and provider quota reservations | Available counters race with other deploys | Atomic quota allocator |
| B-07 | CPU, memory, IP and connection reservations | The Lean capacity field is only observed capacity | Atomic multi-resource allocator |
| B-08 | Maintenance windows, deployment freeze, incident mode | These can forbid a currently requested action | Versioned policy decision |
| B-09 | Feature flags and control-plane version skew | Same input may receive different decisions | Configuration revision and compatibility tests |
| B-10 | Lease clock source and skew bound | `now < expiresAt` is a snapshot relation | Server-side fencing and temporal analysis |
| B-11 | Database migration phase, backfill, old-version population | Schema number and Boolean rollback compatibility are too coarse | Migration controller and compatibility proof/test |
| B-12 | Secret and key version per workload | Rollback can fail after revocation | Secret rollout observation |
| B-13 | Certificate propagation and DNS TTL | Accepted changes may not have converged for clients | Endpoint probes over an observation horizon |
| B-14 | Actual infrastructure generation and manual drift | Approved desired state can differ from runtime | Terraform plan/apply and fresh observation |
| B-15 | Provider operation identity and unknown outcome | Timeout cannot be treated as failure | Idempotent provider API and reconciliation |
| B-16 | Durable event publication and consumer offsets | DB/event split can lose or duplicate work | Outbox and consumer idempotency tests |
| B-17 | Region replication position and old-primary fencing | New primary may race with late old-region writes | Temporal model plus write-authority service |
| B-18 | Health evidence delay and sample sufficiency | No observed failure is not known healthy | Telemetry contract and runtime probes |
| B-19 | Data deletion and retention copies | `deleted` cannot be one state | Data inventory, legal review, deletion evidence |
| B-20 | Restore epoch, dedupe tables and audit continuity | Backup restore can resurrect processed work | Recovery drills and epoch design |
| B-21 | Source, Terraform and test revision binding | `.resolved` and evidence strings are assertions | Source/evidence resolver |
| B-22 | Admission carrier completeness | The Lean `Input` structure may omit production facts before partition checks begin | Reviewed external root scope or checked upstream value contract |
| B-23 | Opaque policy/security subdomains | A named region without a formula cannot support formula-based deduction | Explicit opaque status, reason and review question |

## Open findings for the current Lean slice

- **F-01 — critical, evidence laundering.** `evidenceAddressable` checks that
  references exist, not that results passed. The checked theorem
  `scan_reference_can_hide_failure` demonstrates classification as
  `requestReservation` even with a reference called `scan-failed`. The string
  name itself carries no result semantics. **Status: open.**
- **F-02 — critical, action precedence.** `satisfied` wins before stale policy,
  expired lease, or supersession. That may be appropriate for a read-only
  acknowledgement but cannot authorize a mutation or claim compliance.
  **Status: open, needs consumer contract.**
- **F-03 — high, unverified time.** `fenced` uses supplied `now`, expiry and
  epoch values. Lean proves a relation among them; it does not establish that
  the mutation backend will check the current epoch. **Status: external.**
- **F-04 — high, no executable review handoff.** Canonical branches exist, but
  their implementation is marked `unimplemented`; no Asphalt review revision,
  reviewer approval, source resolver, or evidence observation has been created.
  **Status: open.**
- **F-05 — high, no full-system invariant model.** Network isolation, tenant
  isolation and unique regional write authority are represented only by
  fixtures or open obligations. **Status: external/unsupported by this slice.**
- **F-06 — high, orphan reservation.** The coordinator can reserve IPs and crash
  before writing durable intent. AS-031 demonstrates capacity consumed without
  an outbox record or deployment history. Recovery needs an allocation lease or
  reconciliation protocol. **Status: open.**
- **F-07 — high, carrier provenance.** The signed-count probe preserves `Int`
  upstream and proves that a decoder emitting `Nat` values only for nonnegative
  inputs satisfies its declared source member. A decoder returning the absolute
  value of `-1` cannot satisfy that contract. This checks a *modeled* value
  relation, not the production parser or completeness of Asphalt's `Input`.
  **Status: open for the full admission boundary.**

No finding is considered addressed by a passing Lean build or by the fake
adapter tests. To close one, link a specific check, its source and observed
revision, and rerun review after the checked model changes.
