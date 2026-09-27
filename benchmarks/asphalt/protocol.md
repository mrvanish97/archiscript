# Asphalt evaluation protocol

This is an experiment protocol, not a favorable review of ArchiScript. Record
the architecture and implementation defects before giving the participants the
seed catalog. A passing Lean build earns no credit by itself.

## Comparison arms

Give each arm the same deployment-control-plane requirements, seeded repository
state, time budget, fake provider contract, and engineering reviewers. Keep the
31-case oracle separate from the prompt. Randomize case order and rotate the
strong coding agent or run multiple replicates to reduce operator effects.

| Arm | Allowed workflow |
| --- | --- |
| A | Requirements → coding agent → code and tests |
| B | Requirements → architecture Markdown/diagrams → coding agent |
| C | Requirements → ArchiScript skill → Lean → human review → implementation |
| D | Arm C plus network, IAM, Terraform, temporal and runtime analyzers |

Do not grant C credit for checks available only in D. Record analyzer setup and
maintenance time for D. Do not let an arm see another arm's model or findings.

## Case adjudication

For every seeded defect, an independent evaluator records:

1. The first stage where the arm identified it: architecture, review,
   implementation test, external analysis, runtime probe, or never.
2. The exact artifact and line or result that identified it.
3. The claim made: `PROVED`, `DISPROVED`, `CONDITIONAL`, `UNKNOWN`, or
   `NOT_MODELED`. `CONDITIONAL` includes its unresolved assumptions.
4. Whether the proposed action prevents the defect in the supplied scenario.
5. Any confident claim that exceeded the evidence, especially a checked Lean
   fact being presented as a current production fact.

Credit `UNKNOWN` only when it names the missing observation or verifier and
prevents an unsupported safety claim. Do not score it as detection. An external
test that passes on a fake adapter is evidence for that adapter only.

The catalog's `expected` and `oracle` fields are adjudication aids, not prompts
for the participants. During blinded trials, store the catalog outside the
participant checkout and inject one seeded defect at a time into equivalent
starting snapshots. The fixtures in this repository are public development
fixtures; they are not blinded trial results.

## Review tasks

Ask engineers to answer without reading the entire Lean source:

- Why could an Internet client reach this production database?
- Which attempt currently owns the environment and which epoch fences writes?
- What happens when success for attempt 8 arrives after attempt 9 succeeds?
- Which immutable artifact digest and policy revision were approved?
- Can R19 run after schema contraction and secret rotation?
- Which topology revision supports the no-path claim?
- Which code and infrastructure resource implement a named branch?
- What changed since the approved model and since the last observed runtime state?

Record answer time, correctness, sources consulted, and whether the review
artifact hid an important fact. A reviewer needing a whole-graph diagram or
large Lean search for a routine question is a review-scalability failure.

## Metrics

Record per arm and per case: defects caught before coding, defects caught only
after coding, missed defects, false positives, actionable `UNKNOWN`s, false
confidence events, reviewer decisions changed, implementation rework, and
infrastructure drift found. Also record model creation/review/change time,
proof repair time, manually selected member count, branch count, artifact size,
external assumption count, analyzer count, duplicate declarations, and
revision mismatches. Keep raw timings and case evidence; do not replace them
with a single aggregate score.

Two primary questions are:

1. Did the architecture process force a useful decision that would otherwise
   have stayed implicit?
2. Did it make an unsupported claim look proved, reviewed, or current?

The second question has priority when evaluating safety claims.

## Pre-registered kill criteria

Treat any of the following as an adverse result, even if many Lean checks pass:

| Criterion | Observable failure |
| --- | --- |
| State explosion | More than 1,000 manually enumerated semantic members for the target system, or a forced Cartesian member product |
| Boolean laundering | A global security, capacity, migration or health claim accepted from an unexplained Boolean |
| Proof laundering | Any external assumption or stale reference reported as a Lean-proved production fact |
| Review overload | Median focused review task takes more than 20 minutes or requires a whole-model diagram or Lean search |
| Model duplication | A routine single-source change requires synchronized manual edits in more than three unrelated model/implementation artifacts |
| Concurrency fiction | A race is declared safe solely because a member mapping chose one result |
| Stale-snapshot fiction | A fixed-observation proof is described as valid after relevant world revisions change |
| Poor change locality | One infrastructure policy change forces edits to more than one quarter of otherwise unrelated semantic partitions |
| Global invariant gap | Isolation or unique-write-authority claim can only be encoded as author-asserted local state |
| Excessive proof tax | Formalization plus maintenance takes longer than the rework it prevents across repeated trials |

The numeric thresholds are experiment decision rules, not established product
facts. Report sensitivity to thresholds. One critical false-confidence event
must be analyzed individually rather than averaged away.

## Full-scale gate

The present slice is not the full-scale trial. Before claiming the target scale,
the trial must include 25–40 genuine VDPs, 40–70 real operations, 150–250 named
branches, at least ten independent evidence sources, 8–12 implementation
modules, multiple infrastructure modules, and focused review views. Count only
partitions with explicit semantic members and only branches with checked
member mappings. Publish the number of failed or unsupported obligations too.

Proceed in increments. If the model hits a kill criterion before the scale
target, stop expanding it and report the failure. Filling the remaining quota
with decorative VDPs would invalidate the experiment.

## Current results

Only the local Lean slice and deterministic fixtures have been executed. Arms
A–D, blinded evaluation, cloud/IAM/network/temporal analyzers, human review
timings, and implementation drift measurements have **not** been run. The
current corpus therefore supports no comparative effectiveness claim.
