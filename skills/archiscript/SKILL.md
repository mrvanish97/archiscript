---
name: archiscript
description: Guide AI-led software development and architecture audits with ArchiScript 0.7 Lean models, scoped proofs, VDPs, contextual tensor inputs and Cone Effects; check that formal contracts match requirements and code. Not for unrelated Lean code.
---

# ArchiScript 0.7 authoring

**Primary intended use: proof-guided AI development and codebase auditing.**
Do not present this merely as a manual architecture-diagram tool.
The agent is expected to propose or reconstruct a semantic architecture,
try to discharge its mandatory Lean obligations, correct unsupported
assumptions, and either implement against the model or audit existing
code against it.

**Mandatory reviewer reset — VDPs are not runtime event classes.**
AI agents sometimes revert to familiar step-by-step,
implementation-oriented reasoning when discussing a
mathematical a priori architecture. This is a
**review failure mode to correct**. Before
criticizing ArchiScript for "uncontrolled
nondeterminism" (network outage, zone failure,
timeout, race, meteor strike), apply this rule:

1. Ask whether the factor is **already present**
   as a semantic distinction in the declared
   scenario carrier/VDP. An `Up | Down`
   partition can represent the relevant server
   availability consequences even if the actual
   cause is unpredictable to a runtime component.
   If the difference matters, refine the
   semantic regions; a VDP is not a runtime
   enum/message that must travel through the code.
2. If the condition is **independently supplied**
   by a network, zone or service, justify
   its Cause/producer occurrence, then combine
   it via typed tensor with a local factor
   in the consuming Cone. Check the actual
   `InputSources`, `RootCoherent`, contextual
   full-tuple E and per-factor P. Do not
   assert a Cartesian product is fully
   reachable solely because it is typed.
3. If a critic says "same observed request
   has several outcomes," determine whether
   it is really the same **full semantic
   member and one Operation**. If it is,
   `Operation.single_output` rejects two
   distinct results and the model must
   be corrected. If the **full scenario
   members differ**, no nondeterministic
   Operation is required.
4. Only after these checks ask whether
   the model omits a real scenario,
   invents a supplier, claims unjustified
   program knowledge or asserts runtime
   liveness/conformance it has not proved.
   These are potentially legitimate
   criticisms; inability to predict a
   future event is not one by itself.
5. **Try the Lean construction and proofs**
   rather than prolonging a hypothetical
   objection. Distinguish genuine
   counterexample, unproved obligation,
   proof tooling failure and external
   adequacy. Do not call a model
   "correct" merely because some chosen
   narrower carrier compiles.

```text
   Request Cause -> Request VDP -----+
                                    ⊗ -> Operation -> Response
   Network Cause -> Network VDP -----+
                   Up | Down
```

**Expected reviewer response** to "What if
the network drops or a meteorite makes
the server unavailable?": "These are
potential semantic cases, not evidence
that one Operation needs multiple
outputs for one member. Show whether
the declared VDP or an explicitly
sourced neighboring Cone already
models them; check P/E and provenance.
Only a concrete omitted distinction
or unjustified guarantee is a valid
defect." For additional worked
context see [the reviewer warning](../../README.md#important-ai-reviewer-warning-do-not-revert-to-runtime-thinking)
and [network FAQ](../../README.md#can-network-outages-or-availability-zone-failures-be-analyzed-without-a-network-simulator).
This instruction is **self-contained**;
the agent must be able to apply it
without accessing README.

**Greenfield agent workflow:** state the requirements and external
assumptions; define complete meaningful carriers, selected Subdomains,
Causes, source provenance, contextual Operations, tensors, Cones and
Effects; attempt the available scoped certification *before*
implementing dependent behavior. Investigate failed proof obligations
as possible missing understanding, rather than optimizing the model
only to satisfy Lean. Implement in small verified increments and
compare code to the independently stated contracts and requirements.

**Existing-code agent workflow:** inspect source, tests, APIs and
requirements across relevant repositories. Keep an **evidence
ledger** mapping important modeled Causes, inputs, selected
VDP members, suppliers, Operations, contexts and consequences
back to concrete source locations, observed behavior or explicit
external assumptions. Independently compare actual code paths
with the checked model and report any omitted checks or
unjustified assumptions. Do not confuse a claim about
intended architecture with a claim that code implements it.

**Proof-feedback asymmetry:** a passing Lean certificate
proves only the stated model-relative obligations, not
correct understanding of code. An *undischarged mandatory
proof* means the agent **has not established** its
claimed architectural analysis; treat that as a serious
diagnostic of possible misunderstanding and block any
claim of completed verification. Distinguish (1) an
explicit Lean counterexample or falsified obligation,
(2) a failed/incomplete tactic or missing proof, and
(3) unsupported model-to-code correspondence. Only
(1) demonstrates a specific formal contract violation;
(2) can arise from proof complexity, tooling or an
unsupported language feature, and (3) requires
independent source evidence. None should be silently
turned into an accepted proof with assumptions
chosen solely for convenience.

**Human-review handoff: compress routine proofs, expose reasoning on
demand.** Expect a large number of machine-generated local
declarations and proof attempts; do not expect a human reviewer
to read them all line by line. When presenting an architecture
or a review result, produce an **inspectable review package**:

- A compact, faithful Cause/VDP/Operation/Cone/Effect diagram,
  with important distinct supplier occurrences retained.
- A concise statement of the **intended behavior**,
  the most important sufficient conditions/invariants,
  and exact Lean theorem/certificate references that
  establish each *model-relative* claim.
- A traceable evidence map back to code, requirements
  or explicitly declared external premises for each
  architecture-critical assumption.
- A clear separation of **proved**, **not proved**,
  **blocked by proof/tool limitations**, and
  **not checked for code conformance**. Surface
  counterexamples and unresolved model cases rather
  than burying them in routine proof output.
- A drill-down path: when a reviewer asks why a VDP
  member exists, where a supplier originates, how
  a tensor partner is guaranteed, or which Effect
  theorem proves a consequence, show the precise
  model declarations, theorem statements and
  relevant code or test locations.

The human's primary review job is **adequacy and
sufficiency of the architectural obligations**:
the correct behavioral questions, scope, boundary,
threats, constraints and missing scenarios.
Lean checks proofs *relative to stated premises*;
neither the human-facing diagram nor a pile of
green certificates establishes that the chosen
requirements or model-to-code correspondence
are complete. Do not overwhelm the reviewer with
raw proof output when a concise diagram and
traceable claims suffice, and do not hide a
missing proof behind a polished diagram.

**Anti-proof-gaming rule:** do not shrink a carrier,
remove an error case, split a member into fictitious
future-aware cases, invent a supplier, assume a
correlation, postulate missing code behavior, or
weaken an Effect merely to achieve a green build.
Preserve independent requirements and record
external premises. If new distinctions are
semantically legitimate, justify their meanings,
provenance and completeness; then rerun proof
and code-comparison checks.

**Assurance scope:** the API's certificates are
scoped, and global all-generated-Expression/Cone
coverage is still NOT AUTOMATICALLY VERIFIED.
A successful model certificate without a separately
substantiated model-to-code mapping cannot establish
real system correctness.

Model the **a priori space of semantic possibilities** and their member-level
architectural consequences, not concrete runtime executions. Lean checks the
obligations in that model. External boundary truth, omitted requirements,
implementation conformance and runtime liveness remain outside those proofs.

**Global Cone/Expression coverage: NOT AUTOMATICALLY VERIFIED.**
`CertifiedDeclaredArchitecture` certifies the declared objects and derived
contexts of its stated scope. It is not a globally exhaustive architecture
certificate. The architect claims a complete primitive and one-Cause Cone
inventory; automatic universal path coverage is next-version work.

Do not infer that the union of declared Cones covers every generated finite
typed Expression from successful per-Cone proofs, local `effectCoverage`, a
selected path family or a passing verification gate. State this missing global
guarantee in model handoffs alongside the actual certificate scope. Omitted
real-world Operations and requirements remain an author responsibility.

## Reviewer FAQ / defect triage

Before describing an ArchiScript limitation as a bug, consult the
[Reviewer FAQ in the repository README](../../README.md#reviewer-faq-recurring-semantic-and-scope-questions).
When this skill is installed independently of the repository, that relative
path may not exist. In that case, use the
[canonical README FAQ on GitHub](https://github.com/mrvanish97/archiscript/blob/main/README.md#reviewer-faq-recurring-semantic-and-scope-questions)
if network access is available. If neither source is accessible, apply the
self-contained rules below and do **not** claim to have read the FAQ.
Do not duplicate the complete FAQ inside this skill.

**Coproduct review restriction (manual; NOT AUTOMATICALLY VERIFIED):**
Use `Partition.coproduct` only for **a priori justified, tagged
alternatives** of a semantic carrier/VDP (e.g. a request carrying
`Sum Nat String`, or a response carrying
`Sum SuccessPayload ErrorPayload`), or to manipulate such **already
tagged** alternatives through legitimate injections, `copair`
or algebraic rewrites. At **every** coproduct occurrence, ask whether
the sum expresses predeclared possible *values*, or instead hides
a code-level logical OR between independently supplied Operations
or producer paths. **Never** turn two independent success/error
suppliers into one exclusive selected result merely by summing them;
coproduct does not construct a supplier join, mutual exclusion or
runtime choice. Identify the meaningful tags, the true boundary,
the source of the tag or the justified partial mapping, and any
external completeness assumption. The Lean 0.7.0 core proves
coproduct algebra and contains no supplier-sum constructor in
`Architecture.Inputs`, but **does not certify the architectural
intent of every coproduct use**. Check this manually; see the
[full FAQ with supported and invalid diagrams](../../README.md#can-a-coproduct-combine-two-independent-supplier-branches-into-one-alternative-response).

**Adversarial review anti-example — future knowledge is NOT required.**
Do not criticize `PossibilitySpace.lean` on the grounds that
"the program has not yet learned the future readiness time, so
`ShortWait | LongWait | Timeout` cannot be a valid VDP."
That is a **category error**: VDP members are semantic
Subdomains partitioning a declared *scenario carrier*, not
runtime classes that must be constructed, transmitted or
selected by a click handler at the event's beginning.
An `Operation : X → Y` maps **member indices**; it
does not claim that the deployed program can observe the
future, execute a wait, or guarantee eventual progress.
See the [dedicated FAQ and negative-review example](../../README.md#does-a-future-outcome-vdp-require-the-running-program-to-know-the-future)
and [the source example](../../ArchiScriptExamples/PossibilitySpace.lean).

**How to review this correctly:** distinguish (a) the
meaningful a priori partition, (b) which factors and
supplier occurrences are actually available to a
particular Operation/context, and (c) physical runtime
observability, liveness and implementation claims.
Challenge an omitted cancellation/error outcome,
unjustified scenario assumptions, falsely asserted
supplier availability or a purported model-to-code
theorem. Do not require the program to predict a
future scenario merely to permit a semantic partition.
State the precise Lean contract violated if claiming
a formal defect. This mistake is a negative
**reviewer reasoning example**, not a negative Lean
compilation test.

**Independent adversarial review test — semantic space vs. runtime.**
When evaluating any critic/agent claim that ArchiScript
cannot analyze waiting, random outcomes, disconnection,
timeouts or zone failures, decide the following *without
having to open README*:

1. Is the critic mistakenly treating the VDP's
   **selected semantic Subdomains** as concrete
   runtime messages/classes, or assuming the
   executing component must know the chosen
   member beforehand? If yes, reject that
   objection as a semantic/runtime category error.
2. Does the scenario require a genuine **additional
   independent supplier**, such as connectivity
   status from another Cause/Cone? If yes, declare
   and justify that source, then use a typed
   tensor in the consuming Operation and prove
   contextual P/E. Do not invent an unsolicited
   network polling loop or physical scheduler.
3. If a critic alleges hidden nondeterminism,
   ask for the actual contradictory
   `Operation.run` mapping, missing VDP
   coverage/disjointness, unjustified supplier
   reachability, inconsistent admitted tuple
   or false provenance. "Code cannot foresee
   the future" is not one of these violations.
4. Do not overcorrect: neither the mere VDP nor
   the tensor proves runtime delivery, latency,
   network liveness, exclusive commits, or that
   a real provider implements the declared
   boundary. Those are **distinct** obligations.

**Expected good answer** to the objection
"the handler cannot know future readiness or
a future network outage": "It need not. The
VDP partitions possible scenarios a priori.
If the architecture asserts a status supplier,
justify its Cause/provenance and the full
tensor compatibility. Do not confuse model
possibility with execution-time observation;
review missing cases or claimed runtime
guarantees separately." This is a **reviewer
reasoning test**, not a Lean compilation test.

**Do not conflate** (1) two target members for one source member of **one**
Operation, which is forbidden by `Operation.single_output`, (2) multiple
declared outgoing Operations, which are legal and non-exclusive, and
(3) derived joint Cone Effect tensors, which preserve simultaneous *semantic
tuple possibility* subject to `Reach` but assert **no physical simultaneous
execution or eventual launch**. A common boundary world is not a timestamp.
If a new review claims missing nondeterministic arrows, use the FAQ's explicit
`Waiting → Success / Timeout` counterexample and
[`HiddenWaitingBranch`](../../Test/Negative/HiddenWaitingBranch.lean).
Report mandatory invariant violations separately from optional global
coverage, manual inventory assumptions, real-world adequacy, and runtime
liveness. Cite the violated Lean contract before proposing a semantic change.

**A priori concurrency, shared-state feedback and cyclic tensors
(0.8.0 committed feature; NOT YET END-TO-END DEMONSTRATED):**
Do **not** require an architect to invent separate Causes,
multiple Cones, a physical clock or an external execution
simulator merely to analyze possible contender/resource states.
A planned pattern has **one Cause and one Cone**, a
`Request ⊗ State` tensor input, and a feedback route
which also produces the same declared State VDP.
The tensor's admissible joint members and the Cone's
Effect are semantic possibilities, not a scheduler.
Consult the [README's preserved ASCII diagram and
explanation](../../README.md#can-one-cone-analyze-conflicting-or-concurrent-resource-states-through-a-cyclic-tensor)
and [the 0.8.0 acceptance criteria](../../plans/0.8.0.md).

**Reviewer checklist for this pattern:** check that the
two uses of State are occurrences of a genuine
declared VDP, that the actual generator inventory and
any fan-out are explicit, and that the typed cycle
has one entry and justified auxiliary suppliers.
At **every** supported coherent cyclic tensor input,
including all finite unfoldings, verify full
`ReachInput = AdmInput` (E) and exact independent
incoming factor images / admissible tuple projections
(P). A selected VDP member is **not automatically**
an incoming member. Keep the precondition of
`CertifiedDeclaredArchitecture.input_partner`:
the relevant supplier image needs justified finite
Cause-rooted provenance and `InputSources`.
Do not demand a concrete initial State **value**
merely to state these universal relations; equally,
do not pretend a rootless feedback loop is grounded.

**Effect and implementation status:** the ASCII
diagram's `Decision VDP ⊗ State VDP` is a proposed
analytical Effect with terminal and typed cyclic
boundary roles, **not** an Effect that may be
chosen independently of the derived histories.
Require actual `effectCoverage`, `ConeValid`,
and Effect provenance/tuple proofs. The existing
`CyclicCone` and `CorrelatedJoin` regressions
prove their features **separately**: the combined
feedback-tensor one-Cone architecture has **not
yet been shown to compile and certify**. It may
work already; test this first. Project commitment:
deliver such certification in **0.8.0**, or retain
the committed feature in later versions until
the necessary verifier changes are complete.
Until then report **PLANNED / NOT YET VERIFIED**.

**Distributed-system / cross-Cone shared-VDP review (0.8.0
formal-foundations goal; NOT YET VERIFIED for this combined case):**
Do not treat the absence of an explicit clock, scheduler or trace
logic as a blanket inability to study distributed systems.
Different Cones can have distinct source/member images in the
**same declared State VDP** and those images can be compared
through explicitly justified tensor tuples, supplier provenance
and P/E. The images need not be equal, nor must the joint
relation be the full Cartesian product. This is an
*a priori* semantic question and does not require an
external temporal model by default. See the
[distributed-systems FAQ and two-Cone diagram](../../README.md#can-archiscript-analyze-distributed-system-conflicts-without-a-time-simulator).

Do **not** claim that equal VDP types automatically identify
a physical shared resource or that multiple producers
automatically merge writes. A tensor is not an implicit
state-update combiner or conflict resolver. Preserve
per-occurrence provenance, distinct ownership and
source image constraints; for an actual input Operation
require full contextual P/E, and for an Effect use the
correct derived coordinate/tuple semantics. The
N-Cone compositional account is an **open 0.8.0 research
commitment**, not a proved current capability; avoid
both overclaiming categorical completeness and falsely
demanding N hard-coded `Resolve` operations or a global
time simulator. Physical linearizability, atomicity and
runtime event order remain separate claims when asked.

**Separate runtime claim:** A VDP-level analysis
of conflicting states does **not** by itself prove
that physical workers overlap, run in any order,
acquire exclusive database locks, commit atomically
or satisfy liveness. These properties can be
modeled separately in Lean when required; such
external temporal/trace analysis is **optional**
for the a priori one-Cone semantic problem,
and is not supplied automatically by the 0.7.0
certificate.

## A priori semantic modeling / anti-hidden-branching

### Subdomains, selected members and logical refinement

Before evaluating an Operation or proposing a new semantic construct, keep
three distinct levels visible: (1) the complete declared carrier type,
(2) its named, inhabited and justified `Subdomain` regions (including
intermediate/supporting regions), and (3) the finite family of **selected**
Subdomains that form one `VDP` / `Partition`.

A selected VDP member is itself a `Subdomain`, indexed by `MemberIndex`;
it is not a new kind of entity assembled separately from regions. An
intermediate Subdomain need not itself be selected. Prove each declared
`SemanticSplit` locally; use `SemanticSplit.refine` to flatten justified
child splits and `Partition.ofSplit` when the root covers the full carrier.

Canonical interpretation: carrier `String`; `AllStrings` splits into
`Invalid` and `Valid`; `Valid` splits into `ValidAndPermitted` and
`ValidAndDenied`. One fine-grained VDP selects the three leaves as members,
**not** `Valid` alongside its children. A coarser VDP may instead select
`Invalid` and `Valid`, retaining the finer permission regions as supporting
Subdomains. A selected member need not be a leaf of the finest split, but
one VDP must not select overlapping ancestors and descendants. The carrier
stays `String` through either refinement, including invalid and empty strings;
other VDPs, such as an `Operation` target, may have different carriers.
For the fine-grained choice, the three selected predicates must cover every
string, be pairwise disjoint and each be inhabited. A permission distinction needs a
justified predicate over the carrier or an explicitly sourced dependency;
do not invent facts unavailable to a string-only input.

For a worked comparison of an a priori request classification, a separate
`Available/Unavailable` service-status supplier, and the resulting tensor
Operation, see the
[authorization-service FAQ](../../README.md#why-can-an-authorization-service-be-a-tensor-factor-if-the-requests-outcome-is-already-semantically-distinguished).
The service factor does not invent permissions; it must have its own
justifiable Cause/supplier and does not establish physical invocation.

This derivation is logical funneling, **not** a runtime validation pipeline.
Neither a global taxonomy nor a tree-shaped VDP is mandatory: flat
selections, independent trees, overlapping supporting Subdomains and
coarsening remain valid. See the [worked String example](../../README.md#from-subdomains-to-selected-vdp-members-a-string-carrier)
and [ProjectReference](../../ArchiScriptExamples/ProjectReference.lean).

When criticizing or editing a model, first inspect whether an apparent
ambiguous outcome reflects a missing **a priori semantic distinction**,
not a need for runtime simulation, value-level execution or a nondeterministic
arrow from one member of one Operation.

For each nontrivial model, complete this checklist before claiming its
downstream consequences. The [README explanation](../../README.md#a-priori-possibility-space)
and [worked examples](../../README.md#click-wait-and-timeout) explain the purpose:
make an omitted distinction an explicit modeling obligation instead of hiding
it in apparent implementation behavior.

1. Name one concrete external event per Cause, its sole starting VDP
   (`start c` / `object (start c)`) and its complete **meaningful** boundary
   carrier. Record external assumptions, unavailable information and unknown
   real-world completeness. Multiple consequences of that event do not create
   multiple initial VDPs or invocations. Information may also enter from
   explicitly declared external Causes, suppliers, context and later joins;
   do not require every fact in every Cone's first VDP.
2. State the outcome-relevant distinctions **before constructing arrows**.
   Define inhabited, disjoint, exhaustive member predicates over the honestly
   scoped carrier; do not back-fit it to convenient outcomes. A singleton
   `Click` cannot support three inhabited disjoint members. A declared scenario
   carrier can include readiness history/environment without asserting that
   the program predicts it. Possible PRNG/CSPRNG output classes require neither
   predictable samples nor probability weights; a VDP contains no distribution.
3. Check every source member of every Operation: at most one defined target
   **for that Operation**. Use `Operation.single_output` to diagnose a request
   for both `i → y₁` and `i → y₂` with unequal targets. Refine meaningful input
   semantics, add an explicitly sourced factor or justify context-specific
   semantics before asserting the map. Explain deliberate partiality: `none`
   is undefinedness, not a hidden alternative or runtime non-execution.
   Preserve genuine separate outgoing Operations as non-exclusive fan-out.
4. At every declared supported tensor use, identify each actual **producer
   occurrence**, its Cause, history, availability and shared-source correlation.
   Keep the full abstract Cartesian product. Independently derive each incoming
   image $I_i$ from its supplier **before** restricting the join. Independently
   author a full-tuple $\operatorname{Adm}_t$; prove **P**:
   $\forall i,\ \pi_i(\operatorname{Adm}_t)=I_i$, then **E**:
   $\operatorname{Reach}_t=\operatorname{Adm}_t$, or report the failed/unsupported
   obligations. P is necessary coverage, not sufficient joint behavior. Apply
   both to internal and cross-Cone joins, supported cyclic contexts and terminal
   Effects. **P/E is a statement about the complete supplier-input relation, not
   totality of the consuming Operation**: `g.run` may return `none` even for a
   reachable admitted tensor tuple. A missing factor must surface even when no complete input term can
   be built; never erase the declared use or define its images from accepted
   tuples. Do not set `Adm := Reach` or assume its proof through an unchecked axiom.
5. Diagnose in order: incoming members with no admissible full partner;
   invented incoming projections; $\operatorname{Reach}\setminus\operatorname{Adm}$
   (reachable but prohibited); $\operatorname{Adm}\setminus\operatorname{Reach}$
   (claimed realizable but impossible); n-ary correlations missed by pairwise
   checks. P may fail early; passing it never excuses skipping E. Use actual
   incoming images, not all nominal VDP members: a constant true-only supplier
   needs no partner for unreachable `false`.
6. Do not invent polling loops, scheduler steps, retries, synchronized copies
   or N parameterized Causes merely to mimic implementation waiting. Preserve
   a genuinely declared semantic cycle with its typed boundary. Coproduct OR
   cannot replace simultaneous tensor AND or conceal a missing semantic split.
   Distinct Causes may have equal initial VDPs and feed an explicit cross-Cone
   join. Two simulated invocations of the same Cause are outside the current
   single-event Cone API; a future external multiple-event composition feature
   must not be fabricated here.
7. Report **two separate verdicts**. Level A: the precise mathematical
   obligations proved for the declared local scope, including the API's
   inhabited/unreachable status obligations and named assumptions. P and E
   characterize a local formal contract defined with those obligations.
   Level B: external architectural assumptions and risks requiring human review.
   A valid declared model is necessary evidence, not sufficient proof of overall
   design correctness, completeness, security, performance, fairness or
   implementation conformance. Never infer future runtime knowledge, eventual
   timeout/liveness, or the deferred global generated-Expression guarantee.
   State **Global Cone/Expression coverage: NOT AUTOMATICALLY VERIFIED.**

For click/wait models, [PossibilitySpace.lean](../../ArchiScriptExamples/PossibilitySpace.lean)
proves a broad infinite scenario partition and functional decision map;
[HiddenWaitingBranch.lean](../../Test/Negative/HiddenWaitingBranch.lean) rejects
two distinct outputs from one Operation/source member. For joins, use
[CorrelatedJoin.lean](../../ArchiScriptExamples/CorrelatedJoin.lean),
[TensorVerification.lean](../../ArchiScriptTests/TensorVerification.lean) and
[CrossCone.lean](../../ArchiScriptExamples/CrossCone.lean) for diagonal,
orphan/parity and explicit external-supplier cases. Their current declarations
and [evaluation cases](references/evaluation-cases.md) are authoritative;
the possibility-space example alone is not an architecture certificate.

## Constructive study patterns: reuse the structure, verify the claim

These are **learning templates for agents**, not copied Lean definitions.
The diagrams show intended typed supplier paths; *only the cited
checked Lean examples* establish current certification. When adapting
one, first specify the carrier and member meanings, then the exact
generator inventory and sources, then contextual P/E, Effect
provenance and the certificate. Treat each occurrence independently
even when two paths use the same VDP. Do not take an ASCII arrow,
a nominal VDP equality or an illustrative tuple relation as proof.

### Pattern A — correlated fan-out and a verified tensor join (supported)

```text
             Cause -> Source VDP
                        |
                   +----+----+
                   |         |
                opLeft    opRight
                   |         |
                   v         v
                Left VDP   Right VDP
                   |         |
                   +----⊗----+
                        |
                  join Operation
                        |
                        v
                    Joined VDP
```

**Start from** [`CorrelatedJoin.lean`](../../ArchiScriptExamples/CorrelatedJoin.lean):
`diagonalCertified` has correlated `(false,false)`,
`(true,true)` inputs, while `constantCertified`
permits `(false,true)`, `(true,true)` because the
right supplier always produces `true`. The full
abstract `Bool ⊗ Bool` still has four index pairs;
`Reach=Adm` includes only actual, justified tuples.
**Adapt:** change the independent `rightMeaning` map,
update the authored admissibility relation and prove
projections (P), full tuple equality (E), root
histories and Effect. **Do not** set admissibility
equal to whatever reaches the join by definition.

### Pattern B — external input into another Cone (supported)

```text
  Cone A / Cause A                    Cone B / Cause B
        |                                   |
        v                                   v
     A VDP ----------------+             B VDP
     (owned by A)          |                |
                          +-------⊗--------+
                                  |
                           joined Operation
                           (owned by Cone B)
                                  |
                                  v
                               Result VDP
```

**Start from** [`CrossCone.lean`](../../ArchiScriptExamples/CrossCone.lean),
which certifies a cross-Cone tensor whose external A
factor has its own cyclic supplier history. One
Operation may consume both factors without claiming
that both Causes physically execute together.
**Adapt:** keep `owner`, distinct canonical roots,
supplier histories, the local input-factor requirement,
full `P/E` and separate Cone Effects correct.
This is a cross-Cone **dependency**, not a proof of
joint writes to one physical shared resource.

### Pattern B.1 — network and availability-zone failure as external Cone factors (illustration)

```text
  CONE Network            CONE Zone              CONE Request
  NetworkStatus VDP       ZoneStatus VDP         Request VDP
  Up / Degraded / Down    Healthy / Down         Valid / Invalid
            |                    |                    |
            +------------+-------+--------------------+
                         |
                         v
       Request VDP ⊗ NetworkStatus VDP ⊗ ZoneStatus VDP
                         |
              process Operation + exact P/E
                         |
                         v
                    Response / Effect
```

**Adapt Pattern B** to network disconnection,
provider outage, zone loss, service degradation or
another meaningful network-infrastructure scope.
A declared provider event, status-report event or
an appropriately justified scenario carrier may
source the relevant semantic distinctions. An
ISP's initialization event is **one possible
Cause, not a mandatory step**. Do not invent a
separate Cause for every hypothetical future failure.
These VDP members are **semantic regions**, not
runtime statuses that each component must receive
as message classes or know in advance.

If the generator genuinely consumes this three-factor
tensor, justify each supplied occurrence and Cause,
`RootCoherent`, `InputSources`, the derived
history/context and full tuple `Reach = Adm` (E),
plus exact projections of the independently incoming
images (P). Neither all Cartesian pairs nor independent
failure modes are guaranteed. E.g. a regional
network failure and AZ failure might be correlated:
an independently authored `Adm` cannot admit
a tuple with no possible joint source. Verify
the actual derived Effect rather than drawing
arbitrary terminal coordinates.

**Current evidence:** [`CrossCone.lean`](../../ArchiScriptExamples/CrossCone.lean)
is a certified example of external-Cone suppliers;
[`CorrelatedJoin.lean`](../../ArchiScriptExamples/CorrelatedJoin.lean)
tests a correlated tensor. **This particular
network/AZ model has not been compiled or certified**.
It proves neither runtime overlap nor time-based
network behavior, recovery, availability guarantees,
observation freshness or real-world infrastructure
conformance. The semantic problem needs no
time simulator; a physical timing/liveness claim
may need a separately justified temporal theory.
See the [corresponding FAQ](../../README.md#can-network-outages-or-availability-zone-failures-be-analyzed-without-a-network-simulator).

### Pattern C — own-State feedback through a tensor (0.8.0 planned)

```text
   ONE Cone / Cause
           |
        Request VDP
           |
           v
       Request ⊗ State VDP <------+ State VDP
           |                               ^
           v                               |
      Operation(s) --> Decision VDP        |
           |                               |
           +------> updated State VDP -----+
                                |
           Effect: terminal Decision
                  ⊗ typed cyclic State observation
```

This is the **planned** combination, **NOT YET
END-TO-END VERIFIED**. See the
[canonical full ASCII diagram and explanation](../../README.md#can-one-cone-analyze-conflicting-or-concurrent-resource-states-through-a-cyclic-tensor)
and [0.8.0 acceptance criteria](../../plans/0.8.0.md).
[`CyclicCone.lean`](../../ArchiScriptExamples/CyclicCone.lean)
proves cycles, and Pattern A proves tensors, **not their
combination here**. **Adapt/investigate:** add a
genuine typed `CycleBoundary`, explicit State supplier,
all finite coherent cyclic input contexts, independent
factor incoming images, P/E and derived terminal/cyclic
Effect coordinates. The diagram does not itself
provide a grounded State supplier; no particular
initial State *value* or external timeline is needed
merely to state the universal contracts.

### Pattern D — two or N Cones, same State VDP, different images (research)

```text
  Cone A -> State VDP          Cone B -> State VDP
            I_A                       I_B
         {Free,Locked}             {Locked,Done}
               |                       |
               +-----------⊗-----------+
                           |
                    joint tuples R
                 (P/E and provenance?)
```

**0.8.0 research / NOT YET VERIFIED as common shared
resource behavior.** `State VDP` is the same
declared *partition*; `I_A` and `I_B` are possibly
**different incoming member images** of distinct
producer occurrences. A candidate
`R = {(Free,Locked), (Locked,Done)}` covers both
projections but is **not established by the diagram**.
If a real input join is declared, prove its exact P/E;
if only an analytical Effect is claimed, prove its
derived coordinates and full relation. A tensor gives
a pair of values, not one merged State, a winning
writer or a shared physical storage identity.

**Scale by studying arbitrary finite N**, not by
creating a separate hard-coded N-way `Resolve`.
Pairwise feasibility is insufficient for global
feasibility: for three Bool-valued factors, all
three pairwise constraints `a ≠ b`, `b ≠ c`
and `a ≠ c` have individually satisfying pairs,
but **no common Boolean triple** satisfies all
three. A proposed N-way rule must retain full
joint consistency and supplier identities.
Consult the [cross-Cone research goal](../../plans/0.8.0.md)
and use Pattern B only as the *already checked*
external-source baseline, not as a proof of
shared-resource merging.

### Pattern E — coproduct as a tagged value, not competing producers (supported algebra)

```text
  Request VDP ⊗ ServiceStatus VDP
                 |
             Operation
                 |
                 v
       Response VDP (Sum Success Error)
              inl | inr
         one tagged result per defined source member

  NOT: independent Success producer --+
                                       +--> implicit "pick one"
       independent Error producer -----+
```

**Start from** [`Coproduct.lean`](../../ArchiScript/Coproduct.lean)
and the [coproduct FAQ](../../README.md#can-a-coproduct-combine-two-independent-supplier-branches-into-one-alternative-response).
A valid sum is the **carrier of one tagged semantic
value**, not a source-selection rule or an
`Architecture.Inputs` supplier join.
**Adapt:** justify tags and all relevant source
distinctions, then define member-level
`Operation.run : X.MemberIndex → Option Y.MemberIndex`
and prove the selected partition obligations.
The algebra is checked; whether a particular
tagging faithfully represents the external
boundary is a separate author-review obligation.

**Learning rule:** prefer a proven example as a
starting point, preserve its specific proof
obligations when changing `Node`, `owner`, `Cause`,
`Generator`, `context`, `admissibleInput` or
`effectAnalysis`, and label every new combination
of individually supported primitives **unproven**
until its own Lean certificate and negative
regressions pass. Never fill a missing guarantee
with an unchecked axiom, an invented Cause, an
implicit branch or an assumed join.

## Establish the semantics

1. Start from the complete meaningful carrier, retaining invalid, absent,
   unsupported and unsuccessful cases. A successful-leaf union cannot establish
   completeness of a broader input boundary. Carrier values may be infinite.
2. Declare `Subdomain` meanings and ancestry. Each named region requires an
   inhabitant. `Domain` expressions may be empty. Use `Subdomain.child` to retain
   parent restrictions and `Subdomain.remainder` for an explicitly based
   complement. Opaque predicates require an identified boundary and actual
   hypotheses; their names do not prove properties.
3. Prove every declared split with `SemanticSplit`. Siblings must cover their
   parent and be disjoint, with finite nonempty indices. Different trees may
   share a root and overlap across trees. Flat declarations and coarsening
   remain legitimate. `SemanticSplit.refine` proves flattened leaf coverage.
4. Construct `VDP` (the algebra also spells it `Partition`) from **selected**
   Subdomains with coverage and disjointness proofs over the unchanged carrier.
   Identify selected members separately from intermediate/supporting Subdomains;
   each selected member is a declared `Subdomain`. `Partition.ofSplit` reuses
   a split of the entire carrier. `Partition.closed` supports an independently
   justified finite closed carrier. `classify` is a derived classical lookup,
   not a construction field. A candidate lookup can help prove correspondence
   with independently authored meanings; its fibers cannot replace them.
5. Declare `Operation` maps between whole VDPs. Maps may be partial and
   non-surjective. `none` means undefinedness at that member, not runtime
   non-execution. Several outgoing Operations are non-exclusive structural
   routes, without any obligation that they execute.

The public-only [CurrentApi.lean](examples/CurrentApi.lean) constructs semantic
regions, a split, VDPs, an Operation, a linear route and a complete scoped
certificate. It runs the transitive proof audit.

## Declare consequences and prove their contracts

Use `ArchitectureSignature` for the closed primitive, Cause, node, domain and
split inventories. Generator identities and automatically derived histories
preserve occurrences even when nominal nodes, VDPs and member images coincide.
Each generator contains its actual typed `Inputs`; all factor suppliers must
be accounted for by the certificate's `inputSources` field. The signature's
`localFactor` proves an input/output ownership match, not that every input has
a supplier or a reachable value.

`Expression` is exclusively a finite linear chain over registered names and
nominal objects. Repetition through a cycle is permitted. Nonlinear algebraic
syntax is `Presentation`; its finite selected `Family` is a presentation aid,
never a Cone-completeness proof.

`ArchitectureSignature.Term` records finite supplier provenance. It is not a
single linear Expression or an implicit copying Operation. `Term.RootCoherent`
recursively requires each Cause leaf to use its own designated `origin`,
including nested external suppliers. `InCone c t` requires that coherence and
`t.hasRoot c (S.origin c)`. `isInputContext g t` checks the whole input plus a
local supplier in the output owner's Cone; `isInputContext_iff_coherent` derives
that supplier witness from the signature's ownership law. Use
`input_consequence_inCone` for the corresponding Operation result. Multiple
canonical producer paths and cross-Cone joins remain valid. Noncanonical roots
of any Cause are unsupported, even when the owning Cause alone is coherent.
Raw `Term` and `evaluate` can still express such roots; evaluation is no context
or Effect certificate. Equal VDPs, root labels or values do not merge sources.

Declare boundary and availability semantics in `DeclaredArchitecture`, followed
by independently authored `admissibleInput` and `admissibleEffect` contracts.
`incoming` is calculated from each upstream supplier before the current join's
restriction. `supplierImage` independently ranges over all coherent producers
of a node before a complete input exists. Prove mandatory `inputSources` for
**every generator**: `InputSources.grounded` supplies a coherent typed producer
at every factor position, or `.unreachable` proves all independent supplier
images empty at every position. `inputSources_of_catalog` reuses `effectCoverage`
and `SourcesPresent g` for grounding. An inhabited X image with missing Y cannot
use either alternative, regardless of whether a complete term can be built.

`InputValid` requires exact tuple agreement and every coordinate projection.
E means every reachable tuple must be admitted **and every admitted tuple must
be reachable**, including any impossible tuple mistakenly admitted by the author.
Check full n-ary relations; pairwise compatibility and P alone are insufficient.
The full tensor stays unchanged when Reach and Adm are proper subsets. Neither
an Expression nor a factor must reach all target members. In particular,
`InputValid` does not require `g.run` to be defined on every admitted tuple,
or every member of the full tensor; see the
[reviewer FAQ](../../README.md#does-a-verified-tensor-input-make-the-outgoing-operation-a-total-function).

The certificate's universal `inputs` still checks every full coherent context;
the grounding witnesses do not select or restrict those contexts.
`InputStatus.verified` also requires a reachable tuple. `.unreachable` requires
all actual `incoming t` images empty (`noSupplier`), no reachable tuple
(`noTuple`) and no admitted tuple (`noContract`). Report that status separately
from inhabited verification. `CertifiedDeclaredArchitecture.input_partner`
produces a supported full context and an Adm-and-Reach tuple containing each
member witnessed by an independent `supplierImage`. A bare unused product
receives no architectural verdict.

For the **planned one-Cone cyclic tensor input case**, do not
claim the existing universal P/E plus cycle machinery has been
proved sufficient until the
[0.8.0 end-to-end regression](../../plans/0.8.0.md)
passes; see the
[ASCII diagram in README](../../README.md#can-one-cone-analyze-conflicting-or-concurrent-resource-states-through-a-cyclic-tensor).

For cycles, supply a typed `Term.CycleBoundary` at the chosen observation point:
a real route with one typed entry hole and explicit auxiliary suppliers.
Repeated visits enlarge the boundary's image; they do not add tensor factors.
Reference semantics includes all finite derivations, including cross-Cone
recursive dependencies. It does not imply termination, eventual identity,
execution order or physical storage.

`effectNodes` finds boundary points; it does not enumerate complete coordinates.
Supply `effectAnalysis : ProvenanceAnalysis cyclicBoundary`, with explicit roots
and derived history entries. Certification requires `effectCoverage : Valid`:
`∀ c, S.origin c ∈ effectAnalysis.roots`, plus `Seeded`, `Closed`, `Realized`.
Do not require finiteness or enumeration of all `RootInstance` values;
`rootHistories` seeds only canonical origins even if other roots occur in the
candidate list. The finite normalized-history cache still needs closure.
Its soundness/completeness proofs cover every finite supported supplier derivation.
`effectCoordinates` pairs each boundary with each retained history; repeated C
positions are valid. `reachEffect` and `ConeValid` require
`Nonempty (model.effect c).Position`: an actual derived coordinate, not just a
nominal boundary name or the tensor unit's value. `ConeValid` also needs a
reachable full tuple, exact contract agreement and all upstream projections.

Supply `cones : ∀ c, model.ConeStatus c`. `.observable` carries `ConeValid`;
`.unobservable` carries `NoObservableEffect`: every `effectIncoming` image and
the entire Effect contract are empty. This can hold with structural positions
but no incoming values; it never claims reached unit success. `BoundariesComplete`
requires, for each owned node, that `NoObservableEffect` proof or a `Depends`
path to a derived boundary. `hasCone` proves the existence of a checked
`ConeStatus`, not necessarily an observable Cone. Neither unobservable status
nor an empty Effect cache bypasses `inputSources` or universal `inputs`.
`causeNonempty` is mandatory for `CertifiedDeclaredArchitecture`; an empty Cause
inventory cannot pass as a complete architecture.

A finite computation needs a complete enumeration of semantic configurations,
not merely finite VDP members. `Reachability.FiniteAnalysis.certify` returns an
exact result only after checking closure. `ExactAbstraction` must connect it to
the architectural relation. An unchanged terminal image is not a stopping test.
The provenance basis also needs canonical-origin coverage and closure of
normalized histories; finite VDP members do not imply that condition. If a model
cannot supply this basis, report the unsupported analysis scope and the outstanding obligation;
do not restrict the carrier, drop producer histories or claim certification.
The optional `derive_provenance([roots], fuel)` helper
(import `ArchiScript.Provenance.Derive`) caches candidate data only. Too little
fuel fails the required coverage proof; no domain claim or proof is generated.

## Verify and communicate

### Manual audit of the complete declared inventory

Perform this step during architecture construction and again before claiming
architecture-wide completeness. **Global Cone/Expression coverage: NOT AUTOMATICALLY VERIFIED.**
The limitation includes disconnected declared nodes, rootless SCCs and unused
subgraphs, not only generated paths.

1. Enumerate the complete declared `Cause`, `Node`/VDP and `Generator`/Operation
   inventories, including declarations absent from successfully constructed
   `Occurrence`s or walks starting at Causes. Identify nodes without a finite
   canonical Cause-rooted producer, unused/unconnected components and SCCs with
   no grounded incoming dependency. A cycle's arrows, nominal `owner`, typed
   cyclic marker or empty `supplierImage` do not prove rootedness.
2. Flag each unexplained declaration to the human architect. Ask whether it is
   an accidental leftover to remove, an intentional currently unreachable
   component whose purpose/exclusion must be documented, or an omitted
   Cause/dependency to repair. Record the architect's disposition and unresolved
   questions; do not silently approve it because Lean passes. After connecting
   a component, rerun source and contextual tensor proofs.
3. Report the audit as an **author judgment / manual review assumption**.
   Only the architect/diagram author can attest to the intended global inventory
   and coverage until a future checker exists. `CertifiedDeclaredArchitecture`,
   `InputSources.unreachable`, `NoObservableEffect`, `ConeStatus.unobservable`
   and `BoundariesComplete` do not jointly prove all declared nodes/SCCs grounded
   or every generated Expression covered.

The concrete example is `Cause → X` alongside isolated `Y ↔ E`:
[UngroundedCycle.certified](../../ArchiScriptTests/UngroundedCycle.lean) is an
accepted scoped certificate despite the rootless cycle and its typed marker;
[SourceCoverage.sourceOnly](../../ArchiScriptTests/SourceCoverage.lean) also
retains unrelated orphaned Y/E declarations. With no connecting dependencies or
context predicates, the component does not change unrelated rooted Expressions'
reachable tuples. Risks include overstated global assurance and possible
certificate refusal: for an observable Cone, `BoundariesComplete` checks every
owned node and an unrelated component may have no path to an Effect boundary.
A cyclic marker can satisfy that structural condition without proving production.

Keep this audit separate from strict local obligations: canonical root coherence,
mandatory `inputSources`, both P/E equations and honest Effect status still apply.
Incoming X with missing Y at a declared join must fail now. The
[0.8.0 plan](../../plans/0.8.0.md) separately tracks whole-inventory orphan/SCC
diagnostics and stronger all-generated-Expression/Cone coverage.

### Executable verification

```bash
uv run --no-project python scripts/verify-lean.py
```

This runs the pinned build, public smoke, transitive axiom audit, negative
fixtures and kernel replay. Reports under `.lake/reports` identify checked
sources and commands. The PR Gate CI job runs the same script and saves those
reports as `lean-proof-reports`, including on failure. Cite the checked revision
and report when communicating verification results.

Constructing `CertifiedDeclaredArchitecture` does not itself run the audit or
prove that a contract was independently authored. Run the gate before describing
a concrete model as audited. Builds treat warnings as errors. Audit rejects
direct or transitive `sorryAx`, unauthorized axioms and tagged conditional certificates.
Actual installed input/effect contracts of closed model and certificate
declarations in the checked imports are inspected regardless of tags, including
inline, indirect and opaque aliases. Include the concrete declarations in those
imports; an unimported model is outside that audit run.
Uninspectable closed records are rejected. Tags additionally check standalone
predicates and conditional results. The check conservatively follows transitive
implementation dependencies; it cannot establish independent business meaning.

Use **draft** for incomplete declarations, **conditional** for conclusions with
unsupplied assumptions, and **certified declared contexts** only for completed,
audited concrete certificates. Review approval is not a proof. State the global
coverage exception separately on every complete-model handoff.

## References by task

- Construction, fields and theorem names: [lean-api.md](references/lean-api.md).
- Algebraic reuse and normalization: [compositional-proofs.md](references/compositional-proofs.md).
- Compiler feedback and axiom checks: [proof-engineering.md](references/proof-engineering.md).
- Regression scenarios: [evaluation-cases.md](references/evaluation-cases.md).
- Human-facing views: [review-diagrams.md](references/review-diagrams.md).
- Optional legacy review tooling: [review-packs.md](references/review-packs.md).

Shared targets preserve distinct producer derivations automatically. One C
and one shared h;k declaration can yield two Effect coordinates of the same VDP;
equal members, images or suffixes do not merge those coordinates. Only an
explicit, fully supplied tensor-source Operation performs an architectural join.
The candidate Effect tensor is an analytical product, not that Operation.
`effectCoverage` checks a seeded, closed and realized finite provenance basis;
`EffectProvenance` prevents substituting a different producer in a coordinate.
Typed cyclic markers separately aggregate repeated traversals of their actual
return routes, while reference reachability retains every finite traversal.
