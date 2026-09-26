# ArchiScript: checked design before AI writes code

ArchiScript is a design layer between requirements written in natural language
and code produced by AI coding agents. Its current Lean library checks a model
of the input boundary, the semantic distinctions within it, and the operations
between those distinctions. That model gives agents and reviewers a shared
contract before implementation begins.

Coding agents can turn examples or happy paths into a convenient closed model,
silently excluding missing or malformed inputs, unsupported cases, or context
needed to distinguish outcomes.
The [authoring skill](skills/archiscript) guides the agent to state and justify
the carrier first. Lean then checks claims over that declared carrier. Neither
can prove that the chosen carrier includes every case the real system may
receive; that remains an explicit review obligation.

## A modeling error the checks expose

Imagine a form with an email field and a name field. An agent proposes two
states: `complete` (both filled) and `empty` (both blank). That sounds plausible
until someone submits only an email. That input has no stated meaning.

The [runnable FormInput model](ArchiScript/Examples/FormInput.lean) starts with
`String × String`, so all four presence combinations are in scope:

| Email | Name | Meaning |
| --- | --- | --- |
| blank | blank | both missing |
| filled | blank | name missing |
| blank | filled | email missing |
| filled | filled | complete |

It defines predicates for the meaningful regions and a partition that
classifies each input. The central check is `Partition.Realizes`: for **every**
input, does the classifier's answer agree with the independently stated meaning
of that member?

```lean
import ArchiScript.Examples.FormInput
open ArchiScript ArchiScript.Examples.FormInput

-- The four field-specific regions match the classifier.
example : fieldPartition.Realizes fieldRegions :=
  fieldPartition_realizes_regions
```

The [incomplete variant](Test/Negative/IncompleteMembers.lean) calls the second
member “both missing” while leaving the one-field-filled inputs out of its
stated regions. It cannot satisfy `Realizes`: `("a@example.test", "")` is
neither complete nor both missing. The [overlapping variant](Test/Negative/OverlappingMembers.lean)
also fails: “email provided” and “name provided” overlap when both are filled.
Run `bash scripts/check-negative.sh` to see Lean reject both obligations.

The model can then intentionally group all three incomplete cases into one
member for a consumer that only needs `complete` versus `incomplete`. Its
`forgetFieldFailures` operation maps the four detailed members to those two
members, and a theorem checks that this agrees with classifying the same raw
input at the coarser resolution:

| `fieldPartition` member | `forgetFieldFailures` → `formPartition` member |
| --- | --- |
| both missing | incomplete |
| name missing | incomplete |
| email missing | incomplete |
| complete | complete |

This operation maps **members**, not the input strings. It deliberately forgets
which field was missing.

For a single two-field form, ordinary code and tests may be enough. The example
shows ArchiScript's contract shape: named semantic regions, a partition, and a
member map between two resolutions. ArchiScript supplies this common vocabulary;
Lean checks the stated claims. The value grows when several agents or components
must agree on the same distinctions and routes before implementation.

## Where the member maps pay off: payment webhook retries

Suppose a payment provider sends a `success` webhook twice. The event payload
is identical, but the first delivery should queue fulfillment and the retry
should not. The decision therefore needs both the event and a ledger snapshot
answering whether its ID is already recorded. In the
[PaymentWebhook model](ArchiScript/Examples/PaymentWebhook.lean), the input
carrier contains the raw event ID, raw status, and that ledger observation.
The `inputPartition` selects five semantic members from this carrier.

```mermaid
flowchart LR
    A["Webhook input VDP<br/>event × ledger observation"] -->|decide| B["Decision VDP"]
    B -->|requestLedgerCommand| C["Ledger command VDP"]
```

The arrows are ArchiScript operations: partial maps between **VDP members**.
They are architectural contracts, not calls that read or write the ledger.
Here are all their member mappings:

| `inputPartition` member | `decide` → decision member | `requestLedgerCommand` → ledger command member |
| --- | --- | --- |
| malformed ID | reject | `none` |
| unsupported status | ignore | `none` |
| failed payment | record failure | record failure |
| first successful delivery | fulfill | record payment and queue fulfillment |
| duplicate successful delivery | acknowledge duplicate | `none` |

This is the useful check across components. The input regions are stated
separately from the classifier, so `inputPartition.Realizes inputRegions` must
hold for every combination of event and ledger observation. In particular,
`("p1", "success", false)` and `("p1", "success", true)` have the same event but
belong to different members. An event-only classifier cannot satisfy those
regions. Then operation composition checks the downstream contract:

```lean
import ArchiScript.Examples.PaymentWebhook
open ArchiScript.Examples.PaymentWebhook

example : inputPartition.Realizes inputRegions :=
  inputPartition_realizes_regions

example : (requestLedgerCommand.comp decide) .firstSuccess =
    some .recordAndQueueFulfillment := first_success_requests_fulfillment

example : (requestLedgerCommand.comp decide) .duplicateSuccess = none :=
  duplicate_requests_no_ledger_command
```

If a later edit maps duplicate delivery to `fulfill`, the second theorem fails.
If an operation is connected to a partition with the wrong source or target,
its composition does not type check. That is what ArchiScript adds here: one
explicit set of distinctions and member maps that several implementation
steps can be checked against. The author still has to justify the carrier:
Lean cannot discover a real-world input omitted from it. `none` means no
*modeled ledger command*; it does not prove the handler has no side effects.
Actually recording an ID and queueing fulfillment atomically requires a
separate effect contract and implementation.

## Mathematical foundation in brief

- **Subdomain $S \subseteq B$:** a semantic region of any value domain
  $B \subseteq \mathcal V$, where $\mathcal V$ is the ambient universe of values.
  $B$ need not be a VDP carrier. The foundation permits a defining formula or
  an opaque subdomain; the current Lean API uses a `Domain α` predicate.
  Supporting subdomains can overlap and need not cover their base. For
  $S \subseteq U$, the relative complement $U \setminus S$ names what remains
  inside $U$.
- **Carrier $C$:** the nonempty value domain selected for one VDP
  (`Partition.Carrier` in Lean). It may be infinite. The author must justify
  that it includes the real inputs that matter.
- **Value-domain partition (VDP):** a finite family $\mathcal M$ of nonempty,
  disjoint subdomains whose union is $C$. Equivalently, it classifies every
  $x \in C$ into exactly one member. Lean's `Partition` represents members by
  finite indices and defines each member as a classifier fiber.
  `Partition.Realizes` checks that those fibers match separately stated semantic
  regions. Supporting subdomains can be grouped into a member; they do not
  have to form a tree.
- **Operation $f : \mathcal M_X \rightharpoonup \mathcal M_Y$:** a partial map
  from members of one VDP to members of another (`Operation X Y` in Lean).
  `none` means undefined; `some failureMember` is a defined mapping to a
  modeled failure. An operation maps members, not carrier values or runtime
  effects.

Compatible operations compose: `g.comp f` follows $X \to Y \to Z$ and is
undefined if either mapping is undefined. The webhook example above uses this
to check the result of two member maps together.

This approach follows the sibling design's
[purpose](../archiscript-docs/chapter-1/init-ai-proposal.md),
[mathematical foundation](../archiscript-docs/chapter-1/stage-1/foundation.tex),
and [boundary design](../archiscript-docs/chapter-1/stage-2/scope.md).
Its TypeScript syntax and proposed product capabilities are not the Lean API.

## Lean core

This repository contains a deliberately small Lean 4 frontend/proof library.
The public entry point is `ArchiScript.lean`:

- `ArchiScript.Partition`: value-domain predicates, relative complements, finite
  partitions (VDPs), and correspondence with selected semantic regions;
- `ArchiScript.Operation`: partial member functions, composition laws, and typed
  branch witnesses;
- `ArchiScript.ParameterizedPartition`: finite member-indexed specialization
  and routing data (PVDPs);
- `ArchiScript.Examples.FormInput`: overlapping subdomains and four-to-two-member
  coarsening on the same raw input carrier;
- `ArchiScript.Examples.PaymentWebhook`: event-plus-ledger classification and
  composed member maps for first and duplicate deliveries;
- `ArchiScript.Examples.UserRegistration`: a compact model with named new-user
  and existing-user branches.

Build and check the examples with:

```sh
lake build
bash scripts/check-negative.sh
lake env lean skills/archiscript/examples/CurrentApi.lean
```

For registry identity, branch ownership, routed parameterization, and effect
contracts, see the [Lean API guide](skills/archiscript/references/lean-api.md).
The `UserRegistration` example illustrates these APIs; its no-creation theorem
depends on an explicit store-preservation premise.

## Current scope

Lean checks declared partitions, supplied region correspondence, member maps,
and typed paths. Carrier adequacy and implementation effects still require
authoring and review. The design's `unjustified-generalization` diagnostic is
review guidance here; this library does not emit it automatically. See the
[diagnostic guidance](skills/archiscript/references/lean-api.md#diagnostics).

The repository does not yet include a parser, runtime, UI, semantic linter,
observation knowledge model, or carrier-level executable operations.
Parameterized partitions support finite two-level specialization, not the
general recursive language of the original design.

## AI authoring skill

The self-contained [`skills/archiscript`](skills/archiscript) directory teaches
AI coding agents how to author and review ArchiScript models using the current
Lean API. It includes the [API guide](skills/archiscript/references/lean-api.md)
and [evaluation cases](skills/archiscript/references/evaluation-cases.md).

Install it locally by copying the complete directory into a supported skills
directory. This command refuses to overwrite an existing installation:

```sh
skill_target="${CODEX_HOME:-$HOME/.codex}/skills/archiscript"
if [ -e "$skill_target" ]; then
  echo "skill already exists: $skill_target" >&2
  exit 1
fi
mkdir -p "$(dirname "$skill_target")"
cp -R skills/archiscript "$skill_target"
```

Restart or reload the agent host if it only discovers skills at startup, then
request ArchiScript model authoring/review normally or invoke `$archiscript`
explicitly where supported. The installed skill has no runtime dependency on
this repository's sibling documentation or on tmux. Do not copy only
`SKILL.md`; its relative API and evaluation links expect the whole directory.

## License

This repository is licensed under the [Apache License 2.0](LICENSE).
For material owned by the project author, this grant also covers earlier
revisions of this repository, including commits created before `LICENSE` was
added.
