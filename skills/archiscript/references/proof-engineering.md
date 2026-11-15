# Proof engineering and feedback

The standard gate starts with `lake clean` and rebuilds the source graph.
This prevents removed modules' stale `.olean` files from entering kernel replay.

Missing proof fields are real errors. Repair the declaration or prove the
unchanged obligation; do not add an axiom, narrow a carrier or discard tuples.

For an inherited predicate, start with its parent containment or defining
conjunction. For a split, prove coverage and sibling disjointness independently.
For full tensor tuples, use the complete dependent coordinate type, not just
pairwise projections. `Operation.single_output` exposes a missing source
refinement when one source member is claimed to have incompatible outputs.

Use `change` or controlled `dsimp` to expose a local goal before deciding a
finite proposition. Simple `rfl` and constructor equality are legitimate for
closed data. `Partition.classify` is classical; a runtime `#guard` cannot execute
it. Prove correspondence with `self_member` or use a separately proved,
computable lookup.

In dependent signatures, annotate an occurrence constructor with
`(S := signature)` when Lean cannot infer its actual source graph from a
semantic VDP. Transparent `abbrev` declarations can make a fixed signature's
index types visible without changing the mathematics. Never replace a missing
factor with an arbitrary value merely to make elaboration succeed.

For recursion through indexed provenance terms, formulate an invariant over
arbitrary source structure, then specialize it. This preserves the full
inductive hypothesis and avoids inventing a finite history bound. A typed
`Term.CycleBoundary` records one entry hole and a nontrivial return; it is not
a claim that the cycle halts.

## Coherence, suppliers and explicit statuses

Prove `Term.RootCoherent` for the whole supplier tree. Every Cause leaf must
use its own `origin`, including leaves inside another Cone's producer. Several
paths from one canonical root and joins from distinct Causes remain valid.
Use `isInputContext_iff_coherent` to obtain the local ownership witness and
`input_consequence_inCone` for its output; an owner-only `onlyLocalRoot` guard
does not check external Causes. Raw evaluation of a mixed-root term is still
possible and supplies no context proof. The
[root regressions](../../../ArchiScriptTests/RootCoherence.lean) demonstrate
both supported cases and the nested failure.

Discharge the certificate's two input fields separately:

1. For **every declared generator**, prove `inputSources` using
   `InputSources.grounded` with coherent suppliers at every position, or
   `InputSources.unreachable` with empty independent `supplierImage`s at every
   position. These images range over coherent upstream producers before any
   complete join input exists. `inputSources_of_catalog` can reuse a valid
   cache and `SourcesPresent g`; a missing catalog factor is not itself proof
   that all incoming images are empty.
2. For **every full coherent input context**, prove `inputs` with
   `InputStatus.verified` (P, E and a reachable tuple) or `.unreachable`.
   The latter needs all three proofs: `noSupplier` for every actual `incoming t`
   image, `noTuple`, and `noContract`. Grounding witnesses never limit this
   universal quantification to favorable producer choices.

The [missing-source regression](../../../ArchiScriptTests/SourceCoverage.lean)
proves that X present / Y absent cannot supply either `InputSources` alternative,
even though no complete input can be built. On a completed certificate,
`input_partner` constructs a supported full context and an Adm-and-Reach partner
for each independently incoming member; do not weaken this to a single
compatible tuple or define images from the join's accepted tuples.

For each Cause, supply `ConeStatus.observable` with `ConeValid`, or
`.unobservable` with `NoObservableEffect`. Observable validity needs a witness
of `Nonempty (model.effect c).Position`, a reachable tuple, exactness and all
projections. Nominal `effectNodes ≠ []` or the unit's inhabitant does not prove
there is an actual observation position. Unobservable status needs every
`effectIncoming` image empty and the entire Effect contract empty, even if
there are structural positions. `BoundariesComplete` then takes the
`NoObservableEffect` branch or supplies the required boundary path for each
owned node. `hasCone` yields a checked status, not necessarily observability.

The [unobservable fixture](../../../ArchiScriptTests/Unobservable.lean) has
structural suppliers with no incoming values. The
[ungrounded cycle](../../../ArchiScriptTests/UngroundedCycle.lean) proves that
circular arrows alone produce no finite coherent supplier. Keep both distinct
from a missing-partner fault with an inhabited incoming image.

For a provenance cache, prove `∀ c, S.origin c ∈ analysis.roots` and its
`Seeded`, `Closed`, `Realized` checks. Do not enumerate every raw `RootInstance`
value: `rootHistories` filters to canonical origins. Finite VDP members still
do not prove a finite closed normalized-history basis.

## Release checks

```bash
uv run --no-project python scripts/verify-lean.py
```

The runner builds first, checks the public smoke, audits compiled transitive
axioms, runs intended-diagnostic negative fixtures, and invokes `leanchecker`
with explicit module names. The explicit names matter: the tool's default
capitalization of the package name does not spell `ArchiScript` correctly.

`#audit_archiscript` emits declaration types and axiom dependencies. It rejects
`sorryAx` transitively, custom axioms, extra trusted-computation axioms, tagged
certificates with unsupplied parameters and standalone tagged contracts
referencing Reach. It also exposes the actual installed admissibility fields of
closed model/certificate declarations in the checked imports, including untagged,
indirect, inline and opaque forms. It rejects uninspectable closed records.
The certificate constructor does not run this check. Import the concrete model
and certificate in the audited entry point; a conditional factory alone does not
audit every possible instantiation, and declarations outside the import closure
are not inspected. Negative audit fixtures construct
complete certificates and permit only `CONTRACT_AUDIT` errors, so an unrelated
missing proof cannot masquerade as enforcement. Source hashes reject a verification result if sources
change during the check. A textual search for missing-proof tokens is not a
substitute for the dependency audit.

The runner writes command logs, `verification.json` and `axioms.json` under
`.lake/reports/`. The [PR Gate workflow](../../../.github/workflows/pr-gate.yml)
runs the same script and uploads that directory as `lean-proof-reports`, including
on failure. Use the report's checked commit, source digest and actual command
results when reporting verification; a successful build alone omits these checks.

Named external semantic predicates can remain conditional. A theorem with a
hypothesis is a valid conditional theorem; it is not a closed concrete
certificate until the hypothesis is supplied. Independent contract authorship
and real-world adequacy remain external judgments even when an audit passes.

For shared-target histories, keep one graph and derive candidate data with
`derive_provenance`; never clone nodes to make a proof succeed. Prove `Valid`
for that candidate, rather than accepting a fuel bound or unchanged image as
closure. `Term.history_injective` and `Expression.supply_preserves_provenance`
provide structural proofs independently of member equality. The helper produces
no theorem; every certificate still supplies kernel-checked evidence.
