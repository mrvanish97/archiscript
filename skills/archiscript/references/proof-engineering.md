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
every closed model/certificate, including untagged, indirect, inline and opaque
forms. It rejects uninspectable closed records. Negative audit fixtures construct
complete certificates and permit only `CONTRACT_AUDIT` errors, so an unrelated
missing proof cannot masquerade as enforcement. Source hashes reject a verification result if sources
change during the check. A textual search for missing-proof tokens is not a
substitute for the dependency audit.

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
