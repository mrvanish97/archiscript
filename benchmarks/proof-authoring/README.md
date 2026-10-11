# Proof authoring benchmark (0.5.2)

This is a **measurement protocol**, not a speedup claim. The compiled
`ArchiScriptTests/ProofEngineering.lean` is a correctness regression and its
compilation time alone does not establish an improvement over 0.5.1.

## Fixed target

Start with the theorem `inventory_after_any_producer` in
`ArchiScriptTests/ProofEngineering.lean`, which lifts the existing checked
`inventoryEffect_factorizes` equality through an arbitrary producer. To
compare authoring strategies, preserve *exactly* that theorem statement,
implicitly bound parameters, hypotheses, imports, ArchiScript definitions, and
model revision. Keep the existing nonfactorization counterexample in the
correctness suite.

## Arms

- **A: Direct proof** — a manually constructed direct proof or explicit finite
  reasoning where feasible.
- **B: Unstructured AI** — produce a proof without the 0.5.2 proof-engineering
  instructions; keep model and theorem unchanged.
- **C: Local-first AI** — use the 0.5.2 skill and its compositional reference.

Archive each accepted proof source, the exact agent prompt/context, and the
number and durations of repair attempts. If A/B fails within its recorded
budget, report a failed arm; do not replace the goal with an easier one.

Do not manufacture an A or B proof by claiming it is AI-generated when it is
just a copy of the compositional proof. Use identical imports and cache policy
for Lean-time comparisons. For larger scaling experiments, introduce separate,
controlled synthetic goals and label them as such.

## Execution

1. Record commit SHA and `lean-toolchain`; capture OS, CPU, RAM, and test
   budget.
2. Prebuild unchanged imports with `lake build` and report build time
   separately. Run all arms with the same warmed or cold-cache policy.
3. For each arm, save a standalone `.lean` file containing the identical
   theorem statement and that arm's proof.
4. On Linux with GNU time, run:

   ```sh
   /usr/bin/time -v lake env lean path/to/arm.lean
   ```

   Record elapsed wall-clock time, maximum resident set size, exit status,
   and significant elaboration/profiling hotspots. Repeat with identical
   environment and report run-to-run variation. Use `trace.profiler` only
   after confirming support in the pinned Lean toolchain.
5. Track time from first AI attempt to **first kernel-accepted proof**
   separately from Lean checking time. Count repair attempts and meaningful
   local lemmas.
6. Run `lake build`,
   `bash scripts/check-negative.sh`, and
   `lake env lean skills/archiscript/examples/CurrentApi.lean`
   to confirm the unchanged regressions.

No fixed timing or RSS threshold belongs in standard CI; runner load and
caching can overwhelm small differences. A proof still must pass the kernel.
A result of "no improvement", "slower", "not tested", or "inconclusive" is
legitimate if the data supports it.

## Result record template

Store a record in `benchmarks/proof-authoring/results/` after actually running
a comparison. Include:

```text
Date / commit / toolchain / hardware:
Theorem (exact source digest and model revision):
Same proposition, hypotheses and imports checked?:
Prebuild time and cache policy:
A direct: success/failure, runs (seconds), peak RSS, attempts:
B unstructured AI: success/failure, runs, RSS, attempts:
C local-first AI: success/failure, runs, RSS, attempts:
Profiling or goal-shape observations:
Interpretation and limits:
```

As of the introduction of this protocol, **no A/B/C measurements are claimed**.
The new regression is a verified-shape test subject to Lean CI, not evidence of
measured acceleration.
