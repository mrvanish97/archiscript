# Contributing and merge policy

Changes to `main` should arrive through pull requests. The repository keeps the
merge policy in `.github/rulesets/default.json` and applies it with
`scripts/apply-default-ruleset.sh`.

A pull request is merge-ready only when all of the following are true:

- the branch is up to date with `main`;
- the required `pr-gate` status check passes;
- at least one approving review is present;
- the required code-owner review is present where GitHub can resolve a code owner;
- the change is merged with squash;
- the default branch is not deleted, force-pushed, or given non-linear history.

The `pr-gate` workflow runs the repository's executable checks:

```sh
lake build
bash scripts/check-negative.sh
lake env lean skills/archiscript/examples/CurrentApi.lean
python -m unittest discover -s scripts -p "test_*.py"
node --test examples/payment-webhook.test.mjs
```

These commands cover the public Lean libraries and examples, expected-failure
fixtures, the installed AI-skill API surface, repository scripts and merge-policy
tests, and the companion webhook implementation test.

The merge-policy tests intentionally check that the ruleset and workflow remain
in agreement. If a required command or status context changes, update
`.github/workflows/pr-gate.yml`, `.github/rulesets/default.json`, and
`scripts/test_merge_policy.py` together.

To apply the checked-in ruleset to the GitHub repository:

```sh
bash scripts/apply-default-ruleset.sh
```

or pass the repository explicitly:

```sh
bash scripts/apply-default-ruleset.sh OWNER/REPOSITORY
```

The script requires GitHub CLI access with permission to manage repository
rulesets. The JSON file is the version-controlled policy; GitHub's active
ruleset is the enforcement mechanism.
