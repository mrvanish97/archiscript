#!/usr/bin/env bash
set -euo pipefail

repository="${1:-}"

if [[ -z "$repository" ]]; then
  if gh repo view --json nameWithOwner >/dev/null 2>&1; then
    repository="$(gh repo view --json nameWithOwner --jq '.nameWithOwner')"
  else
    remote_url="$(git remote get-url origin 2>/dev/null || true)"
    if [[ -n "$remote_url" ]]; then
      case "$remote_url" in
        git@github.com:*) remote_path="${remote_url#git@github.com:}" ;;
        https://github.com/*) remote_path="${remote_url#https://github.com/}" ;;
        *) remote_path="" ;;
      esac
      remote_path="${remote_path%.git}"
      if [[ "$remote_path" =~ ^[^/]+/[^/]+$ ]]; then
        repository="$remote_path"
      fi
    fi
  fi
fi

if [[ -z "$repository" ]]; then
  echo "Usage: $0 [OWNER/REPOSITORY]" >&2
  exit 64
fi

ruleset_file="$(cd "$(dirname "$0")/.." && pwd)/.github/rulesets/default.json"
ruleset_id="$(gh api "repos/$repository/rulesets" --jq '.[] | select(.name == "Default") | .id' | head -n 1)"

if [[ -n "$ruleset_id" ]]; then
  gh api --method PUT "repos/$repository/rulesets/$ruleset_id" --input "$ruleset_file"
else
  gh api --method POST "repos/$repository/rulesets" --input "$ruleset_file"
fi
