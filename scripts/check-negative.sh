#!/usr/bin/env bash
set -euo pipefail

for source in Test/Negative/*.lean; do
  output_file="$(mktemp)"
  if lake env lean "$source" >"$output_file" 2>&1; then
    echo "unexpected success: $source" >&2
    rm -f "$output_file"
    exit 1
  fi

  case "$source" in
    *ConflictingBranch.lean)
      expected="existingUserBranchWitness.target = RegistrationMemberIndex.created"
      ;;
    *ConflictingRouteSource.lean)
      expected="(operationRegistry.resolve OperationName.register).source = registrationPartition"
      ;;
    *UninhabitedMember.lean)
      expected="Two.left = Two.right"
      ;;
    *OverlappingMembers.lean)
      expected="formPartition.member i x ↔ overlappingRegions i x"
      ;;
    *IncompleteMembers.lean)
      expected="formPartition.member i x ↔ incompleteRegions i x"
      ;;
    *)
      echo "missing expected diagnostic for: $source" >&2
      rm -f "$output_file"
      exit 1
      ;;
  esac

  if ! grep -F "$expected" "$output_file" >/dev/null; then
    echo "wrong failure reason: $source" >&2
    sed -n '1,80p' "$output_file" >&2
    rm -f "$output_file"
    exit 1
  fi

  rm -f "$output_file"
  echo "expected failure: $source"
done
