#!/usr/bin/env python3
"""Project the checked seven-VDP webhook model into focused review views."""

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "review/generated"
REVIEW = ROOT / "review/payment-webhook-network.review.json"
MODEL_SOURCES = (
    "ArchiScript/Partition.lean",
    "ArchiScript/Boundary.lean",
    "ArchiScript/Operation.lean",
    "ArchiScript/Operation/Declaration.lean",
    "ArchiScriptExamples/PaymentWebhook.lean",
    "ArchiScriptExamples/PaymentWebhookNetwork.lean",
)


def revision(projection, review):
    digest = hashlib.sha256()
    for name in MODEL_SOURCES:
        digest.update(name.encode())
        digest.update((ROOT / name).read_bytes())
    digest.update(json.dumps({"projection": projection, "review": review},
                             sort_keys=True, ensure_ascii=False,
                             separators=(",", ":")).encode())
    return digest.hexdigest()[:12]


def export_projection():
    subprocess.run(["lake", "build", "ArchiScriptExamples.PaymentWebhookNetwork"],
                   cwd=ROOT, check=True, capture_output=True, text=True)
    result = subprocess.run(
        ["lake", "env", "lean", "--run", "scripts/export-webhook-network.lean"],
        cwd=ROOT, check=True, capture_output=True, text=True)
    return json.loads(result.stdout)


def validate_carrier_origin(origin, partition_id):
    status = origin["status"]
    if status in {"trusted-external-root", "trusted-external-narrowing"}:
        if not all(origin.get(key) for key in ("source", "scope", "claim", "revision")):
            raise ValueError(f"incomplete external carrier guarantee: {partition_id}")
        if status == "trusted-external-narrowing":
            if "upstreamOrigin" not in origin:
                raise ValueError(f"external narrowing has no upstream origin: {partition_id}")
            validate_carrier_origin(origin["upstreamOrigin"], partition_id)
    elif status == "derived-contract":
        if not origin.get("upstream") or not origin.get("sourceMember"):
            raise ValueError(f"incomplete derived carrier contract: {partition_id}")
        if "upstreamProvenance" not in origin:
            raise ValueError(f"derived carrier has no upstream provenance: {partition_id}")
        validate_carrier_origin(origin["upstreamProvenance"], origin["upstream"])
    elif status == "declared-internal-output":
        if not origin.get("producer"):
            raise ValueError(f"internal output has no producer: {partition_id}")
        if "sourceOrigin" not in origin:
            raise ValueError(f"internal output has no source origin: {partition_id}")
        validate_carrier_origin(origin["sourceOrigin"], origin["producer"])
    else:
        raise ValueError(f"unrecognized carrier provenance: {partition_id}")


def validate_definition(definition, member_id):
    status = definition["status"]
    if status == "opaque":
        if not definition.get("reason"):
            raise ValueError(f"incomplete subdomain definition: {member_id}")
    elif status == "lean-predicate":
        return
    elif status in {"intersection", "union", "relative-complement"}:
        parts = definition.get("parts", [])
        if len(parts) != 2:
            raise ValueError(f"incomplete subdomain definition: {member_id}")
        for part in parts:
            validate_definition(part, member_id)
    else:
        raise ValueError(f"incomplete subdomain definition: {member_id}")


def opaque_reasons(definition):
    if definition["status"] == "opaque":
        return [definition["reason"]]
    return [reason for part in definition.get("parts", [])
            for reason in opaque_reasons(part)]


def validate(projection, review):
    if projection["model"] != review["model"] or review["state"] != "draft":
        raise ValueError("showcase metadata must describe the draft exported model")
    partitions = {item["name"] for item in projection["partitions"]}
    if len(partitions) != len(projection["partitions"]) or len(partitions) > 8:
        raise ValueError("overview requires unique partitions within the eight-node budget")
    semantic = projection["semanticPartitions"]
    if len(semantic) != len(partitions) or {item["id"] for item in semantic} != {
            item["id"] for item in projection["partitions"]}:
        raise ValueError("every reviewed partition needs semantic member evidence")
    for item in projection["partitions"]:
        entry = next(row for row in semantic if row["id"] == item["id"])
        expected = {f"{item['id']}.{member}" for member in item["members"]}
        if not entry["proof"] or len(entry["members"]) != len(expected) or set(entry["members"]) != expected:
            raise ValueError(f"incomplete semantic member evidence: {item['id']}")
    architectural = projection.get("architecturalPartitions", [])
    if (len(architectural) != len(partitions) or
            {item["id"] for item in architectural} != {item["id"] for item in projection["partitions"]}):
        raise ValueError("every reviewed partition needs carrier provenance")
    for item in architectural:
        validate_carrier_origin(item["carrierProvenance"], item["id"])
        partition = next(row for row in projection["partitions"] if row["id"] == item["id"])
        expected = {f"{item['id']}.{member}" for member in partition["members"]}
        if (len(item["members"]) != len(expected) or
                {member["id"] for member in item["members"]} != expected):
            raise ValueError(f"incomplete selected member definitions: {item['id']}")
        for member in [*item["members"], *item.get("supportingSubdomains", [])]:
            validate_definition(member["definition"], member["id"])
    operations = projection["topology"]
    if len({item["id"] for item in operations}) != len(operations):
        raise ValueError("duplicate canonical operation identity")
    for item in operations:
        if item["source"] not in partitions or item["target"] not in partitions:
            raise ValueError(f"operation endpoint is not a selected VDP: {item['id']}")
    coverage = projection["mappingCoverage"]
    operation_ids = {item["id"] for item in operations}
    if (len(coverage) != len(operation_ids) or
            {item["id"] for item in coverage} != operation_ids):
        raise ValueError("mapping coverage must name every exported operation once")
    missing = [item["id"] for item in coverage if item["missingDefinedMappings"]]
    if missing:
        raise ValueError(f"defined mappings lack named branches: {', '.join(missing)}")
    decision = next(item for item in projection["partitions"]
                    if item["name"] == "decisionPartition")
    if {item["source"] for item in projection["notificationMappings"]} != set(decision["members"]):
        raise ValueError("notification branch map omits a decision member")
    if projection["missingResponsibility"] or projection["missingImplementation"]:
        raise ValueError("declared branch metadata is incomplete")
    subjects = {item["id"] for item in projection["partitions"]}
    subjects.update(item["id"] for item in operations)
    subjects.update(item["id"] for item in projection["bindingRows"])
    for item in [*review["questions"], *review["findings"]]:
        if item["subject"] not in subjects:
            raise ValueError(f"unknown canonical review subject: {item['subject']}")


def mermaid_topology(projection, selected=None):
    operations = [item for item in projection["topology"]
                  if selected is None or item["source"] == selected or item["target"] == selected]
    names = list(dict.fromkeys(name for item in operations
                               for name in (item["source"], item["target"])))
    ids = {name: f"P{index}" for index, name in enumerate(names)}
    lines = ["flowchart LR"]
    lines += [f'  {ids[name]}["{name}"]' for name in names]
    lines += [f'  {ids[item["source"]]} -->|"{item["operation"]}'
              f'{" · partial" if item["partial"] else ""}"| {ids[item["target"]]}'
              for item in operations]
    return lines


def mermaid_duplicate_path(projection):
    path = projection["duplicatePath"]
    ledger = "∅" if path["ledger"] == "none" else path["ledger"]
    lines = [
        "flowchart LR",
        '  subgraph INPUT["inputPartition"]',
        f'    A["{path["source"]}"]',
        '  end',
        '  subgraph DECISION["decisionPartition"]',
        f'    B["{path["decision"]}"]',
        '  end',
        '  subgraph RESPONSE["responsePartition"]',
        f'    D["{path["response"]}"]',
        '  end',
    ]
    if ledger == "∅":
        lines.append('  C(["∅ · undefined"])')
    else:
        lines += ['  subgraph LEDGER["ledgerCommandPartition"]',
                  f'    C["{ledger}"]', '  end']
    lines += ['  A -->|"decide"| B',
              '  B -->|"requestLedgerCommand"| C',
              '  B -->|"planResponse"| D']
    return lines


def mermaid_notification_map(projection):
    mappings = projection["notificationMappings"]
    sources = list(dict.fromkeys(item["source"] for item in mappings))
    targets = list(dict.fromkeys(item["target"] for item in mappings
                                 if item["target"] != "none"))
    source_ids = {name: f"S{index}" for index, name in enumerate(sources)}
    target_ids = {name: f"T{index}" for index, name in enumerate(targets)}
    lines = ["flowchart LR"]
    lines += ['  subgraph DECISION["decisionPartition"]', '    direction TB']
    lines += [f'    {source_ids[name]}["{name}"]' for name in sources]
    lines += ['  end', '  subgraph NOTIFICATION["notificationPartition"]', '    direction TB']
    lines += [f'    {target_ids[name]}["{name}"]' for name in targets]
    lines += ['  end']
    if any(item["target"] == "none" for item in mappings):
        lines.append('  U(["∅ · undefined"])')
    for item in mappings:
        target = "U" if item["target"] == "none" else target_ids[item["target"]]
        lines.append(f'  {source_ids[item["source"]]} -->|"planNotification"| {target}')
    return lines


def diagram(lines):
    return ["```mermaid", *lines, "```", ""]


def source_label(implementation):
    status = implementation["status"]
    if status not in {"resolved", "planned"}:
        return status
    symbol = implementation["symbol"]
    return f"{implementation['repository']}:{implementation['path']}#{symbol} ({status})"


def markdown(projection, review, model_revision):
    lines = [
        "# PaymentWebhookNetwork: one model, several review views", "",
        f"Model revision: `{model_revision}`", "",
        f"Review state: **{review['state']}** · implementation gate: **CLOSED**", "",
        f"Named branch handoff: **COMPLETE** across {len(projection['mappingCoverage'])} registered operations.", "",
        review["scope"], "",
        "These are read-only projections of the Lean model. Arrows map semantic members; they are not runtime calls.", "",
        "## Level 1 · Entire operation topology", "",
        "**Question:** Which VDPs connect? **Hidden:** member mappings, effects, and code sites.", "",
        *diagram(mermaid_topology(projection)),
        "Seven VDPs and six operations fit the overview budget. The four outputs of `decisionPartition` are distinct review obligations, not execution stages.", "",
        "## Level 1 · Decision neighborhood", "",
        "**Question:** What enters and leaves `decisionPartition`? **Hidden:** the downstream fulfillment branch and unrelated member detail.", "",
        *diagram(mermaid_topology(projection, "decisionPartition")),
        "## Focused composition · Duplicate delivery", "",
        "**Question:** How can the duplicate receive a provider response without a ledger command? **Hidden:** audit intent, notification intent, other branches, and runtime effects.", "",
        *diagram(mermaid_duplicate_path(projection)),
        "`∅` means `requestLedgerCommand` is undefined for `acknowledgeDuplicate`. It does not prove absence of other runtime effects.", "",
        "## Level 2 · Complete notification branch map", "",
        "**Question:** Which decisions request customer notification? **Hidden:** other operations and code effects.", "",
        *diagram(mermaid_notification_map(projection)),
        "| Decision member | Notification intent |", "| --- | --- |",
    ]
    for item in projection["notificationMappings"]:
        target = "∅" if item["target"] == "none" else f"`{item['target']}`"
        lines.append(f"| `{item['source']}` | {target} |")
    lines += ["", "## Level 3 · Input partition under review", "",
              "The carrier is the same event-plus-ledger-observation boundary as the base PaymentWebhook model.", "",
              "| Selected member | Review description |", "| --- | --- |"]
    for item in projection["inputRegions"]:
        lines.append(f"| `{item['id']}` | {item['description']} |")
    lines += ["", "Every selected VDP carries semantic member evidence:", ""]
    lines += [f"- `{item['id']}` — `{item['proof']}`"
              for item in projection["semanticPartitions"]]
    lines += ["", "**Carrier provenance**", "",
              "| Partition | Origin | Declared source |", "| --- | --- | --- |"]
    for item in projection["architecturalPartitions"]:
        origin = item["carrierProvenance"]
        lines.append(f"| `{item['id']}` | `{origin['status']}` | {origin.get('source', origin.get('producer', ''))}; closure={item.get('carrierClosure', False)} |")
    opaque = [(member["id"], reason)
              for item in projection["architecturalPartitions"]
              for member in [*item["members"], *item.get("supportingSubdomains", [])]
              for reason in opaque_reasons(member["definition"])]
    lines += ["", "**Opaque subdomains:** " + ("; ".join(
        f"`{name}` — {reason}" for name, reason in opaque) or "none") + ".", "",
              "Opaque means no defining formula is available for deduction. External roots are trusted claims, not Lean proofs of their source."]
    lines += ["", "The descriptions sit beside independent Lean predicates. Lean checks predicate/classifier correspondence, not the English wording or the adequacy of the chosen boundary.", "",
              "## Level 4 · Branch-to-code handoff", "",
              "| Canonical branch | Responsibility | Primary implementation |", "| --- | --- | --- |"]
    for item in projection["bindingRows"]:
        lines.append(f"| `{item['id']}` | {', '.join(item['responsibility'])} | `{source_label(item['implementation'])}` |")
    lines += ["", "The base `decide` binding is resolved in companion code. New output-plan bindings are planned paths; those files do not exist yet. Neither state proves code conformance.", "",
              "## Checked claims and review findings", "",
              "**PROVED over the declared model**", ""]
    lines += [f"- {item['claim']} — `{item['proof']}`" for item in projection["checkedClaims"]]
    lines += ["", "**UNKNOWN / OPEN**", ""]
    lines += [f"- `{item['subject']}`: {item['question']}" for item in review["questions"]]
    lines += ["", "| Finding | Subject | Concern | Status |", "| --- | --- | --- | --- |"]
    for item in review["findings"]:
        lines.append(f"| `{item['id']}` | `{item['subject']}` | {item['concern']} | {item['disposition']} |")
    lines += ["", "The output VDPs describe plans. The model does not establish that any HTTP response, audit record, notification, ledger write, or queue publication occurs atomically or at all.", "",
              "## Source anchors", "",
              "- `ArchiScriptExamples/PaymentWebhookNetwork.lean`: new VDPs, operations, canonical registry, and path proofs",
              "- `ArchiScriptExamples/PaymentWebhook.lean`: input semantics and the base decision/ledger operations",
              "- `review/payment-webhook-network.review.json`: draft review questions and findings", ""]
    return "\n".join(lines)


def main():
    projection = export_projection()
    review = json.loads(REVIEW.read_text())
    validate(projection, review)
    model_revision = revision(projection, review)
    OUTPUT.mkdir(parents=True, exist_ok=True)
    snapshot = {"modelRevision": model_revision, "projection": projection, "review": review}
    (OUTPUT / "PaymentWebhookNetwork.snapshot.json").write_text(
        json.dumps(snapshot, indent=2) + "\n")
    (OUTPUT / "PaymentWebhookNetwork.md").write_text(
        markdown(projection, review, model_revision))
    print(f"Generated {OUTPUT / 'PaymentWebhookNetwork.md'} ({model_revision})")


if __name__ == "__main__":
    main()
