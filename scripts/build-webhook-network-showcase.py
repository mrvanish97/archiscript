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
    "ArchiScript/Operation.lean",
    "ArchiScript/Examples/PaymentWebhook.lean",
    "ArchiScript/Examples/PaymentWebhookNetwork.lean",
)


def revision():
    digest = hashlib.sha256()
    for name in MODEL_SOURCES:
        digest.update(name.encode())
        digest.update((ROOT / name).read_bytes())
    return digest.hexdigest()[:12]


def export_projection():
    subprocess.run(["lake", "build", "ArchiScript.Examples.PaymentWebhookNetwork"],
                   cwd=ROOT, check=True, capture_output=True, text=True)
    result = subprocess.run(
        ["lake", "env", "lean", "--run", "scripts/export-webhook-network.lean"],
        cwd=ROOT, check=True, capture_output=True, text=True)
    return json.loads(result.stdout)


def validate(projection, review):
    if projection["model"] != review["model"] or review["state"] != "draft":
        raise ValueError("showcase metadata must describe the draft exported model")
    partitions = {item["name"] for item in projection["partitions"]}
    if len(partitions) != len(projection["partitions"]) or len(partitions) > 8:
        raise ValueError("overview requires unique partitions within the eight-node budget")
    operations = projection["topology"]
    if len({item["id"] for item in operations}) != len(operations):
        raise ValueError("duplicate canonical operation identity")
    for item in operations:
        if item["source"] not in partitions or item["target"] not in partitions:
            raise ValueError(f"operation endpoint is not a selected VDP: {item['id']}")
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
    return [
        "flowchart LR",
        f'  A(["{path["source"]}"]) -->|"decide"| B(["{path["decision"]}"])',
        f'  B -->|"requestLedgerCommand"| C(["{ledger}"])',
        f'  B -->|"planResponse"| D(["{path["response"]}"])',
    ]


def mermaid_notification_map(projection):
    mappings = projection["notificationMappings"]
    targets = list(dict.fromkeys("∅" if item["target"] == "none" else item["target"]
                                 for item in mappings))
    lines = ["flowchart LR"]
    lines += [f'  S{index}(["{item["source"]}"])' for index, item in enumerate(mappings)]
    lines += [f'  T{index}(["{target}"])' for index, target in enumerate(targets)]
    target_ids = {target: f"T{index}" for index, target in enumerate(targets)}
    for index, item in enumerate(mappings):
        target = "∅" if item["target"] == "none" else item["target"]
        lines.append(f'  S{index} -->|"planNotification"| {target_ids[target]}')
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
              "- `ArchiScript/Examples/PaymentWebhookNetwork.lean`: new VDPs, operations, canonical registry, and path proofs",
              "- `ArchiScript/Examples/PaymentWebhook.lean`: input semantics and the base decision/ledger operations",
              "- `review/payment-webhook-network.review.json`: draft review questions and findings", ""]
    return "\n".join(lines)


def main():
    projection = export_projection()
    review = json.loads(REVIEW.read_text())
    validate(projection, review)
    model_revision = revision()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    snapshot = {"modelRevision": model_revision, "projection": projection, "review": review}
    (OUTPUT / "PaymentWebhookNetwork.snapshot.json").write_text(
        json.dumps(snapshot, indent=2) + "\n")
    (OUTPUT / "PaymentWebhookNetwork.md").write_text(
        markdown(projection, review, model_revision))
    print(f"Generated {OUTPUT / 'PaymentWebhookNetwork.md'} ({model_revision})")


if __name__ == "__main__":
    main()
