#!/usr/bin/env python3
"""Build a human review snapshot from the checked PaymentWebhook Lean model."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
MODEL_SOURCES = (
    "ArchiScript/Partition.lean",
    "ArchiScript/Operation.lean",
    "ArchiScript/Examples/PaymentWebhook.lean",
)
REVIEW_SOURCE = ROOT / "review/payment-webhook.review.json"
OUTPUT = ROOT / "review/generated"


def model_revision():
    digest = hashlib.sha256()
    for name in MODEL_SOURCES:
        digest.update(name.encode())
        digest.update((ROOT / name).read_bytes())
    return digest.hexdigest()[:12]


def projection_from_lean():
    result = subprocess.run(
        ["lake", "env", "lean", "--run", "scripts/export-payment-review.lean"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    return json.loads(result.stdout)


def validate_review(projection, review):
    if review.get("model") != projection["model"]:
        raise ValueError("review metadata names a different model")
    objects = {entry["id"] for entry in projection["objects"]}
    if len(objects) != len(projection["objects"]):
        raise ValueError("projection contains duplicate canonical IDs")
    for item in [review["boundary"], *review["assumptions"],
                 *review["effectNotes"], *review["questions"], *review["findings"]]:
        if item["subject"] not in objects:
            raise ValueError(f"unknown review subject: {item['subject']}")
    finding_ids = [item["id"] for item in review["findings"]]
    if len(finding_ids) != len(set(finding_ids)):
        raise ValueError("duplicate finding ID")
    if review["state"] not in {
        "draft", "ready-for-review", "changes-requested", "approved", "superseded"
    }:
        raise ValueError("invalid review state")
    if any(item["disposition"] not in {"open", "addressed", "accepted"}
           for item in review["findings"]):
        raise ValueError("invalid finding disposition")


def approval_status(review, revision):
    approval = review.get("approval")
    return bool(
        review["state"] == "approved"
        and isinstance(approval, dict)
        and approval.get("reviewer")
        and approval.get("revision") == revision
        and not any(item["disposition"] == "open" for item in review["findings"])
    )


def source_label(source):
    label = f"{source['repository']}:{source['path']}"
    if source["symbol"]:
        label += f"#{source['symbol']}"
    return label


def primary_label(implementation):
    binding = implementation.get("binding")
    if binding:
        return source_label(binding["primary"])
    return implementation.get("reason", "none")


def operation_owners(projection):
    branches = [*projection["decideBranches"], *projection["ledgerBranches"]]
    return [(operation["id"], sorted({owner for item in branches
                                      if item["id"].startswith(operation["id"] + ".")
                                      for owner in item["responsibility"]}))
            for operation in projection["topology"]]


def mermaid_topology(projection):
    names = list(dict.fromkeys(
        name for operation in projection["topology"]
        for name in (operation["source"], operation["target"])))
    nodes = {name: f"P{index}" for index, name in enumerate(names)}
    return [f'  {nodes[operation["source"]]}["{operation["source"]}"] -->|"'
            f'{operation["operation"]}{" · partial" if operation["partial"] else ""}"| '
            f'{nodes[operation["target"]]}["{operation["target"]}"]'
            for operation in projection["topology"]]


def latex_topology(projection):
    operations = projection["topology"]
    if not operations:
        return "No operations exported."
    parts = [r"\fbox{" + tex_escape(operations[0]["source"]) + "}"]
    for operation in operations:
        parts.append(r"\quad $\stackrel{\mathrm{" + tex_escape(operation["operation"])
                     + r"}}{\longrightarrow}$\quad " +
                     r"\fbox{" + tex_escape(operation["target"]) + "}")
    return r"\begin{center}" + "".join(parts) + r"\end{center}"


def semantic_changes(current, previous, current_review=None, previous_review=None):
    if previous is None:
        return ["First generated snapshot; no earlier projection supplied."]
    changes = []
    for key in ("inputMembers", "decisionMembers", "ledgerMembers"):
        added = sorted(set(current[key]) - set(previous.get(key, [])))
        removed = sorted(set(previous.get(key, [])) - set(current[key]))
        if added:
            changes.append(f"Added {key}: {', '.join(added)}")
        if removed:
            changes.append(f"Removed {key}: {', '.join(removed)}")
    old_regions = {item["id"]: item["description"] for item in previous.get("inputRegions", [])}
    for item in current["inputRegions"]:
        if item["id"] in old_regions and old_regions[item["id"]] != item["description"]:
            changes.append(f"Review meaning changed for {item['id']}: {old_regions[item['id']]} → {item['description']}")
    for key in ("decideBranches", "ledgerBranches"):
        old = {item["id"]: item for item in previous.get(key, [])}
        new = {item["id"]: item for item in current[key]}
        for branch_id in sorted(old.keys() | new.keys()):
            if branch_id not in old:
                changes.append(f"Added branch {branch_id}: {new[branch_id]['source']} → {new[branch_id]['target']}")
            elif branch_id not in new:
                changes.append(f"Removed branch {branch_id}")
            else:
                before, after = old[branch_id], new[branch_id]
                for field in ("source", "target", "responsibility"):
                    if before[field] != after[field]:
                        changes.append(f"{branch_id} {field}: {before[field]} → {after[field]}")
                old_binding = (before["implementation"]["status"], primary_label(before["implementation"]))
                new_binding = (after["implementation"]["status"], primary_label(after["implementation"]))
                if old_binding != new_binding:
                    changes.append(f"{branch_id} implementation: {old_binding} → {new_binding}")
    old_maps = {item["source"]: item["target"] for item in previous.get("ledgerMappings", [])}
    for item in current["ledgerMappings"]:
        if item["source"] in old_maps and old_maps[item["source"]] != item["target"]:
            changes.append(f"requestLedgerCommand({item['source']}): {old_maps[item['source']]} → {item['target']}")
    old_topology = {item["id"]: item for item in previous.get("topology", [])}
    for item in current.get("topology", []):
        if item["id"] in old_topology and item != old_topology[item["id"]]:
            changes.append(f"Operation topology changed: {item['id']}")
    if current_review is not None and previous_review is not None:
        if current_review["boundary"] != previous_review.get("boundary"):
            changes.append("Boundary description or challenge changed")
        for key, field in (("assumptions", "statement"), ("effectNotes", "statement"),
                           ("questions", "question")):
            old_items = {(item["subject"], item[field]) for item in previous_review.get(key, [])}
            new_items = {(item["subject"], item[field]) for item in current_review[key]}
            for subject, value in sorted(new_items - old_items):
                changes.append(f"Added or revised {key} on {subject}: {value}")
            for subject, value in sorted(old_items - new_items):
                changes.append(f"Removed or revised {key} on {subject}: {value}")
        old_findings = {item["id"]: item for item in previous_review.get("findings", [])}
        new_findings = {item["id"]: item for item in current_review["findings"]}
        for finding_id in sorted(old_findings.keys() | new_findings.keys()):
            if finding_id not in old_findings:
                changes.append(f"New review finding {finding_id}: {new_findings[finding_id]['concern']}")
            elif finding_id not in new_findings:
                changes.append(f"Removed review finding {finding_id}")
            elif old_findings[finding_id]["disposition"] != new_findings[finding_id]["disposition"]:
                changes.append(f"Finding {finding_id}: {old_findings[finding_id]['disposition']} → {new_findings[finding_id]['disposition']}")
    return changes or ["No semantic changes detected in the exported projection."]


def markdown_pack(projection, review, revision, changes, allowed):
    lines = [
        "# PaymentWebhook engineering review pack", "",
        f"Model revision: `{revision}`", "",
        f"Review state: **{review['state']}**", "",
        f"Implementation gate: **{'OPEN' if allowed else 'CLOSED'}**", "",
        "This is a generated snapshot. Semantic mappings, members, responsibility, and code bindings come from Lean; review notes and findings come from structured review metadata. Approval belongs to the model revision above.", "",
        "## Fast pass", "",
        "### 1. Scope and direction", "", review["scope"], "",
        "### 2. Changes since previous review", "",
        *[f"- {change}" for change in changes], "",
        "### 3. Boundary to challenge", "",
        f"**{review['boundary']['subject']}** — {review['boundary']['description']}", "",
        f"**Review challenge:** {review['boundary']['challenge']}", "",
        "### 4. Operation topology", "",
        "View: Level 1 — operation topology. Focus: input, decision, and ledger-command VDPs. Hidden: individual members, effects, and proofs.", "",
        "```mermaid", "flowchart LR",
        *mermaid_topology(projection),
        "```", "",
        "The arrows are semantic member mappings, not runtime calls.", "",
        "**Operation responsibility**", "",
        *[f"- `{operation}`: {', '.join(owners) or 'unassigned'}"
          for operation, owners in operation_owners(projection)], "",
        "### 5. Major assumptions and open questions", "",
        *[f"- **{item['subject']}**: {item['statement']}" for item in review["assumptions"]], "",
        *[f"- **{item['subject']}**: {item['question']}" for item in review["questions"]], "",
        "## Deep pass", "",
        "### 6. Semantic partitions", "",
        f"- `PaymentWebhook.inputPartition`: {', '.join(f'`{x}`' for x in projection['inputMembers'])}",
        f"- `PaymentWebhook.decisionPartition`: {', '.join(f'`{x}`' for x in projection['decisionMembers'])}",
        f"- `PaymentWebhook.ledgerCommandPartition`: {', '.join(f'`{x}`' for x in projection['ledgerMembers'])}", "",
        "The input carrier includes `alreadyRecorded`; the model does not establish how that observation was acquired.", "",
        "Coarsening: none represented in this scoped review projection.", "",
        "| Input member | Review meaning |", "| --- | --- |",
        *[f"| `{item['name']}` | {item['description']} |" for item in projection["inputRegions"]], "",
        "These descriptions sit beside the Lean predicates. The correspondence proof checks predicates against the classifier, not the English wording.", "",
        "### 7. `decide` branch map", "",
        "View: Level 2 — one operation. Focus: every declared `decide` branch. Hidden: predicate formulas and runtime effects.", "",
        "```mermaid", "flowchart LR",
    ]
    for index, item in enumerate(projection["decideBranches"]):
        lines.append(f'  S{index}(["{item["source"]}"]) -->|"decide"| T{index}(["{item["target"]}"])')
    lines += ["```", "", "| Canonical branch | Source | Target | Responsibility | Primary implementation |", "| --- | --- | --- | --- | --- |"]
    for item in projection["decideBranches"]:
        lines.append(f"| `{item['id']}` | `{item['source']}` | `{item['target']}` | {', '.join(item['responsibility']) or 'unassigned'} | `{primary_label(item['implementation'])}` ({item['implementation']['status']}) |")
    lines += ["", "### 8. Partial ledger mapping", "", "| Decision member | Ledger-command member |", "| --- | --- |"]
    for item in projection["ledgerMappings"]:
        target = "∅" if item["target"] == "none" else f"`{item['target']}`"
        lines.append(f"| `{item['source']}` | {target} |")
    lines += ["", "∅ means the operation is undefined for that member. It does not establish absence of unrelated runtime effects.", "",
              "### 9. Effects and state assumptions", ""]
    lines += [f"- **{item['subject']}**: {item['statement']}" for item in review["effectNotes"]]
    lines += ["", "### 10. Responsibility, code, and evidence", "",
              "| Canonical branch | Responsibility | Binding | Evidence references |", "| --- | --- | --- | --- |"]
    for item in [*projection["decideBranches"], *projection["ledgerBranches"]]:
        implementation = item["implementation"]
        evidence = "; ".join(entry["reference"] for entry in implementation.get("binding", {}).get("evidence", [])) or "none"
        lines.append(f"| `{item['id']}` | {', '.join(item['responsibility']) or 'unassigned'} | `{primary_label(implementation)}` ({implementation['status']}) | {evidence} |")
    lines += ["", "### 11. Machine-checked claims", ""]
    lines += [f"- {item['claim']} — `{item['proof']}`" for item in projection["checkedClaims"]]
    lines += ["", "Conditional claims: none exported in this scoped review projection. The effect and concurrency questions below remain unknown.", "",
              "These claims concern the declared model. Evidence references are not conformance proofs.", "",
              "### 12. Unknowns and review findings", ""]
    lines += [f"- **{item['subject']}**: {item['question']}" for item in review["questions"]]
    lines += ["", "| Finding | Subject | Concern | Required change | Disposition |", "| --- | --- | --- | --- | --- |"]
    for item in review["findings"]:
        lines.append(f"| `{item['id']}` | `{item['subject']}` | {item['concern']} | {item['requestedChange']} | {item['disposition']} |")
    lines += ["", "### 13. Approval record", ""]
    approval = review.get("approval")
    lines.append(f"- State: `{review['state']}`")
    lines.append(f"- Reviewer: {approval['reviewer'] if approval else 'none'}")
    lines.append(f"- Approved model revision: `{approval['revision']}`" if approval else "- Approved model revision: none")
    lines.append(f"- Implementation allowed by review gate: **{'yes' if allowed else 'no'}**")
    lines += ["", "### Appendix: source anchors", "",
              "- `ArchiScript/Examples/PaymentWebhook.lean`: carrier, partitions, operations, registry, and checked claims",
              "- `ArchiScript/Operation.lean`: canonical branch and implementation-binding API",
              "- `review/payment-webhook.review.json`: review notes, findings, and approval state", ""]
    return "\n".join(lines)


def tex_escape(text):
    replacements = {
        "\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
        "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}",
        "~": r"\textasciitilde{}", "^": r"\textasciicircum{}",
        "→": r"$\rightarrow$", "∅": r"$\emptyset$", "—": "---", "–": "--",
    }
    return "".join(replacements.get(char, char) for char in str(text))


def tex_identifier(text):
    return (tex_escape(text).replace(".", r".\allowbreak{}")
            .replace(r"\_", r"\_\allowbreak{}"))


def tex_table(headers, rows, widths):
    def cell_text(value):
        text = tex_escape(value)
        return (text.replace(".", r".\allowbreak{}")
                    .replace("/", r"/\allowbreak{}")
                    .replace(":", r":\allowbreak{}"))

    spec = "|" + "|".join(f"p{{{width}\\linewidth}}" for width in widths) + "|"
    result = [r"\par\medskip\noindent\begin{tabular}{" + spec + "}", r"\hline",
              " & ".join(r"\textbf{" + tex_escape(head) + "}" for head in headers) + r" \\ \hline"]
    for row in rows:
        result.append(" & ".join(cell_text(cell) for cell in row) + r" \\ \hline")
    result.append(r"\end{tabular}\par\medskip")
    return "\n".join(result)


def latex_pack(projection, review, revision, changes, allowed):
    t = tex_escape
    lines = [r"\documentclass[10pt]{article}",
             r"\usepackage[T1]{fontenc}",
             r"\usepackage[margin=0.7in]{geometry}",
             r"\setlength{\parindent}{0pt}",
             r"\setlength{\parskip}{3pt}",
             r"\raggedright",
             r"\begin{document}",
             r"\begin{center}{\LARGE PaymentWebhook engineering review pack}\\[8pt]",
             f"Model revision: {t(revision)}\\\\",
             f"Review state: {t(review['state'])}\\\\",
             f"Approval reviewer: {t(review['approval']['reviewer'] if review.get('approval') else 'none')}\\\\",
             f"Implementation gate: {'OPEN' if allowed else 'CLOSED'}",
             r"\end{center}",
             r"\textit{Generated snapshot. Semantic rows come from Lean; review notes and findings come from structured review metadata.}",
             r"\section*{Fast pass}",
             r"\subsection*{Scope and changes}", t(review["scope"]),
             r"\begin{itemize}", *[r"\item " + t(change) for change in changes], r"\end{itemize}",
             r"\subsection*{Boundary to challenge}",
             r"\textbf{" + t(review["boundary"]["subject"]) + "}: " + t(review["boundary"]["description"]),
             r"\textbf{Review challenge:} " + t(review["boundary"]["challenge"]),
             r"\subsection*{Operation topology -- Level 1}",
             latex_topology(projection),
             "Partial operations: " + t(", ".join(
                 item["operation"] for item in projection["topology"] if item["partial"]) or "none") + ".",
             r"Arrows mean member mappings, not runtime calls. Hidden: individual members, effects, and proofs.",
             r"\textbf{Operation responsibility:} ",
             *[t(operation + ": " + (", ".join(owners) or "unassigned")) + r"\\"
               for operation, owners in operation_owners(projection)],
             r"\subsection*{Assumptions and open questions}", r"\begin{itemize}"]
    lines += [r"\item " + t(item["subject"] + ": " + item["statement"]) for item in review["assumptions"]]
    lines += [r"\item " + t(item["subject"] + ": " + item["question"]) for item in review["questions"]]
    lines += [r"\end{itemize}", r"\newpage", r"\section*{Deep pass}",
              r"\subsection*{Semantic partitions}"]
    for key, name in (("inputMembers", "inputPartition"), ("decisionMembers", "decisionPartition"),
                      ("ledgerMembers", "ledgerCommandPartition")):
        lines.append(r"\textbf{" + t(name) + "}: " + t(", ".join(projection[key])) + r"\\")
    lines.append("Coarsening: none represented in this scoped review projection.")
    lines += [tex_table(("Input member", "Review meaning"),
                        [(item["name"], item["description"]) for item in projection["inputRegions"]],
                        (.24, .63)),
              "The descriptions sit beside the Lean predicates. The proof checks predicates against the classifier, not the English wording."]
    lines += [r"\subsection*{decide branch map -- Level 2}",
              "Focus: all declared decide branches. Hidden: predicate formulas and runtime effects.",
              tex_table(("Canonical branch", "Source", "Target"),
                        [(item["id"], item["source"], item["target"])
                         for item in projection["decideBranches"]], (.47, .20, .20)),
              r"\subsection*{Partial ledger mapping}",
              tex_table(("Decision", "Ledger command"),
                        [(item["source"], "∅" if item["target"] == "none" else item["target"])
                         for item in projection["ledgerMappings"]], (.42, .45)),
              r"$\emptyset$ means undefined for this member; it does not prove absence of unrelated runtime effects.",
              r"\subsection*{Effects and state assumptions}", r"\begin{itemize}"]
    lines += [r"\item " + t(item["subject"] + ": " + item["statement"]) for item in review["effectNotes"]]
    lines += [r"\end{itemize}", r"\subsection*{Responsibility and implementation}",
              tex_table(("Branch", "Responsibility", "Primary code / status"),
                        [(item["id"], ", ".join(item["responsibility"]),
                          primary_label(item["implementation"]) + " (" + item["implementation"]["status"] + ")")
                         for item in [*projection["decideBranches"], *projection["ledgerBranches"]]],
                        (.37, .20, .31)),
              r"\subsection*{Machine-checked claims}", r"\begin{itemize}"]
    lines += [r"\item " + t(item["claim"]) + " (" + tex_identifier(item["proof"]) + ")"
              for item in projection["checkedClaims"]]
    lines += [r"\end{itemize}",
              "Conditional claims: none exported in this scoped review projection. Effect and concurrency questions remain unknown.",
              r"Code bindings and test references do not prove code conformance.",
              r"\subsection*{Unknowns and findings}", r"\begin{itemize}"]
    lines += [r"\item " + t(item["subject"] + ": " + item["question"]) for item in review["questions"]]
    lines += [r"\end{itemize}"]
    for item in review["findings"]:
        lines += [r"\textbf{" + t(item["id"] + " — " + item["subject"]) + "} (" + t(item["disposition"]) + ")\\",
                  t(item["concern"]), r"\textit{Required change:} " + t(item["requestedChange"]), r"\par"]
    lines += [r"\end{document}"]
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--previous", type=Path, help="earlier generated snapshot JSON")
    args = parser.parse_args()
    projection = projection_from_lean()
    review = json.loads(REVIEW_SOURCE.read_text())
    validate_review(projection, review)
    revision = model_revision()
    previous_snapshot = json.loads(args.previous.read_text()) if args.previous else None
    previous = previous_snapshot.get("projection", previous_snapshot) if previous_snapshot else None
    previous_review = previous_snapshot.get("review") if previous_snapshot else None
    changes = semantic_changes(projection, previous, review, previous_review)
    allowed = approval_status(review, revision)
    OUTPUT.mkdir(parents=True, exist_ok=True)
    snapshot = {"modelRevision": revision, "projection": projection, "review": review}
    (OUTPUT / "PaymentWebhook.snapshot.json").write_text(json.dumps(snapshot, indent=2) + "\n")
    (OUTPUT / "PaymentWebhook.md").write_text(
        markdown_pack(projection, review, revision, changes, allowed))
    with tempfile.TemporaryDirectory(prefix="archiscript-review-") as temporary:
        tex_file = Path(temporary) / "PaymentWebhook.tex"
        tex_file.write_text(latex_pack(projection, review, revision, changes, allowed))
        subprocess.run(["tectonic", "-C", str(tex_file), "-o", str(OUTPUT)],
                       cwd=ROOT, check=True, capture_output=True, text=True)
    print(f"Review pack: {OUTPUT / 'PaymentWebhook.pdf'}")
    print(f"Model revision: {revision}; implementation gate: {'open' if allowed else 'closed'}")


if __name__ == "__main__":
    main()
