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
    "ArchiScript/Boundary.lean",
    "ArchiScript/Operation.lean",
    "ArchiScript/Operation/Declaration.lean",
    "ArchiScriptExamples/PaymentWebhook.lean",
)
REVIEW_SOURCE = ROOT / "review/payment-webhook.review.json"
OUTPUT = ROOT / "review/generated"


def source_fingerprint():
    digest = hashlib.sha256()
    for name in MODEL_SOURCES:
        digest.update(name.encode())
        digest.update((ROOT / name).read_bytes())
    return digest.hexdigest()


def reviewed_contract(review):
    """Only review content requiring renewed approval; approval is self-referential."""
    return {key: value for key, value in review.items()
            if key not in {"approval", "state"}}


def model_revision(projection, review, checked_sources=None):
    contract = {"sources": checked_sources or source_fingerprint(),
                "projection": projection, "review": reviewed_contract(review)}
    encoded = json.dumps(contract, sort_keys=True, ensure_ascii=False,
                         separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()[:12]


def projection_from_lean():
    subprocess.run(["lake", "build", "ArchiScriptExamples.PaymentWebhook"],
                   cwd=ROOT, text=True, capture_output=True, check=True)
    result = subprocess.run(
        ["lake", "env", "lean", "--run", "scripts/export-payment-review.lean"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    return json.loads(result.stdout)


def validate_carrier_origin(origin, partition_id):
    status = origin["status"]
    if status in {"trusted-external-root", "trusted-external-narrowing"}:
        if not all(origin.get(key) for key in ("source", "scope", "claim", "revision")):
            raise ValueError(f"incomplete external carrier guarantee: {partition_id}")
    elif status == "derived-contract":
        if not origin.get("upstream") or not origin.get("sourceMember"):
            raise ValueError(f"incomplete derived carrier contract: {partition_id}")
        if "upstreamProvenance" not in origin:
            raise ValueError(f"derived carrier has no upstream provenance: {partition_id}")
        validate_carrier_origin(origin["upstreamProvenance"], origin["upstream"])
    elif status != "closed-constructors":
        raise ValueError(f"unrecognized carrier provenance: {partition_id}")


def validate_review(projection, review):
    if review.get("model") != projection["model"]:
        raise ValueError("review metadata names a different model")
    objects = {entry["id"] for entry in projection["objects"]}
    if len(objects) != len(projection["objects"]):
        raise ValueError("projection contains duplicate canonical IDs")
    partitions = {item["id"] for item in projection["objects"]
                  if item["kind"] == "partition"}
    semantic = projection["semanticPartitions"]
    if len(semantic) != len(partitions) or {item["id"] for item in semantic} != partitions:
        raise ValueError("every reviewed partition needs semantic member evidence")
    for item in semantic:
        expected = {entry["id"] for entry in projection["objects"]
                    if entry["kind"] == "member" and
                    entry["id"].startswith(item["id"] + ".")}
        if not item["proof"] or len(item["members"]) != len(expected) or set(item["members"]) != expected:
            raise ValueError(f"incomplete semantic member evidence: {item['id']}")
    architectural = projection.get("architecturalPartitions", [])
    if (len(architectural) != len(partitions) or
            {item["id"] for item in architectural} != partitions):
        raise ValueError("every reviewed partition needs carrier provenance and member definitions")
    for item in architectural:
        validate_carrier_origin(item["carrierProvenance"], item["id"])
        expected = {entry["id"] for entry in projection["objects"]
                    if entry["kind"] == "member" and
                    entry["id"].startswith(item["id"] + ".")}
        definitions = item["members"]
        if len(definitions) != len(expected) or {entry["id"] for entry in definitions} != expected:
            raise ValueError(f"incomplete selected member definitions: {item['id']}")
        for entry in [*definitions, *item.get("supportingSubdomains", [])]:
            definition = entry["definition"]
            if definition["status"] == "opaque":
                if not definition.get("reason"):
                    raise ValueError(f"opaque subdomain needs a reason: {entry['id']}")
            elif definition["status"] == "formula":
                if not definition.get("description"):
                    raise ValueError(f"formula subdomain needs a review description: {entry['id']}")
            else:
                raise ValueError(f"unrecognized subdomain definition: {entry['id']}")
    coverage = projection["mappingCoverage"]
    operation_ids = {item["id"] for item in projection["topology"]}
    if (len(coverage) != len(operation_ids) or
            {item["id"] for item in coverage} != operation_ids):
        raise ValueError("mapping coverage must name every exported operation once")
    missing = [item["id"] for item in coverage if item["missingDefinedMappings"]]
    if missing:
        raise ValueError(f"defined mappings lack named branches: {', '.join(missing)}")
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
        and approval.get("revision")
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


def architecture_summary(projection):
    rows = []
    for item in projection["architecturalPartitions"]:
        origin = item["carrierProvenance"]
        detail = ", ".join(f"{key}={origin[key]}" for key in
                           ("source", "scope", "claim", "revision", "upstream", "sourceMember")
                           if key in origin)
        rows.append((item["id"], origin["status"], detail or "finite constructors exhaust carrier"))
    return rows


def opaque_member_warnings(projection):
    return [(member["id"], member["definition"]["reason"])
            for item in projection["architecturalPartitions"]
            for member in [*item["members"], *item.get("supportingSubdomains", [])]
            if member["definition"]["status"] == "opaque"]


def mermaid_topology(projection):
    names = list(dict.fromkeys(
        name for operation in projection["topology"]
        for name in (operation["source"], operation["target"])))
    nodes = {name: f"P{index}" for index, name in enumerate(names)}
    return [f'  {nodes[operation["source"]]}["{operation["source"]}"] -->|"'
            f'{operation["operation"]}{" · partial" if operation["partial"] else ""}"| '
            f'{nodes[operation["target"]]}["{operation["target"]}"]'
            for operation in projection["topology"]]


def mermaid_decide_branches(projection):
    branches = projection["decideBranches"]
    sources = list(dict.fromkeys(item["source"] for item in branches))
    targets = list(dict.fromkeys(item["target"] for item in branches))
    source_ids = {name: f"S{index}" for index, name in enumerate(sources)}
    target_ids = {name: f"T{index}" for index, name in enumerate(targets)}
    lines = ['  subgraph INPUT["inputPartition"]', '    direction TB']
    lines += [f'    {source_ids[name]}["{name}"]' for name in sources]
    lines += ['  end', '  subgraph DECISION["decisionPartition"]', '    direction TB']
    lines += [f'    {target_ids[name]}["{name}"]' for name in targets]
    lines += ['  end']
    lines += [f'  {source_ids[item["source"]]} -->|"decide"| {target_ids[item["target"]]}'
              for item in branches]
    return lines


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


def tikz_decide_branches(projection):
    branches = projection["decideBranches"]
    count = len(branches)
    bottom = -0.68 * count - 0.15
    lines = [r"\begin{center}", r"\begin{tikzpicture}[>=stealth, font=\small]",
             rf"\draw[rounded corners] (-0.2,0.5) rectangle (3.1,{bottom:.2f});",
             rf"\draw[rounded corners] (5.0,0.5) rectangle (9.5,{bottom:.2f});",
             r"\node[font=\bfseries] at (1.45,0.20) {inputPartition};",
             r"\node[font=\bfseries] at (7.25,0.20) {decisionPartition};"]
    for index, item in enumerate(branches):
        y = -0.36 - 0.68 * index
        lines += [rf"\node[draw, rounded corners, minimum width=2.65cm] (S{index}) at (1.45,{y:.2f}) {{{tex_escape(item['source'])}}};",
                  rf"\node[draw, rounded corners, minimum width=3.95cm] (T{index}) at (7.25,{y:.2f}) {{{tex_escape(item['target'])}}};",
                  rf"\draw[->] (S{index}.east) -- (T{index}.west);"]
    lines += [r"\end{tikzpicture}", r"\end{center}"]
    return "\n".join(lines)


def latex_decide_branches(projection):
    branches = projection["decideBranches"]
    height = 8 * len(branches) + 9
    lines = [r"\begin{center}\setlength{\unitlength}{1mm}",
             rf"\begin{{picture}}(150,{height})",
             rf"\put(0,0){{\framebox(63,{height}){{}}}}",
             rf"\put(85,0){{\framebox(65,{height}){{}}}}",
             rf"\put(3,{height - 5}){{\textbf{{inputPartition}}}}",
             rf"\put(88,{height - 5}){{\textbf{{decisionPartition}}}}"]
    for index, item in enumerate(branches):
        y = height - 13 - 8 * index
        lines += [rf"\put(3,{y}){{\framebox(57,6){{\texttt{{{tex_escape(item['source'])}}}}}}}",
                  rf"\put(88,{y}){{\framebox(59,6){{\texttt{{{tex_escape(item['target'])}}}}}}}",
                  rf"\put(63,{y + 3}){{\makebox(22,0){{$\longrightarrow$}}}}"]
    lines += [r"\end{picture}\end{center}"]
    return "\n".join(lines)


def semantic_changes(current, previous, current_review=None, previous_review=None):
    if previous is None:
        return ["First generated snapshot; no earlier projection supplied."]
    missing = object()

    def identity(item, path):
        if not isinstance(item, dict):
            return str(item)
        if "id" in item:
            return item["id"]
        if path.endswith(".checkedClaims"):
            return item.get("proof", item["claim"])
        if path.endswith(".ledgerMappings"):
            return item["source"]
        if path.endswith(".supporting"):
            return ":".join(str(item.get(key) or "")
                            for key in ("repository", "path", "symbol"))
        if path.endswith(".evidence"):
            return f"{item['kind']}:{item['reference']}"
        if "subject" in item:
            return f"{item['subject']}:{item.get('statement', item.get('question', ''))}"
        return json.dumps(item, sort_keys=True, ensure_ascii=False)

    def indexed(items, path):
        result = {}
        for item in items:
            key = identity(item, path)
            if key in result:
                raise ValueError(f"duplicate semantic identity at {path}: {key}")
            result[key] = item
        return result

    def differences(before, after, path):
        if before is missing:
            yield f"Added {path}: {after!r}"
        elif after is missing:
            yield f"Removed {path}: {before!r}"
        elif isinstance(before, dict) and isinstance(after, dict):
            for key in sorted(before.keys() | after.keys()):
                yield from differences(before.get(key, missing), after.get(key, missing),
                                       f"{path}.{key}")
        elif isinstance(before, list) and isinstance(after, list):
            old = indexed(before, path)
            new = indexed(after, path)
            for key in sorted(old.keys() | new.keys()):
                yield from differences(old.get(key, missing), new.get(key, missing),
                                       f"{path}[{key}]")
        elif before != after:
            yield f"{path}: {before!r} → {after!r}"

    changes = list(differences(previous, current, "projection"))
    if current_review is not None and previous_review is not None:
        changes.extend(differences(reviewed_contract(previous_review),
                                   reviewed_contract(current_review), "review"))
    return changes or ["No semantic changes detected in the exported projection or review contract."]


def markdown_pack(projection, review, revision, changes, allowed):
    lines = [
        "# PaymentWebhook engineering review pack", "",
        f"Model revision: `{revision}`", "",
        f"Review state: **{review['state']}**", "",
        f"Implementation gate: **{'OPEN' if allowed else 'CLOSED'}**", "",
        f"Named branch handoff: **COMPLETE** across {len(projection['mappingCoverage'])} registered operations.", "",
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
        "Each partition's selected member IDs and `HasMembers` proof travel in the review projection:", "",
        *[f"- `{item['id']}` — `{item['proof']}`"
          for item in projection["semanticPartitions"]], "",
        "**Carrier provenance**", "",
        "| Partition | Origin | Declared basis |", "| --- | --- | --- |",
        *[f"| `{name}` | `{status}` | {detail} |"
          for name, status, detail in architecture_summary(projection)], "",
        "External roots and guarantees are trusted premises; a checked derived contract does not prove production code conforms.", "",
        "**Opaque subdomains:** " + ("; ".join(f"`{name}` — {reason}"
            for name, reason in opaque_member_warnings(projection)) or "none") + ".", "",
        "An opaque subdomain has a declared extension but no formula available for deduction. Review its meaning and consider specifying a formula.", "",
        "The input carrier includes `alreadyRecorded`; the model does not establish how that observation was acquired.", "",
        "Coarsening: none represented in this scoped review projection.", "",
        "| Input member | Review meaning |", "| --- | --- |",
        *[f"| `{item['name']}` | {item['description']} |" for item in projection["inputRegions"]], "",
        "These descriptions sit beside the Lean predicates. The correspondence proof checks predicates against the classifier, not the English wording.", "",
        "### 7. `decide` branch map", "",
        "View: Level 2 — one operation. Focus: every declared `decide` branch. Hidden: predicate formulas and runtime effects.", "",
        "```mermaid", "flowchart LR",
    ]
    lines += mermaid_decide_branches(projection)
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
              "- `ArchiScriptExamples/PaymentWebhook.lean`: carrier, partitions, operations, registry, and checked claims",
              "- `ArchiScript/Operation.lean`: partial member-map algebra",
              "- `ArchiScript/Operation/Declaration.lean`: branch and implementation-binding API",
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
             r"\\ Named branch handoff: COMPLETE across " +
             t(str(len(projection["mappingCoverage"]))) + " registered operations",
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
    lines += [r"\textbf{Semantic correspondence evidence:}", r"\begin{itemize}"]
    lines += [r"\item " + tex_identifier(item["id"]) + ": " + tex_identifier(item["proof"])
              for item in projection["semanticPartitions"]]
    lines.append(r"\end{itemize}")
    lines.append(r"\textbf{Carrier provenance (external claims remain trusted):}")
    lines.append(tex_table(("Partition", "Origin", "Declared basis"),
                           architecture_summary(projection), (.27, .22, .39)))
    opaque = opaque_member_warnings(projection)
    lines.append(r"\textbf{Opaque subdomains:} " +
                 t("; ".join(f"{name}: {reason}" for name, reason in opaque) or "none") +
                 ". No formula is available for deduction; review the meaning and consider specifying one.")
    lines.append("Coarsening: none represented in this scoped review projection.")
    lines += [tex_table(("Input member", "Review meaning"),
                        [(item["name"], item["description"]) for item in projection["inputRegions"]],
                        (.24, .63)),
              "The descriptions sit beside the Lean predicates. The proof checks predicates against the classifier, not the English wording."]
    lines += [r"\subsection*{decide branch map -- Level 2}",
              "Focus: all declared decide branches. Hidden: predicate formulas and runtime effects.",
              latex_decide_branches(projection),
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
    checked_sources = source_fingerprint()
    projection = projection_from_lean()
    if checked_sources != source_fingerprint():
        raise RuntimeError("model sources changed while the Lean projection was built")
    review = json.loads(REVIEW_SOURCE.read_text())
    validate_review(projection, review)
    revision = model_revision(projection, review, checked_sources)
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
    (OUTPUT / "PaymentWebhook-decide.tikz").write_text(
        tikz_decide_branches(projection) + "\n")
    with tempfile.TemporaryDirectory(prefix="archiscript-review-") as temporary:
        tex_file = Path(temporary) / "PaymentWebhook.tex"
        tex_file.write_text(latex_pack(projection, review, revision, changes, allowed))
        subprocess.run(["tectonic", "-C", str(tex_file), "-o", str(OUTPUT)],
                       cwd=ROOT, check=True, capture_output=True, text=True)
    print(f"Review pack: {OUTPUT / 'PaymentWebhook.pdf'}")
    print(f"Model revision: {revision}; implementation gate: {'open' if allowed else 'closed'}")


if __name__ == "__main__":
    main()
