import Lean
import ArchiScript.Review

open ArchiScript Lean

private def finding (disposition : FindingDisposition) : ReviewFinding := {
  id := "F"
  subject := { kind := .carrier, canonicalId := "M.Input" }
  reviewer := "engineer"
  concern := "concern"
  requestedChange := "change"
  disposition := disposition
}

private def record (decision : ReviewDecision) (disposition : FindingDisposition) : ReviewRecord := {
  modelRevision := "v1"
  decision := decision
  findings := [finding disposition]
}

def main : IO Unit := do
  let cases := [
    record (.approved "engineer" "v1") .addressed,
    record (.approved "engineer" "v2") .addressed,
    record (.approved "engineer" "") .addressed,
    record (.approved "" "v1") .addressed,
    record (.approved "engineer" "v1") .open,
    record .draft .addressed,
    record (.approved "engineer" "v1") .accepted
  ]
  IO.println (Json.compress (toJson (cases.map ReviewRecord.implementationAllowed)))
