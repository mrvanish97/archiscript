import Lean
import ArchiScriptExamples.Asphalt

open Lean
open ArchiScript
open ArchiScriptExamples.Asphalt

private def projection : Json := Id.run do
  have _ : admissionArchitecture.partition.HasMembers
      (fun i => (admissionArchitecture.selectedMembers i).meaning) :=
    admissionArchitecture.hasMembers
  have _ : CarrierOrigin Nat := naturalCarrierOrigin
  let status := match admissionArchitecture.carrierOrigin with
    | .externalRoot _ => "trusted-external-root"
    | .externalNarrowing .. => "trusted-external-narrowing"
    | .internalOutput .. => "declared-internal-output"
    | .derived .. => "derived-contract"
  let naturalStatus := match naturalCarrierOrigin with
    | .externalRoot _ => "trusted-external-root"
    | .externalNarrowing .. => "trusted-external-narrowing"
    | .internalOutput .. => "declared-internal-output"
    | .derived .. => "derived-contract"
  let naturalUpstreamStatus := match naturalCarrierOrigin with
    | .derived _ _ _ upstream _ _ _ _ =>
      match upstream with
      | .externalRoot _ => "trusted-external-root"
      | .externalNarrowing .. => "trusted-external-narrowing"
      | .internalOutput .. => "declared-internal-output"
      | .derived .. => "derived-contract"
    | _ => "none"
  return Json.mkObj [
    ("model", toJson "Asphalt admission slice"),
    ("admissionCarrierOrigin", toJson status),
    ("opaqueSupportingSubdomains",
      toJson admissionArchitecture.opaqueSupportingSubdomains),
    ("naturalCountCarrierOrigin", toJson naturalStatus),
    ("naturalCountUpstreamOrigin", toJson naturalUpstreamStatus),
    ("naturalCountSource", toJson "Asphalt.countPartition.nonnegative")
  ]

def main : IO Unit := IO.println projection.compress
