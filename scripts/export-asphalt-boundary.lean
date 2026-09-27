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
    | .architecturalDomain .. => "architecture-defined-domain"
  let naturalStatus := match naturalCarrierOrigin with
    | .externalRoot _ => "trusted-external-root"
    | .externalNarrowing .. => "trusted-external-narrowing"
    | .architecturalDomain .. => "architecture-defined-domain"
  return Json.mkObj [
    ("model", toJson "Asphalt admission slice"),
    ("admissionCarrierOrigin", toJson status),
    ("opaqueSupportingSubdomains",
      toJson admissionArchitecture.opaqueSupportingSubdomains),
    ("naturalCountCarrierOrigin", toJson naturalStatus),
    ("naturalCountSource", toJson "external decoder contract; no carrier-valued operation is modeled")
  ]

def main : IO Unit := IO.println projection.compress
