import Lean
import ArchiScriptExamples.Asphalt

open Lean
open ArchiScript
open ArchiScriptExamples.Asphalt

private def projection : Json := Id.run do
  have _ : admissionArchitecture.partition.HasMembers
      (fun i => (admissionArchitecture.selectedMembers i).meaning) :=
    admissionArchitecture.hasMembers
  have _ : CarrierProvenance Nat := naturalCarrierProvenance
  let status := match admissionArchitecture.carrierProvenance with
    | .externalRoot _ => "trusted-external-root"
    | .externalNarrowing _ => "trusted-external-narrowing"
    | .derived .. => "derived-contract"
    | .closedConstructors .. => "closed-constructors"
  let naturalStatus := match naturalCarrierProvenance with
    | .externalRoot _ => "trusted-external-root"
    | .externalNarrowing _ => "trusted-external-narrowing"
    | .derived .. => "derived-contract"
    | .closedConstructors .. => "closed-constructors"
  let naturalUpstreamStatus := match naturalCarrierProvenance with
    | .derived _ _ _ upstream _ _ _ _ =>
      match upstream with
      | .externalRoot _ => "trusted-external-root"
      | .externalNarrowing _ => "trusted-external-narrowing"
      | .derived .. => "derived-contract"
      | .closedConstructors .. => "closed-constructors"
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
