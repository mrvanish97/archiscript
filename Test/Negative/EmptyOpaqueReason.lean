import ArchiScript

open ArchiScript

-- An opaque leaf must remain visible with a substantive reason.
def silentUnknown : DomainDerivation Nat (fun _ => True) :=
  .opaque "" (by decide) (fun _ => True)
