import ArchiScript

open ArchiScript

inductive ConvenientCount where
  | small | large

-- Operations have no carrier-producing provenance constructor. A member
-- mapping cannot certify the target carrier's boundary universe.
def fakeOrigin : CarrierOrigin ConvenientCount :=
  .internalOutput "imaginary producer"
