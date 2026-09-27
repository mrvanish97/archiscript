import ArchiScript

open ArchiScript

inductive ConvenientCount where
  | small | large

-- A string cannot certify an internal output. A typed producer and its source
-- origin are required by the constructor.
def fakeOrigin : CarrierOrigin ConvenientCount :=
  .internalOutput "imaginary producer"
