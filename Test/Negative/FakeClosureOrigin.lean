import ArchiScript

open ArchiScript

inductive ConvenientCount where
  | small | large

def closed : CarrierClosure ConvenientCount :=
  ⟨[.small, .large], by intro x; cases x <;> simp⟩

-- Closure of a convenient type cannot be used as its boundary origin.
def fakeOrigin : CarrierOrigin ConvenientCount := closed
