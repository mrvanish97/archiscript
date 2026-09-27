import ArchiScript

open ArchiScript

-- A derivation indexed by x < 5 cannot define the member x > 100.
def dishonest : DomainDerivation Nat (fun x => x > 100) :=
  .predicate (fun x => x < 5)
