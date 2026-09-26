# Current Lean API patterns

Read the installed `ArchiScript.lean` and its imported modules before adapting
these patterns. Declaration names and types in the installed package are
authoritative.

## Partition shape

The example boundary is an externally supplied natural-number request (for
example, a protocol count); zero is a real input, not a missing constructor.
The carrier is all `Nat`, and the partition uses the zero predicate and its
complement. The finite inductive type is only the label universe.

```lean
import ArchiScript

open ArchiScript

inductive RequestIndex where
  | zero
  | positive
  deriving DecidableEq

def positive : Domain Nat := fun n => 0 < n

def requestPartition : Partition where
  Carrier := Nat
  MemberIndex := RequestIndex
  carrierNonempty := ⟨0⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.zero, .positive]
  memberIndices_complete := by intro i; cases i <;> simp
  classify n := if n = 0 then .zero else .positive
  member_inhabited
    | .zero => ⟨0, rfl⟩
    | .positive => ⟨1, rfl⟩
```

Here `requestPartition.member .positive` is extensionally the positive
predicate and `requestPartition.member .zero` is its relative complement. The
external specification is “a `Nat` request is supplied”; the classifier does
not invent the carrier from two selected examples. `MemberIndex` contains
labels, while `requestPartition.member .positive` is the semantic predicate.
The finite enumeration is not the carrier.

To check that the classifier realizes separately named semantic regions:

```lean
def requestRegions : RequestIndex → Domain Nat
  | .zero => Domain.complement positive
  | .positive => positive

example : requestPartition.Realizes requestRegions := by
  intro i n
  cases i <;> cases n <;> simp [Partition.member, requestPartition, requestRegions,
    Domain.complement, positive]
```

This correspondence constrains the model: the selected regions must equal the
actual classifier fibers. It is separate proof evidence, so it does not change
partition identity or composition endpoints. Core coverage and disjointness
then apply to those regions; there is no separate tree obligation.

## Subdomains and architectural resolution

Represent a named subdomain as a `Domain` predicate. Containment is implication,
intersection is conjunction, and union is disjunction. A domain can be contained
in several parents; supporting domains need not be disjoint or exhaustive.
`Domain.complement s` negates `s` over the whole carrier, while
`Domain.relativeComplement parent s contained` means $parent \setminus s$,
implemented as `fun x => parent x ∧ ¬ s x`. Supply containment evidence
`contained : ∀ x, s x → parent x`. For example, exclude `completeForm` from
`emailProvided` using `fun _ h => h.1`; the independent `nameProvided` domain is
not itself contained in `emailProvided`.

A VDP groups regions at the resolution its consumers need. The library's
`ArchiScript.Examples.FormInput` demonstrates two arbitrary string fields:
`emailProvided` and `nameProvided` overlap, their intersection is `completeForm`,
and the remaining three combinations can be either separate members or one
incomplete member. Both VDPs have checked `Realizes` evidence. The
`forgetFieldFailures` operation coarsens the four members to two, with a proof
that the member mapping agrees with classification of the same input value.
These predicates model presence, not full email or name validation.

This implements the docs' distinction between supporting semantic regions and
the selected partition members. A flat declaration is normal; a tree is only a
possible explanatory view. Opaque-domain reasoning can take explicit predicate
parameters and assumptions; the core has no symbolic provenance registry or
automatic inference of those assumptions.

## Operations and canonical branch references

An `Operation` is only a partial member map:

```lean
def accept : Operation requestPartition requestPartition where
  run
    | .zero => none
    | .positive => some .positive
```

Stable declaration identity comes from `Operation.Registry.OperationName`, not
from extensional equality of `accept.run`. A declaration owns its scoped
`BranchName` and one resolver:

```lean
inductive OperationName where | accept deriving DecidableEq
inductive BranchName where | positive deriving DecidableEq

def acceptDeclaration : Operation.Declaration where
  source := requestPartition
  target := requestPartition
  operation := accept
  BranchName := BranchName
  branchNameDecidableEq := inferInstance
  branch
    | .positive => ⟨.positive, .positive, rfl⟩
  owners := ["request-api"]
  branchOwners := fun _ => some ["request-processing"]

def registry : Operation.Registry where
  OperationName := OperationName
  operationNameDecidableEq := inferInstance
  resolve
    | .accept => acceptDeclaration

def acceptedBranch : Operation.BranchAddress registry :=
  ⟨.accept, .positive⟩

def acceptedBranchWitness := registry.resolveBranch acceptedBranch

#guard registry.resolveBranchOwners acceptedBranch == ["request-processing"]
```

One registry value is the uniqueness scope. Another registry is another model
scope. An alias is a definition equal to the same `OperationName` or
`BranchAddress`; a new name is a new declaration identity even if the map is
extensionally equal.

`owners` defaults to `[]`, and `branchOwners` defaults to `fun _ => none`.
`none` inherits the operation tags; `some tags` replaces them, and `some []`
explicitly marks a branch unassigned. Use `declaration.effectiveOwners name`
or `registry.resolveBranchOwners address` for effective ownership. Tags are
free-form responsibility labels, with no inferred permission or effect semantics.
There is no automatic owner propagation through `Operation.comp`: register and
annotate a composite declaration when it needs its own responsibility contract.

The repository example demonstrates an effect theorem tied to a canonical
branch:

```lean
import ArchiScript.Examples.UserRegistration

open ArchiScript.Examples.UserRegistration

#check existingUserBranch
#check existingUserBranchWitness
#check existingUserBranch_creates_no_user
#check NewUserCreation
```

`existingUserBranch_creates_no_user` depends on an explicit
`ExistingSelection` contract whose `store_preserved` premise provides the
no-creation result. It is not derived from the member labels.
The new-user contract's `absent_before` and `present_after` fields can be used
directly; do not add a theorem merely to conjoin them. Likewise, branch aliases
need no named equality theorem. Tests can check the API without turning those
checks into model guarantees.

## Routed parameterization

`ParameterizedPartition.Routed.routeOperation` returns a canonical registry
operation name. `resolveOutbound` derives its typed target and operation from
the registry; callers cannot independently attach a different payload.
`routeSource` proves that the registered operation source matches the selected
specialization.

Use `RoutingRelevant` to show that some canonical operation is available in one
specialization and unavailable in another. Use `RoutesEquivalent` to show that
renamed or duplicated route aliases preserve the same operation availability.

The runnable file [../examples/CurrentApi.lean](../examples/CurrentApi.lean)
checks these entry points against the repository's current library.

## Diagnostics

The core has no missing-tree warning or automatic semantic-boundary linter.
Current checks are Lean type/proof obligations:

| Condition | Result | Why |
| --- | --- | --- |
| Flat declaration with valid partition evidence | Accepted | Presentation does not determine semantic validity |
| Overlapping or incomplete supporting subdomains | Accepted | Supporting regions are not necessarily VDP members |
| Selected regions disagree with classifier fibers | `Partition.Realizes` cannot be proved | Declared semantics must match actual members |
| Missing inhabitance or enumeration evidence | Lean proof/type error | Every declared member must exist and be enumerated |
| Conflicting branch or route source | Lean proof/type error | Witnesses must match the canonical declaration |

The original design calls for `unjustified-generalization` when a convenient
leaf union becomes a carrier, complement boundary, or completeness universe
without an independently established parent or explicit constructor closure.
Apply that as a review criterion here; automatic detection needs provenance
that this Lean core does not yet represent. A union or Lean `inductive` alone
does not justify a warning.

Unused, equivalent, or safely collapsible subdomains are possible design-smell
diagnostics, not foundational errors; these are also not implemented.
Completeness is always relative to the stated universe and assumptions. A
classifier can be valid while omitting real-world cases from its carrier, and
an unchecked named predicate need not describe any classifier member.
