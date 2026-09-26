import ArchiScript.Operation

namespace ArchiScript

universe u w

/-- A PVDP family is indexed by the finite member set of a parameter VDP. -/
structure ParameterizedPartition (K : Partition.{u, u}) where
  specialize : K.MemberIndex → Partition.{u, u}

namespace ParameterizedPartition

/-- One resolved outbound operation, retaining its typed target. -/
structure Outbound (source : Partition.{u, u}) where
  target : Partition.{u, u}
  operation : Operation source target

/-- Finite, declared outbound route names for each specialization. -/
structure Routed (K : Partition.{u, u}) where
  specialize : K.MemberIndex → Partition.{u, u}
  registry : Operation.Registry.{u}
  Route : (k : K.MemberIndex) → Type
  routes : (k : K.MemberIndex) → List (Route k)
  routes_complete : ∀ k r, r ∈ routes k
  routeOperation : (k : K.MemberIndex) → Route k → registry.OperationName
  routeSource : ∀ k r,
    (registry.resolve (routeOperation k r)).source = specialize k

def Routed.resolveOutbound {K : Partition.{u, u}} (P : Routed K)
    (k : K.MemberIndex) (route : P.Route k) : Outbound (P.specialize k) :=
  let declaration := P.registry.resolve (P.routeOperation k route)
  let sourceEq := P.routeSource k route
  { target := declaration.target
    operation := sourceEq ▸ declaration.operation }

def HasOperation {K : Partition.{u, u}} (P : Routed K)
    (k : K.MemberIndex) (operation : P.registry.OperationName) : Prop :=
  ∃ route, P.routeOperation k route = operation

/-- Relevance means availability of an identified actual route changes. -/
def RoutingRelevant {K : Partition.{u, u}} (P : Routed K) : Prop :=
  ∃ a b operation, HasOperation P a operation ↔ ¬ HasOperation P b operation

def RoutesEquivalent {K : Partition.{u, u}} (P : Routed K)
    (a b : K.MemberIndex) : Prop :=
  ∀ operation, HasOperation P a operation ↔ HasOperation P b operation

/-- A resolved ordinary VDP may parameterize the next finite family. -/
structure Nested (Outer : Partition.{u, u}) where
  innerParameter : Outer.MemberIndex → Partition.{u, u}
  result : (o : Outer.MemberIndex) → (innerParameter o).MemberIndex → Partition.{u, u}

def Nested.specialize {Outer : Partition.{u, u}} (P : Nested Outer)
    (o : Outer.MemberIndex) (i : (P.innerParameter o).MemberIndex) : Partition.{u, u} :=
  P.result o i

end ParameterizedPartition
end ArchiScript
