import ArchiScript.Examples.UserRegistration

open ArchiScript
open ArchiScript.Examples.UserRegistration

-- Expected failure: a route cannot attach the canonical `register` payload to
-- a specialization whose source is `registrationPartition`.
def conflictingRouteSource : ParameterizedPartition.Routed channelPartition where
  specialize := fun _ => registrationPartition
  registry := operationRegistry
  Route := fun _ => Unit
  routes := fun _ => [()]
  routes_complete := by intro _ route; cases route; simp
  routeOperation := fun _ _ => .register
  routeSource := by intro _ route; cases route; rfl
