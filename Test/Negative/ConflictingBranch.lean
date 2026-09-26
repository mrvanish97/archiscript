import ArchiScript.Examples.UserRegistration

open ArchiScript
open ArchiScript.Examples.UserRegistration

-- Expected failure: the canonical address resolves once, to the selected branch.
example : existingUserBranchWitness.target = RegistrationMemberIndex.created := rfl
