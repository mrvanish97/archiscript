import ArchiScriptExamples.UserRegistration

open ArchiScript
open ArchiScriptExamples.UserRegistration

-- Expected failure: the canonical address resolves once, to the selected branch.
example : existingUserBranchWitness.target = RegistrationMemberIndex.created := rfl
