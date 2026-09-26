import ArchiScript

open ArchiScript ArchiScript.Examples.FormInput

-- Listing only both-present and both-missing omits the mixed input cases.
def incompleteRegions : formPartition.MemberIndex → Domain Input
  | true => completeForm
  | false => fun x => ¬ emailProvided x ∧ ¬ nameProvided x

example : formPartition.Realizes incompleteRegions := by
  intro i x
  rfl
