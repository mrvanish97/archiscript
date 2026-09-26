import ArchiScript

open ArchiScript ArchiScript.Examples.FormInput

-- Overlapping supporting domains cannot serve as two distinct VDP members.
def overlappingRegions : formPartition.MemberIndex → Domain Input
  | true => emailProvided
  | false => nameProvided

example : formPartition.Realizes overlappingRegions := by
  intro i x
  rfl
