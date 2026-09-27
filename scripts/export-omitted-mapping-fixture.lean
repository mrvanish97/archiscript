import Lean
import ArchiScriptExamples.UserRegistration

open Lean ArchiScript ArchiScriptExamples.UserRegistration

inductive NoBranch deriving DecidableEq

private def unnamedRegister : Operation.Declaration where
  source := userPartition
  target := registrationPartition
  operation := register
  BranchName := NoBranch
  branchNameDecidableEq := inferInstance
  branchNames := []
  branchNames_complete := by intro name; cases name
  branchNames_nodup := by simp
  branch := by intro name; cases name

def main : IO Unit :=
  IO.println (Json.compress (toJson unnamedRegister.definedMappingsWithoutBranch.length))
