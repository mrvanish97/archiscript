import ArchiScript.Resolution
import ArchiScriptExamples.FormInput

namespace ArchiScriptTests.Resolution
open ArchiScript ArchiScriptExamples.FormInput

example : fieldPartition.RefinesVia formPartition forgetFieldFailuresMap :=
  fieldPartition_refines_formPartition

example : Function.Surjective forgetFieldFailuresMap :=
  Partition.coarseningMap_surjective fieldPartition_refines_formPartition

example : forgetFieldFailures =
    Partition.coarseningOperation forgetFieldFailuresMap := rfl

example : Operation.IsTotal forgetFieldFailures :=
  Operation.coarseningOperation_total forgetFieldFailuresMap

example : Operation.IsSurjective forgetFieldFailures :=
  Operation.coarseningOperation_surjective fieldPartition_refines_formPartition

example : Operation.ConstantOnFibers forgetFieldFailures forgetFieldFailures := by
  intro a b hab
  exact hab

example : Operation.FactorsThrough forgetFieldFailures forgetFieldFailures := by
  exact ⟨Operation.id formPartition, by simp⟩

private def identityFine : Operation fieldPartition fieldPartition :=
  Operation.id fieldPartition

#guard (Operation.firstFiberConflict forgetFieldFailures identityFine).isSome

example : ¬ Operation.ConstantOnFibers forgetFieldFailures identityFine := by
  intro h
  have bad := h (false, false) (false, true) rfl
  have impossible :
      (some (false, false) : Option (Bool × Bool)) ≠ some (false, true) := by
    decide
  exact impossible bad

end ArchiScriptTests.Resolution