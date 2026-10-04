import ArchiScript.Resolution
import ArchiScriptExamples.FormInput

namespace ArchiScriptTests.Resolution
open ArchiScript ArchiScriptExamples.FormInput

private def forgetMap : fieldPartition.MemberIndex → formPartition.MemberIndex :=
  fun i => i.1 && i.2

example : fieldPartition.RefinesVia formPartition forgetMap := by
  refine ⟨rfl, ?_⟩
  intro i x hx
  change fieldPartition.classify x = i at hx
  change formPartition.classify x = forgetMap i
  cases hx
  rfl

example : Function.Surjective forgetMap :=
  Partition.coarseningMap_surjective (by
    refine ⟨rfl, ?_⟩
    intro i x hx
    change fieldPartition.classify x = i at hx
    change formPartition.classify x = forgetMap i
    cases hx
    rfl)

private def coarseOp : Operation fieldPartition formPartition :=
  Partition.coarseningOperation forgetMap

example : coarseOp = forgetFieldFailures := by
  apply Operation.ext
  intro i
  rfl

example : Operation.ConstantOnFibers coarseOp forgetFieldFailures := by
  intro a b hab
  simpa [coarseOp, Partition.coarseningOperation, forgetFieldFailures] using hab

example : Operation.FactorsThrough coarseOp forgetFieldFailures := by
  exact ⟨Operation.id formPartition, by simp [coarseOp]⟩

private def identityFine : Operation fieldPartition fieldPartition :=
  Operation.id fieldPartition

#guard (Operation.firstFiberConflict coarseOp identityFine).isSome

example : ¬ Operation.ConstantOnFibers coarseOp identityFine := by
  intro h
  have bad := h (false, false) (false, true) rfl
  simp [coarseOp, Partition.coarseningOperation, identityFine, Operation.id] at bad

end ArchiScriptTests.Resolution
