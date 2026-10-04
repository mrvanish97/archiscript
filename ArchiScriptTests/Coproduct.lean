import ArchiScriptExamples.Coproduct

namespace ArchiScriptTests.Coproduct
open ArchiScript ArchiScriptExamples.Coproduct

#guard commandPartition.memberIndices.length == 5
#guard commandPartition.classify (.inl .create) == Sum.inl UserCommand.create
#guard commandPartition.classify (.inr .expire) == Sum.inr SystemCommand.expire

example :
    handleCommand.comp
      (Operation.coprodInl userCommandPartition systemCommandPartition) =
      handleUser :=
  Operation.copair_inl handleUser handleSystem

example :
    handleCommand.comp
      (Operation.coprodInr userCommandPartition systemCommandPartition) =
      handleSystem :=
  Operation.copair_inr handleUser handleSystem

example :
    Operation.coprodMap
      (Operation.id userCommandPartition)
      (Operation.id systemCommandPartition) =
      Operation.id commandPartition :=
  Operation.coprodMap_id userCommandPartition systemCommandPartition

example :
    Operation.copair handleUser handleSystem = handleCommand := rfl

end ArchiScriptTests.Coproduct
