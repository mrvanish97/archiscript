import ArchiScriptExamples.Coproduct

namespace ArchiScriptTests.Coproduct
open ArchiScript ArchiScriptExamples.Coproduct

#guard entryPartition.memberIndices.length == 4
#guard entryPartition.classify (.inl ⟨"/"⟩) == Sum.inl BrowserMember.root
#guard entryPartition.classify (.inr ⟨["status"]⟩) == Sum.inr CliMember.nonempty

example :
    handleEntry.comp (Operation.coproductInl browserPartition cliPartition) =
      handleBrowser :=
  Operation.copair_inl handleBrowser handleCli

example :
    handleEntry.comp (Operation.coproductInr browserPartition cliPartition) =
      handleCli :=
  Operation.copair_inr handleBrowser handleCli

example :
    Operation.coproductMap
      (Operation.id browserPartition)
      (Operation.id cliPartition) =
      Operation.id entryPartition :=
  Operation.coproductMap_id browserPartition cliPartition

example :
    Operation.copair handleBrowser handleCli = handleEntry := rfl

end ArchiScriptTests.Coproduct
