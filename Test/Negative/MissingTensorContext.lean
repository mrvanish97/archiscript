-- EXPECT: Fields missing: `inputs`
import ArchiScriptExamples.SimpleCone
open ArchiScript ArchiScriptExamples.SimpleCone
def skipped : CertifiedDeclaredArchitecture where
  model := model
  causeNonempty := certified.causeNonempty
  inputSources := certified.inputSources
  cones := certified.cones
  boundariesComplete := certified.boundariesComplete
  effectCoverage := certified.effectCoverage
