-- EXPECT: Fields missing: `inputs`
import ArchiScriptExamples.SimpleCone
open ArchiScript ArchiScriptExamples.SimpleCone
def skipped : CertifiedDeclaredArchitecture where
  model := model
  causeNonempty := certified.causeNonempty
  cones := certified.cones
  boundariesComplete := certified.boundariesComplete
  effectCoverage := certified.effectCoverage
