-- EXPECT: Fields missing: `inputSources`
-- ONLY_ERROR: Fields missing: `inputSources`
import ArchiScriptExamples.SimpleCone
open ArchiScript ArchiScriptExamples.SimpleCone

-- Checking complete input terms cannot replace per-declared-generator coverage.
def skipped : CertifiedDeclaredArchitecture where
  model := model
  causeNonempty := certified.causeNonempty
  effectCoverage := certified.effectCoverage
  inputs := certified.inputs
  cones := certified.cones
  boundariesComplete := certified.boundariesComplete
