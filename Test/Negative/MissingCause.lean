-- EXPECT: Fields missing
-- EXPECT: causeNonempty
import ArchiScriptExamples.SimpleCone

open ArchiScript ArchiScriptExamples.SimpleCone

def absentCauseEvidence : CertifiedDeclaredArchitecture where
  model := model
  inputs := certified.inputs
  cones := certified.cones
  boundariesComplete := certified.boundariesComplete
  effectCoverage := certified.effectCoverage
