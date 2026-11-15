-- EXPECT: Fields missing
-- EXPECT: effectCoverage
import ArchiScriptExamples.SharedTargets

open ArchiScript ArchiScriptExamples.SharedTargets

def skippedEffectCoverage : CertifiedDeclaredArchitecture where
  model := equalImages.model
  causeNonempty := equalImages.causeNonempty
  inputs := equalImages.inputs
  inputSources := equalImages.inputSources
  cones := equalImages.cones
  boundariesComplete := equalImages.boundariesComplete
