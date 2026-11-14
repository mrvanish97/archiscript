-- EXPECT: Fields missing
-- EXPECT: terminalOccurrencesFaithful
import ArchiScriptTests.TerminalOccurrences

open ArchiScript ArchiScriptTests.TerminalOccurrences

def skippedTerminalIdentity : CertifiedDeclaredArchitecture where
  model := model
  causeNonempty := certified.causeNonempty
  inputs := certified.inputs
  cones := certified.cones
  boundariesComplete := certified.boundariesComplete
