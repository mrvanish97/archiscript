-- EXPECT: Application type mismatch
-- ONLY_ERROR: Application type mismatch
import ArchiScriptExamples.SharedTargetJoin
open ArchiScript ArchiScriptExamples.SharedTargetJoin

-- C cannot supply the two independent positions of the declared C tensor C.
def fake : signature.Occurrence (.node .result) :=
  ArchitectureSignature.Term.operation (S := signature) .join leftC
