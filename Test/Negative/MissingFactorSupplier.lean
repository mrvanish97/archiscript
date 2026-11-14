-- EXPECT: Application type mismatch
import ArchiScriptExamples.CorrelatedJoin
open ArchiScript ArchiScriptExamples.CorrelatedJoin
#check ArchitectureSignature.Term.operation (S := signature id) Arrow.join (leftTrace id)
