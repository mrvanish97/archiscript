-- EXPECT: Fields missing: `route`
import ArchiScriptExamples.CyclicCone
open ArchiScript ArchiScriptExamples.CyclicCone
def noEntry : ArchitectureSignature.Term.CycleBoundary signature () where
  oneEntry := rfl
  nontrivial := by decide
