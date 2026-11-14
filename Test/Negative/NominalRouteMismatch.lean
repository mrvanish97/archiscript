-- EXPECT: Application type mismatch
import ArchiScriptExamples.SimpleCone
open ArchiScript ArchiScriptExamples.SimpleCone
abbrev G := signature.generatorsInventory
def illicit : Expression G (Inputs.node Port.input) (Inputs.node Port.output) :=
  Expression.step (G := G) ()
    (Expression.step (G := G) () (Expression.identity (G := G) (Inputs.node Port.input)))
