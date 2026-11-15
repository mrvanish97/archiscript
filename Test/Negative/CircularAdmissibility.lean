-- EXPECT: CONTRACT_AUDIT
import ArchiScriptExamples.SimpleCone
open ArchiScript ArchiScriptExamples.SimpleCone
@[archiscript_contract] def ArchiScriptBad.circular (b : Bool) : Prop :=
  model.reachInput () (.cause () ()) b
#audit_archiscript
