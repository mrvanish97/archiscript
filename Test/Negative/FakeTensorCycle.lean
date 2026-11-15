-- EXPECT: Application type mismatch
import ArchiScriptExamples.SimpleCone
open ArchiScript ArchiScriptExamples.SimpleCone
def f : Operation bit bit := Operation.id bit
def h : Operation (bit.tensor bit) bit := ⟨fun pair => some pair.1⟩
#check h.comp f
