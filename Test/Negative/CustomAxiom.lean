-- EXPECT: AXIOM_AUDIT rejected ArchiScriptBad.smuggled: [ArchiScriptBad.postulate]
import ArchiScript.ProofAudit
namespace ArchiScriptBad
axiom postulate : False
theorem smuggled : True := False.elim postulate
end ArchiScriptBad
#audit_archiscript
