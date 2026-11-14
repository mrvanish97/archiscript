-- EXPECT: AXIOM_AUDIT rejected ArchiScriptBad.direct: [sorryAx]
import ArchiScript.ProofAudit
set_option warningAsError false
namespace ArchiScriptBad
theorem direct : False := by sorry
end ArchiScriptBad
#audit_archiscript
