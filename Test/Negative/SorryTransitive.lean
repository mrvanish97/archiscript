-- EXPECT: AXIOM_AUDIT rejected ArchiScriptBad.transitive: [sorryAx]
import ArchiScript.ProofAudit
set_option warningAsError false
namespace ArchiScriptBad
private theorem hidden : False := by sorry
theorem transitive : True := False.elim hidden
end ArchiScriptBad
#audit_archiscript
