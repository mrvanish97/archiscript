-- EXPECT: CONTRACT_AUDIT ArchiScriptBad.effectContract.admissibleEffect
-- ONLY_ERROR: CONTRACT_AUDIT
import ArchiScriptTests.ContractAudit
open ArchiScript ArchiScriptExamples
namespace ArchiScriptBad

def effectAlias := SimpleCone.model.reachEffect
def effectContract : CertifiedDeclaredArchitecture :=
  ArchiScriptTests.ContractAudit.certificate (fun _ _ _ => True) effectAlias
    (fun _ _ _ => trivial)
    (by intro c tuple; cases c; exact SimpleCone.effectReach tuple)
end ArchiScriptBad
#audit_archiscript
