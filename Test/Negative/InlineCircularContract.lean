-- EXPECT: CONTRACT_AUDIT ArchiScriptBad.inlineContract.admissibleInput
-- ONLY_ERROR: CONTRACT_AUDIT
import ArchiScriptTests.ContractAudit
open ArchiScript ArchiScriptExamples
namespace ArchiScriptBad

def inlineContract : CertifiedDeclaredArchitecture :=
  ArchiScriptTests.ContractAudit.certificate
    (fun g t value => (fun relation => relation g t value) SimpleCone.model.reachInput)
    (fun _ _ => True)
    (by intro g t b; cases g; exact SimpleCone.inputReach t b) (fun _ _ => trivial)
end ArchiScriptBad
#audit_archiscript
