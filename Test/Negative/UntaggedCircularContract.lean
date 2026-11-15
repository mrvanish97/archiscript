-- EXPECT: CONTRACT_AUDIT ArchiScriptBad.untagged.admissibleInput
-- ONLY_ERROR: CONTRACT_AUDIT
import ArchiScriptTests.ContractAudit
open ArchiScript ArchiScriptExamples
namespace ArchiScriptBad

def untaggedPredicate := SimpleCone.model.reachInput
abbrev firstAlias := untaggedPredicate
abbrev secondAlias := firstAlias
-- This really is a complete, mathematically valid certificate. No tags opt it
-- into the contract audit; the installed fields are inspected automatically.
def untagged : CertifiedDeclaredArchitecture :=
  ArchiScriptTests.ContractAudit.certificate secondAlias (fun _ _ => True)
    (by intro g t b; cases g; exact SimpleCone.inputReach t b) (fun _ _ => trivial)
end ArchiScriptBad
#audit_archiscript
