-- EXPECT: CONTRACT_AUDIT ArchiScriptBad.opaqueCertificate.admissibleInput
-- ONLY_ERROR: CONTRACT_AUDIT
import ArchiScriptTests.ContractAudit
open ArchiScript ArchiScriptExamples
namespace ArchiScriptBad

opaque opaqueAlias : { input : ArchiScriptTests.ContractAudit.InputContract //
    ∀ g t b, input g t b } :=
  ⟨SimpleCone.model.reachInput, by intro g t b; cases g; exact SimpleCone.inputReach t b⟩
opaque opaqueCertificate : CertifiedDeclaredArchitecture :=
  ArchiScriptTests.ContractAudit.certificate opaqueAlias.val (fun _ _ => True)
    opaqueAlias.property (fun _ _ => trivial)
end ArchiScriptBad
#audit_archiscript
