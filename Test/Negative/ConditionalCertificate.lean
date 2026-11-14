-- EXPECT: conditional certificate
import ArchiScriptExamples.SimpleCone
open ArchiScript
@[archiscript_certificate] def ArchiScriptBad.conditional (missing : CertifiedDeclaredArchitecture) :
    CertifiedDeclaredArchitecture := missing
#audit_archiscript
