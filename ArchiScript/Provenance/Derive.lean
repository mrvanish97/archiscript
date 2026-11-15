import ArchiScript.Provenance
import Lean

/-! An optional elaboration helper for caching derived data. It produces no
domain claims or proofs; `ProvenanceAnalysis.Valid` remains a kernel obligation. -/
namespace ArchiScript
open Lean Elab Term Meta

elab "derive_provenance(" roots:term "," fuel:term ")" : term <= expectedType => do
  let expected ← whnf expectedType
  unless expected.isAppOf ``ArchitectureSignature.ProvenanceAnalysis do
    throwError "derive_provenance expects a ProvenanceAnalysis type"
  let arguments := expected.getAppArgs
  let signature := arguments[0]!
  let marked := arguments[1]!
  let rootType := mkApp (mkConst ``ArchitectureSignature.RootInstance) signature
  let roots ← elabTerm roots (some (mkApp (mkConst ``List [Level.zero]) rootType))
  let fuel ← elabTerm fuel (some (mkConst ``Nat))
  synthesizeSyntheticMVarsNoPostponing
  let roots ← instantiateMVars roots
  let fuel ← instantiateMVars fuel
  let fuel ← withTransparency .all (whnf fuel)
  let .lit (.natVal steps) := fuel | throwError "derive_provenance requires concrete finite fuel"
  let entries ← mkAppM ``ArchitectureSignature.provenanceEntries
    #[signature, marked, roots, mkNatLit 0]
  let mut entries ← withTransparency .all (reduce (← instantiateMVars entries))
  for _ in [:steps] do
    let next ← mkAppM ``ArchitectureSignature.extendProvenanceEntries #[signature, marked, entries]
    entries ← withTransparency .all (reduce (← instantiateMVars next))
  return mkAppN (mkConst ``ArchitectureSignature.ProvenanceAnalysis.mk)
    #[signature, marked, roots, entries]

end ArchiScript
