import ArchiScript.Provenance.Derive

/-! Development/release tooling. This module is intentionally not imported by
the public calculus. The audit inspects compiled transitive dependencies. -/
namespace ArchiScript.ProofAudit
open Lean Elab Command Meta

initialize certificateAttribute : TagAttribute ←
  registerTagAttribute `archiscript_certificate "A closed concrete architecture certificate to audit"

initialize contractAttribute : TagAttribute ←
  registerTagAttribute `archiscript_contract "An independently authored admissibility contract"

private def approvedAxiom (name : Name) : Bool :=
  [``propext, ``Classical.choice, ``Quot.sound].contains name

private def projectDeclaration (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => true
  | some index => (env.header.moduleNames[index]!).toString.startsWith "ArchiScript"

private def semanticDependency (name : Name) : Bool :=
  ["ArchiScript.DeclaredArchitecture.evaluate", "ArchiScript.DeclaredArchitecture.reachInput",
   "ArchiScript.DeclaredArchitecture.reachEffect", "ArchiScript.DeclaredArchitecture.incoming",
   "ArchiScript.DeclaredArchitecture.effectIncoming"].contains name.toString

private partial def contractDependencies (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : Bool :=
  match todo with
  | [] => false
  | name :: rest =>
    if semanticDependency name then true
    else if seen.contains name then contractDependencies env rest seen
    else
      let used := match env.find? name with
        | some info => match info.value? true with
          | some value => value.getUsedConstants.toList
          | none => []
        | none => []
      contractDependencies env (used ++ rest) (seen.insert name)

/-- Inspect the actual closed record, including opaque aliases. An unavailable
or conditional implementation is not silently accepted as an audited contract. -/
private partial def recordValue (env : Environment) (record : Name) (value : Expr) : MetaM Expr := do
  let rec expose (fuel : Nat) (value : Expr) : MetaM Expr := do
    if fuel = 0 then throwError "CONTRACT_AUDIT could not expose {record}"
    let value ← withTransparency .all (whnf value)
    if value.isAppOf (record ++ `mk) then return value
    match value with
    | .proj parent field input =>
      let input ← recordValue env parent input
      expose (fuel - 1) (.proj parent field input)
    | _ =>
      if let .const name levels := value.getAppFn then
        if let some info := env.find? name then
          if let some body := info.value? true then
            let body := body.instantiateLevelParams info.levelParams levels
            return ← expose (fuel - 1) (mkAppN body value.getAppArgs)
      throwError "CONTRACT_AUDIT cannot inspect installed {record} contracts"
  expose 128 value

private def recordField (env : Environment) (record : Name) (value : Expr)
    (field : Name) : MetaM Expr := do
  let value ← recordValue env record value
  let fields := getStructureFields env record
  let some index := fields.findIdx? (· == field)
    | throwError "CONTRACT_AUDIT unknown field {record}.{field}"
  let arguments := value.getAppArgs
  let parameters := arguments.size - fields.size
  return arguments[parameters + index]!

private def installedContracts (env : Environment) (name : Name) (info : ConstantInfo) :
    CommandElabM Unit := do
  if info.type.isForall then return
  liftTermElabM do
    let type ← withTransparency .all (whnf info.type)
    let certificate := type.isConstOf `ArchiScript.CertifiedDeclaredArchitecture
    if !certificate && !type.isConstOf `ArchiScript.DeclaredArchitecture then return
    let value := mkConst name (info.levelParams.map mkLevelParam)
    let model ← if certificate then
      recordField env `ArchiScript.CertifiedDeclaredArchitecture value `model
      else pure value
    for field in [`admissibleInput, `admissibleEffect] do
      let contract ← recordField env `ArchiScript.DeclaredArchitecture model field
      if contractDependencies env contract.getUsedConstants.toList then
        logError m!"CONTRACT_AUDIT {name}.{field} depends on Reach/evaluation; independent evidence is absent"

/-- Audit all project declarations, including private and local ones, rather
than an author-selected certificate shortlist. JSON lines are machine readable.
Local warning suppression cannot conceal a dependency on `sorryAx`. -/
elab "#audit_archiscript" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if projectDeclaration env name then
      count := count + 1
      let axioms ← collectAxioms name
      let rejected := axioms.filter fun ax => !approvedAxiom ax
      if !rejected.isEmpty then
        logError m!"AXIOM_AUDIT rejected {name}: {rejected.toList}"
      if certificateAttribute.hasTag env name then
        if info.type.isForall then
          logError m!"CERTIFICATE_AUDIT conditional certificate {name} has unsupplied parameters"
        unless info.type.isConstOf `ArchiScript.CertifiedDeclaredArchitecture do
          logError m!"CERTIFICATE_AUDIT {name} does not have the closed certificate type"
      if contractAttribute.hasTag env name && contractDependencies env [name] then
        logError m!"CONTRACT_AUDIT {name} depends on Reach/evaluation; independent evidence is absent"
      installedContracts env name info
      logInfo <| Json.compress <| Json.mkObj [
        ("declaration", toJson name.toString),
        ("type", toJson (toString info.type)),
        ("axioms", toJson (axioms.map Name.toString))]
  logInfo m!"AXIOM_AUDIT checked {count} project declarations"

end ArchiScript.ProofAudit
