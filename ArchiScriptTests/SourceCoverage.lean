import ArchiScript.Consequence
import ArchiScript.ProofAudit

namespace ArchiScriptTests.SourceCoverage
open ArchiScript
abbrev bit : VDP := Partition.closed Bool "Boolean"
  ⟨[false, true], by intro b; cases b <;> simp⟩ ⟨false⟩
inductive Port where | x | y | effect deriving DecidableEq
abbrev signature : ArchitectureSignature where
  Node := Port
  nodeDecidableEq := inferInstance
  nodes := [.x, .y, .effect]
  nodes_complete := by intro n; cases n <;> simp
  nodes_nodup := by decide
  object := fun _ => bit
  domains := [⟨Bool, bit.members false⟩, ⟨Bool, bit.members true⟩]
  memberDeclared := by intro n i; cases i <;> simp
  splits := []
  Cause := Unit
  causeDecidableEq := inferInstance
  causes := [()]
  causes_complete := by intro c; cases c; simp
  causes_nodup := by simp
  RootInstance := Bool
  rootDecidableEq := inferInstance
  origin := fun _ => false
  start := fun _ => .x
  owner := fun _ => ()
  start_owner := fun _ => rfl
  Generator := Unit
  generatorDecidableEq := inferInstance
  generators := [()]
  generators_complete := by intro g; cases g; simp
  input := fun _ => .tensor (.node .x) (.node .y)
  output := fun _ => .effect
  operation := fun _ => ⟨fun pair => some pair.1⟩
  localFactor := fun _ => ⟨.x, by simp [Inputs.nodes], rfl⟩
abbrev basis : signature.ProvenanceAnalysis (fun _ => none) := derive_provenance([false, true], 0)
abbrev model : DeclaredArchitecture where
  signature := signature
  boundary := fun _ => True
  boundaryNonempty := ⟨fun _ _ => false, trivial⟩
  context := fun _ _ _ => True
  admissibleInput := fun _ _ _ => True
  cyclicBoundary := fun _ => none
  effectAnalysis := basis
  effectContext := fun _ _ _ => True
  admissibleEffect := fun _ _ => True

theorem noY (t : signature.Occurrence (.node .y)) : False := by cases t; rename_i impossible; exact Empty.elim impossible

theorem basis_valid : basis.Valid :=
  ⟨by intro c; cases c; simp, by decide⟩

-- There is a genuine independently incoming X, despite the missing Y.
abbrev xRoot : signature.Occurrence (.node .x) :=
  ArchitectureSignature.Term.cause (S := signature) () false

theorem suppliedX : model.supplierImage .x false :=
  ⟨xRoot, rfl, (fun _ _ => false), trivial, rfl⟩

theorem missing_sources_rejected : ¬ model.InputSources () := by
  intro status
  cases status with
  | grounded suppliers =>
    obtain ⟨t, _⟩ := suppliers (.inr ())
    exact noY t
  | unreachable empty => exact empty (.inl ()) false suppliedX

theorem no_certificate (certificate : CertifiedDeclaredArchitecture)
    (same : certificate.model = model) : False := by
  have sources : ∀ g : model.S.Generator, model.InputSources g :=
    Eq.mp (congrArg (fun m : DeclaredArchitecture => ∀ g : m.S.Generator, m.InputSources g) same)
      certificate.inputSources
  exact missing_sources_rejected (sources ())

example : signature.effectNodes (fun _ => none) () = [.effect] := rfl
example : signature.effectCoordinates basis () = [] := rfl
example : model.effect () = .unit := rfl

theorem unit_not_reached : ¬ model.reachEffect () () := by
  rintro ⟨_, _, _, _, _, _, _, ⟨i⟩⟩
  exact Empty.elim i

theorem no_observable_cone : ¬ model.ConeValid () := by
  rintro ⟨⟨i⟩, _⟩
  exact Empty.elim i

-- Changing the Effect contract cannot conceal the input fault.
abbrev noEffectModel : DeclaredArchitecture :=
  { model with admissibleEffect := fun _ _ => False }
example : noEffectModel.NoObservableEffect () :=
  ⟨fun i => Empty.elim i, fun _ impossible => impossible⟩
example : ¬ noEffectModel.InputSources () := by
  intro status
  cases status with
  | grounded suppliers => obtain ⟨t, _⟩ := suppliers (.inr ()); exact noY t
  | unreachable empty =>
    exact empty (.inl ()) false ⟨xRoot, rfl, (fun _ _ => false), trivial, rfl⟩

-- A genuinely source-only event is representable without inventing an Effect.
abbrev sourceOnlySignature : ArchitectureSignature := {
  signature with
  Generator := Empty
  generatorDecidableEq := inferInstance
  generators := []
  generators_complete := by intro g; cases g
  input := fun g => nomatch g
  output := fun g => nomatch g
  operation := fun g => nomatch g
  localFactor := by intro g; cases g }
abbrev sourceOnlyBasis : sourceOnlySignature.ProvenanceAnalysis (fun _ => none) :=
  derive_provenance([false], 0)
abbrev sourceOnlyModel : DeclaredArchitecture where
  signature := sourceOnlySignature
  boundary := fun _ => True
  boundaryNonempty := ⟨fun _ _ => false, trivial⟩
  context := fun g => nomatch g
  admissibleInput := fun g => nomatch g
  cyclicBoundary := fun _ => none
  effectAnalysis := sourceOnlyBasis
  effectContext := fun _ _ _ => True
  admissibleEffect := fun _ _ => False

theorem sourceOnly_unobservable : sourceOnlyModel.NoObservableEffect () :=
  ⟨fun i => Empty.elim i, fun _ impossible => impossible⟩

@[archiscript_certificate] def sourceOnly : CertifiedDeclaredArchitecture where
  model := sourceOnlyModel
  causeNonempty := ⟨()⟩
  effectCoverage := ⟨by intro c; cases c; simp, by decide⟩
  inputSources := by intro g; cases g
  inputs := by intro g; cases g
  cones := by intro c; cases c; exact .unobservable sourceOnly_unobservable
  boundariesComplete := by intro c n _; cases c; exact Or.inl sourceOnly_unobservable

example : ¬ sourceOnly.model.reachEffect () () := sourceOnly_unobservable.not_reachable ()

-- Only the canonical origin needs enumeration, even for an infinite root type.
abbrev infiniteRootSignature : ArchitectureSignature := {
  signature with
  RootInstance := Nat
  rootDecidableEq := inferInstance
  origin := fun _ => 0 }
abbrev infiniteRootBasis : infiniteRootSignature.ProvenanceAnalysis (fun _ => none) :=
  derive_provenance([0], 0)
theorem infiniteRootBasis_valid : infiniteRootBasis.Valid :=
  ⟨by intro c; cases c; simp, by decide⟩

end ArchiScriptTests.SourceCoverage
