import ArchiScriptTests.SourceCoverage

namespace ArchiScriptTests.UngroundedCycle
open ArchiScript ArchiScriptTests.SourceCoverage
inductive Arrow where | forward | back deriving DecidableEq
abbrev signature : ArchitectureSignature := {
  SourceCoverage.signature with
  Generator := Arrow
  generatorDecidableEq := inferInstance
  generators := [.forward, .back]
  generators_complete := by intro g; cases g <;> simp
  input | .forward => .node .y | .back => .node .effect
  output | .forward => .effect | .back => .y
  operation | .forward => Operation.id bit | .back => Operation.id bit
  localFactor := by
    intro g; cases g
    · exact ⟨.y, List.mem_cons_self, rfl⟩
    · exact ⟨.effect, List.mem_cons_self, rfl⟩ }

def boundary : ArchitectureSignature.Term.CycleBoundary signature .y where
  route := ArchitectureSignature.Term.operation (S := signature)
    (Hole := fun n => PLift (Port.y = n)) .back
    (ArchitectureSignature.Term.operation (S := signature)
      (Hole := fun n => PLift (Port.y = n)) .forward
      (ArchitectureSignature.Term.hole (S := signature)
        (Hole := fun n => PLift (Port.y = n)) .y ⟨rfl⟩))
  oneEntry := rfl
  nontrivial := by decide
abbrev marked : signature.Markers
  | .y => some boundary
  | .x | .effect => none
abbrev basis : signature.ProvenanceAnalysis marked := derive_provenance([false], 0)
abbrev model : DeclaredArchitecture where
  signature := signature
  boundary := fun _ => True
  boundaryNonempty := ⟨fun _ _ => false, trivial⟩
  context := fun _ _ _ => True
  admissibleInput := fun _ _ _ => False
  cyclicBoundary := marked
  effectAnalysis := basis
  effectContext := fun _ _ _ => True
  admissibleEffect := fun _ _ => False

theorem basis_valid : basis.Valid := ⟨by intro c; cases c; simp, by decide⟩

-- Reference completeness, not the existence of a graph cycle, determines
-- whether any finite rooted producer exists in the component.
theorem ungrounded (n : Port) (away : n ≠ .x)
    (t : signature.Occurrence (.node n)) (coherent : t.RootCoherent) : False := by
  have produced := basis.complete basis_valid () t coherent
  cases n with
  | x => exact away rfl
  | y => change _ ∈ [] at produced; cases produced
  | effect => change _ ∈ [] at produced; cases produced

theorem source_unreachable (g : Arrow) : model.InputSources g := by
  apply DeclaredArchitecture.InputSources.unreachable
  intro i member
  cases g <;> cases i
  all_goals
    rintro ⟨t, coherent, _⟩
    exact ungrounded _ (by decide) t coherent

theorem unobservable : model.NoObservableEffect () :=
  ⟨fun i => Empty.elim i, fun _ impossible => impossible⟩

@[archiscript_certificate] def certified : CertifiedDeclaredArchitecture where
  model := model
  causeNonempty := ⟨()⟩
  effectCoverage := basis_valid
  inputSources := source_unreachable
  inputs := by
    intro g t context
    cases g
    · exact False.elim (ungrounded .y (by decide) t context.1)
    · exact False.elim (ungrounded .effect (by decide) t context.1)
  cones := by intro c; cases c; exact .unobservable unobservable
  boundariesComplete := by intro c n _; cases c; exact Or.inl unobservable

example : signature.effectNodes marked () = [.y] := rfl
example : signature.effectCoordinates basis () = [] := rfl
example : ¬ model.reachEffect () () := unobservable.not_reachable ()
example : ¬ basis.SourcesPresent .forward := by decide
example : ¬ basis.SourcesPresent .back := by decide

end ArchiScriptTests.UngroundedCycle
