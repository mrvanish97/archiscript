import ArchiScriptExamples.SimpleCone

/-! A mathematically valid certificate factory used to exercise the independent
contract audit. Acceptance also requires #audit_archiscript: equality with Reach
alone does not establish independent authorship of a domain requirement. -/
namespace ArchiScriptTests.ContractAudit
open ArchiScript
open ArchiScriptExamples

abbrev InputContract := (g : SimpleCone.signature.Generator) →
  SimpleCone.signature.Occurrence (SimpleCone.signature.input g) → Bool → Prop
abbrev EffectContract := Unit → Bool × Unit → Prop

abbrev model (input : InputContract) (effect : EffectContract) : DeclaredArchitecture :=
  { SimpleCone.model with admissibleInput := input, admissibleEffect := effect }

theorem evaluation (input : InputContract) (effect : EffectContract)
    (w : SimpleCone.signature.World) {s} (t : SimpleCone.signature.Occurrence s) :
    (model input effect).Evaluates w t (s.assign (fun _ => w () ())) := by
  apply (model input effect).evaluate_of_assignment
  · intro c root; cases c; cases root; rfl
  · intro g; rfl
  · intro g t; trivial

theorem inputReach (input : InputContract) (effect : EffectContract)
    (t : SimpleCone.signature.Occurrence (.node .input)) (b : Bool) :
    (model input effect).reachInput () t b :=
  ⟨SimpleCone.world b, trivial, evaluation input effect _ t, trivial⟩

theorem effectReach (input : InputContract) (effect : EffectContract) (tuple : Bool × Unit) :
    (model input effect).reachEffect () tuple := by
  rcases tuple with ⟨b, u⟩; cases u
  exact ⟨SimpleCone.terminal, SimpleCone.terminalOrigin, SimpleCone.terminalProvenance,
    SimpleCone.world b, trivial, evaluation input effect _ _, trivial⟩

def certificate (input : InputContract) (effect : EffectContract)
    (allInput : ∀ g t b, input g t b) (allEffect : ∀ c tuple, effect c tuple) :
    CertifiedDeclaredArchitecture where
  model := model input effect
  causeNonempty := SimpleCone.certified.causeNonempty
  effectCoverage := SimpleCone.certified.effectCoverage
  inputs := by
    intro g t _; cases g
    refine .verified ⟨?_, ?_⟩ ⟨false, inputReach input effect t false⟩
    · intro b; exact ⟨fun _ => allInput () t b, fun _ => inputReach input effect t b⟩
    · intro i b; cases i
      exact ⟨fun _ => ⟨b, allInput () t b, rfl⟩,
        fun _ => ⟨SimpleCone.world b, trivial, (evaluation input effect _ t).supplier ()⟩⟩
  cones := by
    intro c; cases c
    refine ⟨by exact of_decide_eq_true rfl, ⟨(false, ()), effectReach input effect _⟩, ?_, ?_⟩
    · intro tuple
      exact ⟨fun _ => allEffect () tuple, fun _ => effectReach input effect tuple⟩
    · intro i b; cases i with
      | inl i =>
        cases i
        exact ⟨fun _ => ⟨(b, ()), allEffect () _, rfl⟩,
          fun _ => ⟨SimpleCone.terminal.supplier (.inl ()), SimpleCone.terminalOrigin _, rfl,
            SimpleCone.world b, trivial, evaluation input effect _ _⟩⟩
      | inr impossible => exact Empty.elim impossible
  boundariesComplete := SimpleCone.certified.boundariesComplete

@[archiscript_certificate] def independent : CertifiedDeclaredArchitecture :=
  certificate (fun _ _ _ => True) (fun _ _ => True) (fun _ _ _ => trivial) (fun _ _ => trivial)

end ArchiScriptTests.ContractAudit
