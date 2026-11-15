import ArchiScriptTests.Provenance
import ArchiScriptTests.TensorVerification

/-! Draft countermodels: structural grounding does not establish a proposed
contract. These test the actual typed input predicates, without claiming a
complete architecture certificate for the surrounding fixture. -/
namespace ArchiScriptTests.ContractCoverage
open ArchiScript
open ArchiScriptTests.Provenance

abbrev Triple := Bool × (Bool × Bool)

def inputContract (predicate : Triple → Prop) (g : signature.Generator)
    (_ : signature.Occurrence (signature.input g)) : (signature.input g).vdp.MemberIndex → Prop :=
  match g with
  | false => predicate
  | true => fun _ => True

abbrev proposed (predicate : Triple → Prop) : DeclaredArchitecture :=
  { independentModel with admissibleInput := inputContract predicate }

theorem evaluation (predicate : Triple → Prop) (w : signature.World) {s}
    (t : signature.Occurrence s) :
    (proposed predicate).evaluate w t = independentModel.evaluate w t :=
  independentModel.evaluate_inputContract (inputContract predicate) w t

theorem full_reach (predicate : Triple → Prop) (tuple : Triple) :
    (proposed predicate).reachInput false good tuple :=
  ⟨independentWorld tuple, trivial,
    (evaluation predicate _ good).trans (independent_evaluation tuple), trivial⟩

theorem supplied (predicate : Triple → Prop) (tuple : Triple)
    (i : (signature.input false).Position) :
    (proposed predicate).incoming good i ((signature.input false).coordinate tuple i) :=
  ⟨independentWorld tuple, trivial,
    (show (proposed predicate).Evaluates (independentWorld tuple) good tuple from
      (evaluation predicate _ good).trans (independent_evaluation tuple)).supplier i⟩

theorem all_sources (predicate : Triple → Prop) (g : signature.Generator) :
    (proposed predicate).InputSources g := by
  cases g with
  | false =>
    apply DeclaredArchitecture.InputSources.grounded
    intro i
    exact ⟨good.supplier i,
      (show good.RootCoherent from ⟨rfl, rfl, rfl⟩).supplier i⟩
  | true => exact .grounded (fun _ => ⟨root .one false, rfl⟩)

def narrow (tuple : Triple) : Prop := tuple = (false, false, false)

theorem orphan_incoming : (proposed narrow).incoming good (.inl ()) true :=
  supplied narrow (true, false, false) (.inl ())

theorem orphan_has_no_partner : ¬ ∃ tuple,
    (proposed narrow).admissibleInput false good tuple ∧
      (signature.input false).coordinate tuple (.inl ()) = true := by
  rintro ⟨tuple, rfl, impossible⟩
  cases impossible

theorem orphan_invalid : ¬ (proposed narrow).InputValid false good := by
  intro valid
  exact orphan_has_no_partner ((valid.2 (.inl ()) true).mp orphan_incoming)

theorem orphan_not_unreachable : ¬ (proposed narrow).InputStatus false good := by
  intro status
  cases status with
  | verified valid _ => exact orphan_invalid valid
  | unreachable empty _ _ => exact empty (.inl ()) true orphan_incoming

abbrev parity := TensorVerification.parity

-- Unary and pair projections of this contract are full; the full relation is not.
theorem parity_projections :
    (∀ a b : Bool, ∃ c : Bool, parity (a, b, c)) ∧
    (∀ a c : Bool, ∃ b : Bool, parity (a, b, c)) ∧
    (∀ b c : Bool, ∃ a : Bool, parity (a, b, c)) :=
  ⟨TensorVerification.pairwise_is_insufficient.1,
    TensorVerification.pairwise_is_insufficient.2.1,
    TensorVerification.pairwise_is_insufficient.2.2.1⟩

theorem parity_unary_projection (i : (signature.input false).Position) (member : Bool) :
    ∃ tuple, parity tuple ∧ (signature.input false).coordinate tuple i = member := by
  cases i with
  | inl i =>
    cases i
    exact ⟨(member, false, member), by cases member <;> rfl, rfl⟩
  | inr i => cases i with
    | inl i =>
      cases i
      exact ⟨(false, member, member), by cases member <;> rfl, rfl⟩
    | inr i =>
      cases i
      exact ⟨(member, false, member), by cases member <;> rfl, rfl⟩

theorem parity_invalid : ¬ (proposed parity).InputValid false good := by
  intro valid
  exact TensorVerification.pairwise_is_insufficient.2.2.2
    ((valid.1 (false, false, true)).mp (full_reach parity _))

theorem parity_status_rejected : ¬ (proposed parity).InputStatus false good := by
  intro status
  cases status with
  | verified valid _ => exact parity_invalid valid
  | unreachable empty _ _ => exact empty (.inl ()) false (supplied parity (false, false, false) _)

-- A true-only right supplier keeps false in its VDP, but cannot supply it.
open ArchiScriptExamples.CorrelatedJoin in
abbrev constantModel := model (fun _ => true)
open ArchiScriptExamples.CorrelatedJoin in
abbrev constantInput := joinInput (fun _ => true)
abbrev invented : DeclaredArchitecture :=
  { constantModel with admissibleInput := fun _ _ _ => True }

theorem invented_projection : ∃ tuple,
    invented.admissibleInput .join constantInput tuple ∧
      (invented.S.input .join).coordinate tuple (.inr ()) = false :=
  ⟨(false, false), trivial, rfl⟩

theorem invented_not_incoming : ¬ invented.incoming constantInput (.inr ()) false := by
  rintro ⟨w, _, supplied⟩
  have same := constantModel.evaluate_inputContract (fun _ _ _ => True) w
    (constantInput.supplier (.inr ()))
  have actual := ArchiScriptExamples.CorrelatedJoin.evaluation (fun _ => true) w
    (constantInput.supplier (.inr ()))
  have impossible : (true : Bool) = false := Option.some.inj ((same.trans actual).symm.trans supplied)
  cases impossible

theorem invented_invalid : ¬ invented.InputValid .join constantInput := by
  intro valid
  exact invented_not_incoming ((valid.2 (.inr ()) false).mpr invented_projection)

theorem invented_status_rejected : ¬ invented.InputStatus .join constantInput := by
  intro status
  cases status with
  | verified valid _ => exact invented_invalid valid
  | unreachable empty _ _ =>
    apply empty (.inr ()) true
    refine ⟨(fun _ _ => false), trivial, ?_⟩
    exact (constantModel.evaluate_inputContract (fun _ _ _ => True) _ _).trans
      (ArchiScriptExamples.CorrelatedJoin.evaluation (fun _ => true) _ _)

end ArchiScriptTests.ContractCoverage
