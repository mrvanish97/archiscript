import ArchiScript.Consequence

namespace ArchiScript.Verification

/-- Complete tuple differences, never a pairwise compatibility test. -/
def unexpected (all : List Tuple) (reach admissible : Tuple → Prop)
    [DecidablePred reach] [DecidablePred admissible] : List Tuple :=
  all.filter fun tuple => decide (reach tuple ∧ ¬ admissible tuple)

def missing (all : List Tuple) (reach admissible : Tuple → Prop)
    [DecidablePred reach] [DecidablePred admissible] : List Tuple :=
  all.filter fun tuple => decide (admissible tuple ∧ ¬ reach tuple)

theorem unexpected_witness {all : List Tuple} {reach admissible : Tuple → Prop}
    [DecidablePred reach] [DecidablePred admissible] {tuple}
    (h : tuple ∈ unexpected all reach admissible) : reach tuple ∧ ¬ admissible tuple :=
  of_decide_eq_true (List.mem_filter.mp h).2

theorem missing_witness {all : List Tuple} {reach admissible : Tuple → Prop}
    [DecidablePred reach] [DecidablePred admissible] {tuple}
    (h : tuple ∈ missing all reach admissible) : admissible tuple ∧ ¬ reach tuple :=
  of_decide_eq_true (List.mem_filter.mp h).2

def checkAgreement (all : List Tuple) (reach admissible : Tuple → Prop)
    [DecidablePred reach] [DecidablePred admissible] : Bool :=
  all.all fun tuple => decide (reach tuple ↔ admissible tuple)

/-- An executable verdict becomes proof only with exhaustive tuple enumeration
and decidability of both independently specified relations. -/
theorem checkAgreement_correct (all : List Tuple) (complete : ∀ t, t ∈ all)
    (reach admissible : Tuple → Prop) [DecidablePred reach] [DecidablePred admissible] :
    checkAgreement all reach admissible = true ↔ ∀ tuple, reach tuple ↔ admissible tuple := by
  simp only [checkAgreement, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h t => h t (complete t), fun h t _ => h t⟩

/-- This diagnostic uses the supplied upstream image, independently of the
admissible tuple list. It therefore retains orphaned incoming members. -/
def unpartnered (members : List Member) (tuples : List Tuple) (coordinate : Tuple → Member)
    (incoming : Member → Prop) (admissible : Tuple → Prop)
    [DecidableEq Member] [DecidablePred incoming] [DecidablePred admissible] : List Member :=
  members.filter fun member => decide (incoming member ∧
    ¬ ∃ tuple ∈ tuples, admissible tuple ∧ coordinate tuple = member)

theorem unpartnered_witness {members : List Member} {tuples : List Tuple}
    {coordinate : Tuple → Member} {incoming : Member → Prop} {admissible : Tuple → Prop}
    [DecidableEq Member] [DecidablePred incoming] [DecidablePred admissible]
    (complete : ∀ tuple, tuple ∈ tuples) {member}
    (h : member ∈ unpartnered members tuples coordinate incoming admissible) :
    incoming member ∧ ¬ ∃ tuple, admissible tuple ∧ coordinate tuple = member := by
  obtain ⟨supplied, noPartner⟩ := of_decide_eq_true (List.mem_filter.mp h).2
  refine ⟨supplied, ?_⟩
  rintro ⟨tuple, allowed, same⟩
  exact noPartner ⟨tuple, complete tuple, allowed, same⟩

end ArchiScript.Verification
