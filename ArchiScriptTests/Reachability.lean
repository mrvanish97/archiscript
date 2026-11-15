import ArchiScriptExamples.CyclicCone

namespace ArchiScriptTests.Reachability
open ArchiScript

/-- The terminal image can remain unchanged while internal state still grows. -/
def delayed : Reachability.FiniteAnalysis (Fin 4) where
  states := [0, 1, 2, 3]
  complete := by intro n; have := n.isLt; simp; omega
  initial := fun s => s = 0
  step := fun s t => t.val = s.val + 1
  initialDecidable := inferInstance
  stepDecidable := inferInstance
  stateDecidableEq := inferInstance

#guard ((delayed.compute 0).filter fun s => s.val == 3) == []
#guard ((delayed.compute 1).filter fun s => s.val == 3) == []
#guard (delayed.certify 1).isNone
#guard (delayed.certify 2).isNone
#guard (delayed.certify 3).isSome

example : Reachability.Reach delayed.initial delayed.step (3 : Fin 4) := by
  have zero : Reachability.Reach delayed.initial delayed.step (0 : Fin 4) := .initial rfl
  have one : Reachability.Reach delayed.initial delayed.step (1 : Fin 4) := .next zero rfl
  have two : Reachability.Reach delayed.initial delayed.step (2 : Fin 4) := .next one rfl
  exact .next two rfl

private theorem list_bounded (xs : List Nat) : ∃ bound, ∀ n ∈ xs, n < bound := by
  induction xs with
  | nil => exact ⟨0, by intro n h; cases h⟩
  | cons head tail ih =>
    obtain ⟨bound, bounded⟩ := ih
    refine ⟨head + bound + 1, ?_⟩
    intro n hn
    rcases List.mem_cons.mp hn with same | hn
    · subst n; omega
    · have := bounded n hn; omega

/-- Finite member alphabets do not make unbounded occurrence histories finite. -/
theorem histories_are_not_enumerable : ¬ ∃ xs : List Nat, ∀ generation, generation ∈ xs := by
  rintro ⟨xs, complete⟩
  obtain ⟨bound, bounded⟩ := list_bounded xs
  have := bounded bound (complete bound)
  omega

example : ArchiScriptExamples.CyclicCone.signature.RootInstance = Unit := rfl

end ArchiScriptTests.Reachability
