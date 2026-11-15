-- EXPECT: Tactic `decide` proved that the proposition
-- EXPECT: is false
-- ONLY_ERROR: Tactic `decide` proved that the proposition
import ArchiScriptTests.TerminalOccurrences
open ArchiScript ArchiScriptTests.TerminalOccurrences ArchiScriptExamples.SharedTargets

-- Same C and same values, but the second slot requires g/q provenance.
example : equalImages.model.EffectProvenance () collapsed := by
  intro i
  cases i with
  | inl i => cases i; rfl
  | inr i =>
    cases i with
    | inl i =>
      cases i
      change ProducerHistory.operation (2 : Fin 4) (.operation 0 (.cause () ())) =
        ProducerHistory.operation 3 (.operation 1 (.cause () ()))
      decide
    | inr impossible => exact Empty.elim impossible
