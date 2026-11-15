-- EXPECT: Tactic `rfl` failed
-- EXPECT: ⊢ true = false
-- ONLY_ERROR: Tactic `rfl` failed
import ArchiScript.Consequence
import ArchiScriptTests.RootCoherence

open ArchiScriptTests.RootCoherence

-- Reuse the independent regression graph, never the root/example aggregators.
-- The raw tensor is well typed, but its second root is not the designated origin.
example : model.isInputContext .directJoin mixedInput := by
  apply (model.isInputContext_iff_coherent .directJoin mixedInput).mpr
  change (false = false) ∧ (true = false)
  constructor
  · rfl
  · rfl
