-- EXPECT: Tactic `decide` proved that the proposition
-- ONLY_ERROR: Tactic `decide` proved that the proposition
import ArchiScriptTests.SourceCoverage
open ArchiScript ArchiScriptTests.SourceCoverage

-- The declared join has an incoming X but no coherent Y supplier.
example : model.InputSources () :=
  model.inputSources_of_catalog basis_valid () (by decide)
