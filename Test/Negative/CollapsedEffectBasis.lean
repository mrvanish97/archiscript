-- EXPECT: Tactic `decide` proved that the proposition
-- EXPECT: is false
-- ONLY_ERROR: Tactic `decide` proved that the proposition
import ArchiScriptExamples.SharedTargets
open ArchiScript ArchiScriptExamples.SharedTargets

-- Drop only g's terminal result while keeping the whole original graph.
abbrev missingProducer : (signature 0 id).ProvenanceAnalysis (fun _ => none) :=
  { baseBasis id with entries := (baseBasis id).entries.filter fun entry =>
      entry.2.1.val != 3 || entry.2.2 == (leftC 0 id).history }
example : missingProducer.Closed := by decide
