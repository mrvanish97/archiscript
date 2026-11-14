-- EXPECT: Tactic `contradiction` failed
import ArchiScriptTests.SemanticFoundation
open ArchiScript ArchiScriptTests.SemanticFoundation
def overlap : SemanticSplit root where
  Index := Bool
  indices := [false, true]
  indices_complete := by intro b; cases b <;> simp
  indexNonempty := ⟨false⟩
  indexDecidableEq := inferInstance
  children := fun _ => root
  within := fun _ _ h => h
  covers := fun _ h => ⟨false, h⟩
  disjoint := by intro i j different x h; contradiction
