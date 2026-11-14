-- EXPECT: Fields missing: `covers`
import ArchiScriptTests.SemanticFoundation
open ArchiScript ArchiScriptTests.SemanticFoundation
def unfinished : SemanticSplit root where
  Index := Bool
  indices := [false, true]
  indices_complete := by intro b; cases b <;> simp
  indexNonempty := ⟨false⟩
  indexDecidableEq := inferInstance
  children := firstTree.children
  within := firstTree.within
  disjoint := firstTree.disjoint
