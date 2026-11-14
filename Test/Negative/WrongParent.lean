-- EXPECT: Tactic `rfl` failed
import ArchiScript.Subdomain
open ArchiScript
def wrong : Subdomain Bool where
  name := "false inside true"
  base := fun b => b = true
  parent := .predicate _
  meaning := fun b => b = false
  contained := by intro b h; cases h; rfl
  definition := .predicate _
  nonempty := ⟨false, rfl⟩
