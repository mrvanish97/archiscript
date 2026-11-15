-- EXPECT: Fields missing: `nonempty`
import ArchiScript.Subdomain
open ArchiScript
def unfinished : Subdomain Bool where
  name := "true"
  base := fun _ => True
  parent := .predicate _
  meaning := fun b => b = true
  contained := fun _ _ => trivial
  definition := .predicate _
