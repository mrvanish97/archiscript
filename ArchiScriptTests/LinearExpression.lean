import ArchiScriptExamples.CyclicCone

namespace ArchiScriptTests.LinearExpression
open ArchiScript ArchiScriptExamples.CyclicCone

abbrev inventory := signature.generatorsInventory

/-- Each route is finite and linear, but it may traverse the same cycle n times. -/
def walk : Nat → Expression inventory (.node ()) (.node ())
  | 0 => Expression.identity (G := inventory) (Inputs.node ())
  | n + 1 => Expression.step (G := inventory) () (walk n)

theorem member_after_walk (n : Nat) : (walk n).denote false = some (alternating n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((walk n).denote false).bind (fun b => some (!b)) = some (!alternating n)
    rw [ih]
    rfl

example (n : Nat) : (walk n).denote.image (fun b => b = false) (alternating n) :=
  ⟨false, rfl, member_after_walk n⟩

example : ((walk 1).append (walk 1)).denote = (walk 1).denote.comp (walk 1).denote :=
  Expression.denote_append _ _

end ArchiScriptTests.LinearExpression
