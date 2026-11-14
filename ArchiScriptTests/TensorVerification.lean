import ArchiScript.Verification
import ArchiScriptExamples.CorrelatedJoin

namespace ArchiScriptTests.TensorVerification
open ArchiScript

abbrev Pair := Bool × Bool
abbrev Triple := Bool × (Bool × Bool)
def pairs : List Pair := MemberEnumeration.indices
def triples : List Triple := MemberEnumeration.indices

def diagonal (t : Pair) : Prop := t.1 = t.2
instance (t : Pair) : Decidable (diagonal t) := inferInstanceAs (Decidable (t.1 = t.2))

def parity (t : Triple) : Prop := t.2.2 = xor t.1 t.2.1
instance (t : Triple) : Decidable (parity t) := inferInstanceAs (Decidable (t.2.2 = xor t.1 t.2.1))

def full {α : Type} (_ : α) : Prop := True
instance {α : Type} (x : α) : Decidable (full x) := isTrue trivial

#guard pairs.length == 4
#guard triples.length == 8
#guard (Verification.missing triples parity full).length == 4
#guard (Verification.unexpected triples full parity).length == 4

/-- Every pair projection is complete, but four full triples remain forbidden. -/
theorem pairwise_is_insufficient :
    (∀ a b : Bool, ∃ c : Bool, parity (a, b, c)) ∧
    (∀ a c : Bool, ∃ b : Bool, parity (a, b, c)) ∧
    (∀ b c : Bool, ∃ a : Bool, parity (a, b, c)) ∧
    ¬ parity (false, false, true) := by
  decide

example : (false, false, true) ∈ Verification.missing triples parity full := by decide
example : (false, false, true) ∈ Verification.unexpected triples full parity := by decide

def constantIncoming (b : Bool) : Prop := b = true
instance (b : Bool) : Decidable (constantIncoming b) := inferInstanceAs (Decidable (b = true))
def tooNarrow (t : Pair) : Prop := t = (true, true)
instance (t : Pair) : Decidable (tooNarrow t) := inferInstanceAs (Decidable (t = (true, true)))

-- The second actual supplier can produce false, even though the first is constant.
#guard Verification.unpartnered [false, true] pairs Prod.snd full tooNarrow == [false]
example : ¬ ∃ t : Pair, tooNarrow t ∧ t.2 = false := by
  rintro ⟨t, rfl, impossible⟩
  cases impossible

-- A true-only producer keeps the false member in its mathematical VDP.
#guard Verification.unpartnered [false, true] pairs Prod.fst constantIncoming
  (fun t => t.1 = true) == []

open ArchiScriptExamples.CorrelatedJoin in
example : ¬ (model id).reachInput .join (joinInput id) (false, true) := by
  intro bad
  have impossible := (input_exact id .join (joinInput id) (false, true)).mp bad
  cases impossible

open ArchiScriptExamples.CorrelatedJoin in
example : (model (fun _ => true)).reachInput .join (joinInput (fun _ => true)) (false, true) :=
  (input_exact _ _ _ _).mpr rfl

end ArchiScriptTests.TensorVerification
