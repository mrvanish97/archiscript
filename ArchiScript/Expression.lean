import ArchiScript.Operation

namespace ArchiScript

/-- The claimed-complete primitive inventory. Generated paths use these names,
not arbitrary derived Operations disguised as new atoms. -/
structure Generators where
  Name : Type v
  names : List Name
  complete : ∀ n, n ∈ names
  Object : Type x
  object : Object → Partition.{u, w}
  source : Name → Object
  target : Name → Object
  operation : (n : Name) → Operation (object (source n)) (object (target n))

/-- A finite linear typed chain. Tensor and copair trees belong to
`Presentation`, not to this route syntax. -/
inductive Expression (G : Generators) : G.Object → G.Object → Type _ where
  | identity (X) : Expression G X X
  | step (name : G.Name) {X} (before : Expression G X (G.source name)) :
      Expression G X (G.target name)

namespace Expression

def denote {G : Generators} {X Y} : Expression G X Y → Operation (G.object X) (G.object Y)
  | .identity X => Operation.id (G.object X)
  | .step name before => (G.operation name).comp before.denote

def append {G : Generators} {X Y Z} (g : Expression G Y Z)
    (f : Expression G X Y) : Expression G X Z :=
  match g with
  | .identity _ => f
  | .step name before => .step name (append before f)

theorem denote_append {G : Generators} {X Y Z} (g : Expression G Y Z)
    (f : Expression G X Y) : (g.append f).denote = g.denote.comp f.denote := by
  induction g with
  | identity => simp [append, denote]
  | step name before ih =>
    simp only [append, denote, ih, Operation.comp_assoc]

/-- The image concerns the specified inputs, never all target members. -/
def image {G : Generators} {X Y} (e : Expression G X Y)
    (inputs : (G.object X).MemberIndex → Prop) (j : (G.object Y).MemberIndex) : Prop :=
  ∃ i, inputs i ∧ e.denote i = some j

end Expression
end ArchiScript
