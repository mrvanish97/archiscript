import ArchiScript.Partition

namespace ArchiScript

/-- An operation is exactly a partial function on semantic member indices. -/
structure Operation (X Y : Partition) where
  run : X.MemberIndex → Option Y.MemberIndex

namespace Operation

universe u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆

instance (X Y : Partition) : CoeFun (Operation X Y) (fun _ => X.MemberIndex → Option Y.MemberIndex) :=
  ⟨Operation.run⟩

@[ext] theorem ext {X Y : Partition} {f g : Operation X Y} (h : ∀ m, f m = g m) : f = g := by
  cases f with
  | mk frun =>
    cases g with
    | mk grun =>
      congr
      funext m
      exact h m

def id (X : Partition) : Operation X X := ⟨fun m => some m⟩

/-- Right-to-left composition: `(g.comp f) m` first runs `f`, then `g`. -/
def comp {X Y Z : Partition} (g : Operation Y Z) (f : Operation X Y) : Operation X Z :=
  ⟨fun m => (f m).bind g.run⟩

/-- Independent product of partial member maps. It is defined exactly when
both factors are defined; it says nothing about runtime parallel execution. -/
def tensor
    {P : Partition.{u₁, v₁}} {P' : Partition.{u₂, v₂}}
    {Q : Partition.{u₃, v₃}} {Q' : Partition.{u₄, v₄}}
    (f : Operation P P') (g : Operation Q Q') :
    Operation (P.tensor Q) (P'.tensor Q') :=
  ⟨fun ij => match f ij.1, g ij.2 with
    | some i', some j' => some (i', j')
    | _, _ => none⟩

@[simp] theorem tensor_apply
    {P : Partition.{u₁, v₁}} {P' : Partition.{u₂, v₂}}
    {Q : Partition.{u₃, v₃}} {Q' : Partition.{u₄, v₄}}
    (f : Operation P P') (g : Operation Q Q')
    (i : P.MemberIndex) (j : Q.MemberIndex) :
    f.tensor g (i, j) = match f i, g j with
      | some i', some j' => some (i', j')
      | _, _ => none := rfl

@[simp] theorem tensor_id (P Q : Partition) :
    (id P).tensor (id Q) = id (P.tensor Q) := by
  apply Operation.ext
  intro ⟨i, j⟩
  rfl

theorem tensor_comp
    {P : Partition.{u₁, v₁}} {P' : Partition.{u₂, v₂}} {P'' : Partition.{u₃, v₃}}
    {Q : Partition.{u₄, v₄}} {Q' : Partition.{u₅, v₅}} {Q'' : Partition.{u₆, v₆}}
    (f₁ : Operation P P') (f₂ : Operation P' P'')
    (g₁ : Operation Q Q') (g₂ : Operation Q' Q'') :
    (f₂.comp f₁).tensor (g₂.comp g₁) =
      (f₂.tensor g₂).comp (f₁.tensor g₁) := by
  apply Operation.ext
  intro ⟨i, j⟩
  cases hf₁ : f₁ i with
  | none => simp [tensor, comp, hf₁]
  | some i' =>
    cases hg₁ : g₁ j with
    | none => simp [tensor, comp, hf₁, hg₁]
    | some j' =>
      cases hf₂ : f₂ i' with
      | none => simp [tensor, comp, hf₁, hg₁, hf₂, Option.bind]
      | some i'' =>
        cases hg₂ : g₂ j' with
        | none => simp [tensor, comp, hf₁, hg₁, hf₂, hg₂, Option.bind]
        | some j'' => simp [tensor, comp, hf₁, hg₁, hf₂, hg₂, Option.bind]

@[simp] theorem id_apply (X : Partition) (m : X.MemberIndex) : id X m = some m := rfl

@[simp] theorem comp_apply {X Y Z : Partition} (g : Operation Y Z) (f : Operation X Y)
    (m : X.MemberIndex) : g.comp f m = (f m).bind g.run := rfl

@[simp] theorem id_comp {X Y : Partition} (f : Operation X Y) : (id Y).comp f = f := by
  ext m
  cases h : f m <;> simp [comp, id, h]

@[simp] theorem comp_id {X Y : Partition} (f : Operation X Y) : f.comp (id X) = f := by
  ext m
  simp [comp, id]

theorem comp_assoc {W X Y Z : Partition} (h : Operation Y Z) (g : Operation X Y)
    (f : Operation W X) : (h.comp g).comp f = h.comp (g.comp f) := by
  ext m
  cases hf : f m <;> simp [comp, hf]

/-- A typed witness that a source/target pair belongs to a partial map. -/
structure Branch {X Y : Partition} (op : Operation X Y) where
  source : X.MemberIndex
  target : Y.MemberIndex
  belongs : op source = some target

theorem Branch.in_operation {X Y : Partition} {op : Operation X Y} (b : Branch op) :
    op b.source = some b.target := b.belongs

end Operation
end ArchiScript
