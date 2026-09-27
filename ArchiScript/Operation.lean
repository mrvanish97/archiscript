import ArchiScript.Partition

namespace ArchiScript

/-- An operation is exactly a partial function on semantic member indices. -/
structure Operation (X Y : Partition) where
  run : X.MemberIndex → Option Y.MemberIndex

namespace Operation

universe u

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
