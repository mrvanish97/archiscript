import ArchiScript.Distributive

namespace ArchiScript

universe u v

/--
A finite, well-typed ArchiScript morphism expression.

The category supplies semantic morphisms; this syntax records how one selected
architectural consequence is presented. Every expression has exactly one source
and one target even when its syntax tree branches through tensor or copairing.
-/
inductive Expression :
    Partition.{u, v} → Partition.{u, v} → Type (max (u + 1) (v + 1)) where
  | atom {X Y : Partition.{u, v}} (operation : Operation X Y) :
      Expression X Y
  | identity (X : Partition.{u, v}) :
      Expression X X
  | comp {X Y Z : Partition.{u, v}}
      (g : Expression Y Z) (f : Expression X Y) :
      Expression X Z
  | tensor {P P' Q Q' : Partition.{u, v}}
      (f : Expression P P') (g : Expression Q Q') :
      Expression (P.tensor Q) (P'.tensor Q')
  | coproductInl (P Q : Partition.{u, v}) :
      Expression P (P.coproduct Q)
  | coproductInr (P Q : Partition.{u, v}) :
      Expression Q (P.coproduct Q)
  | copair {P Q R : Partition.{u, v}}
      (f : Expression P R) (g : Expression Q R) :
      Expression (P.coproduct Q) R
  | iso {P Q : Partition.{u, v}} (e : Partition.PartitionIso P Q) :
      Expression P Q

namespace Expression

/-- Interpret expression syntax as the ordinary ArchiScript Operation it denotes. -/
def denote {X Y : Partition.{u, v}} : Expression X Y → Operation X Y
  | .atom operation => operation
  | .identity X => Operation.id X
  | .comp g f => (denote g).comp (denote f)
  | .tensor f g => (denote f).tensor (denote g)
  | .coproductInl P Q => Operation.coproductInl P Q
  | .coproductInr P Q => Operation.coproductInr P Q
  | .copair f g => Operation.copair (denote f) (denote g)
  | .iso e => e.toOperation

instance {X Y : Partition.{u, v}} :
    Coe (Expression X Y) (Operation X Y) :=
  ⟨denote⟩

/-- A finite dependent entry keeps one target together with its typed expression. -/
structure Some (source : Partition.{u, v}) where
  target : Partition.{u, v}
  expression : Expression source target

/--
A finite nonempty family of expressions with one common source.

The declaration that names a family remains presentation identity; no name field
is added to the mathematical VDP or Operation structures.
-/
structure Family where
  source : Partition.{u, v}
  expressions : List (Some source)
  nonempty : expressions ≠ []

namespace Family

def targets (family : Family.{u, v}) : List Partition :=
  family.expressions.map (fun entry => entry.target)

def singleton {X Y : Partition.{u, v}} (expression : Expression X Y) :
    Family.{u, v} where
  source := X
  expressions := [⟨Y, expression⟩]
  nonempty := by simp

end Family

/-- A local same-endpoint normalization certificate. -/
structure Rewrite {X Y : Partition.{u, v}}
    (before after : Expression X Y) where
  sound : denote before = denote after

/--
A local normalization certificate when structural endpoint representatives
change through explicit VDP isomorphisms.
-/
structure Transport {X Y X' Y' : Partition.{u, v}}
    (before : Expression X Y) (after : Expression X' Y') where
  sourceIso : Partition.PartitionIso X X'
  targetIso : Partition.PartitionIso Y Y'
  commutes :
    targetIso.toOperation.comp (denote before) =
      (denote after).comp sourceIso.toOperation

namespace Rewrite

def refl {X Y : Partition.{u, v}} (e : Expression X Y) : Rewrite e e :=
  ⟨rfl⟩

def trans {X Y : Partition.{u, v}} {a b c : Expression X Y}
    (ab : Rewrite a b) (bc : Rewrite b c) : Rewrite a c :=
  ⟨ab.sound.trans bc.sound⟩

@[simp] theorem id_left {X Y : Partition.{u, v}} (e : Expression X Y) :
    Rewrite (.comp (.identity Y) e) e := by
  refine ⟨?_⟩
  exact Operation.id_comp (denote e)

@[simp] theorem id_right {X Y : Partition.{u, v}} (e : Expression X Y) :
    Rewrite (.comp e (.identity X)) e := by
  refine ⟨?_⟩
  exact Operation.comp_id (denote e)

theorem comp_assoc {W X Y Z : Partition.{u, v}}
    (h : Expression Y Z) (g : Expression X Y) (f : Expression W X) :
    Rewrite (.comp (.comp h g) f) (.comp h (.comp g f)) := by
  refine ⟨?_⟩
  exact Operation.comp_assoc (denote h) (denote g) (denote f)

@[simp] theorem copair_inl {P Q R : Partition.{u, v}}
    (f : Expression P R) (g : Expression Q R) :
    Rewrite
      (.comp (.copair f g) (.coproductInl P Q))
      f := by
  refine ⟨?_⟩
  exact Operation.copair_inl (denote f) (denote g)

@[simp] theorem copair_inr {P Q R : Partition.{u, v}}
    (f : Expression P R) (g : Expression Q R) :
    Rewrite
      (.comp (.copair f g) (.coproductInr P Q))
      g := by
  refine ⟨?_⟩
  exact Operation.copair_inr (denote f) (denote g)

@[simp] theorem tensor_identity (P Q : Partition.{u, v}) :
    Rewrite
      (.tensor (.identity P) (.identity Q))
      (.identity (P.tensor Q)) := by
  refine ⟨?_⟩
  exact Operation.tensor_id P Q

end Rewrite

end Expression
end ArchiScript
