import ArchiScript.Monoidal
import ArchiScript.Coproduct

namespace ArchiScript

namespace Partition

/--
Canonical right distributivity of tensor over binary coproduct.

This is an isomorphism, not definitional equality: the source carrier is a
tagged sum of products, while the target carrier is a product whose left
coordinate is tagged.
-/
def tensorCoproductRightDistributivity (P Q R : Partition) :
    PartitionIso ((P.tensor R).coproduct (Q.tensor R))
      ((P.coproduct Q).tensor R) where
  carrier := {
    toFun := fun
      | .inl (p, r) => (.inl p, r)
      | .inr (q, r) => (.inr q, r)
    invFun := fun
      | (.inl p, r) => .inl (p, r)
      | (.inr q, r) => .inr (q, r)
    left_inv := by
      intro x
      cases x <;> rfl
    right_inv := by
      intro x
      rcases x with ⟨pq, r⟩
      cases pq <;> rfl
  }
  memberIndex := {
    toFun := fun
      | .inl (i, k) => (.inl i, k)
      | .inr (j, k) => (.inr j, k)
    invFun := fun
      | (.inl i, k) => .inl (i, k)
      | (.inr j, k) => .inr (j, k)
    left_inv := by
      intro x
      cases x <;> rfl
    right_inv := by
      intro x
      rcases x with ⟨ij, k⟩
      cases ij <;> rfl
  }
  classify_commutes := by
    intro x
    cases x <;> rfl

/-- Canonical left distributivity of tensor over binary coproduct. -/
def tensorCoproductLeftDistributivity (R P Q : Partition) :
    PartitionIso ((R.tensor P).coproduct (R.tensor Q))
      (R.tensor (P.coproduct Q)) where
  carrier := {
    toFun := fun
      | .inl (r, p) => (r, .inl p)
      | .inr (r, q) => (r, .inr q)
    invFun := fun
      | (r, .inl p) => .inl (r, p)
      | (r, .inr q) => .inr (r, q)
    left_inv := by
      intro x
      cases x <;> rfl
    right_inv := by
      intro x
      rcases x with ⟨r, pq⟩
      cases pq <;> rfl
  }
  memberIndex := {
    toFun := fun
      | .inl (k, i) => (k, .inl i)
      | .inr (k, j) => (k, .inr j)
    invFun := fun
      | (k, .inl i) => .inl (k, i)
      | (k, .inr j) => .inr (k, j)
    left_inv := by
      intro x
      cases x <;> rfl
    right_inv := by
      intro x
      rcases x with ⟨k, ij⟩
      cases ij <;> rfl
  }
  classify_commutes := by
    intro x
    cases x <;> rfl

end Partition

namespace Operation

/-- Right distributivity as an ordinary ArchiScript morphism. -/
def distributeRight (P Q R : Partition) :
    Operation ((P.tensor R).coproduct (Q.tensor R))
      ((P.coproduct Q).tensor R) :=
  (Partition.tensorCoproductRightDistributivity P Q R).toOperation

def distributeRightInv (P Q R : Partition) :
    Operation ((P.coproduct Q).tensor R)
      ((P.tensor R).coproduct (Q.tensor R)) :=
  (Partition.tensorCoproductRightDistributivity P Q R).inverseOperation

/-- Left distributivity as an ordinary ArchiScript morphism. -/
def distributeLeft (R P Q : Partition) :
    Operation ((R.tensor P).coproduct (R.tensor Q))
      (R.tensor (P.coproduct Q)) :=
  (Partition.tensorCoproductLeftDistributivity R P Q).toOperation

def distributeLeftInv (R P Q : Partition) :
    Operation (R.tensor (P.coproduct Q))
      ((R.tensor P).coproduct (R.tensor Q)) :=
  (Partition.tensorCoproductLeftDistributivity R P Q).inverseOperation

@[simp] theorem distributeRight_left_inv (P Q R : Partition) :
    (distributeRightInv P Q R).comp (distributeRight P Q R) =
      id ((P.tensor R).coproduct (Q.tensor R)) :=
  (Partition.tensorCoproductRightDistributivity P Q R).left_operation_inv

@[simp] theorem distributeRight_right_inv (P Q R : Partition) :
    (distributeRight P Q R).comp (distributeRightInv P Q R) =
      id ((P.coproduct Q).tensor R) :=
  (Partition.tensorCoproductRightDistributivity P Q R).right_operation_inv

@[simp] theorem distributeLeft_left_inv (R P Q : Partition) :
    (distributeLeftInv R P Q).comp (distributeLeft R P Q) =
      id ((R.tensor P).coproduct (R.tensor Q)) :=
  (Partition.tensorCoproductLeftDistributivity R P Q).left_operation_inv

@[simp] theorem distributeLeft_right_inv (R P Q : Partition) :
    (distributeLeft R P Q).comp (distributeLeftInv R P Q) =
      id (R.tensor (P.coproduct Q)) :=
  (Partition.tensorCoproductLeftDistributivity R P Q).right_operation_inv

/-- Right distributivity is natural in all three coordinates. -/
theorem distributeRight_natural
    {P P' Q Q' R R' : Partition}
    (f : Operation P P') (g : Operation Q Q') (h : Operation R R') :
    (distributeRight P' Q' R').comp
        (coproductMap (f.tensor h) (g.tensor h)) =
      ((coproductMap f g).tensor h).comp (distributeRight P Q R) := by
  apply Operation.ext
  intro x
  cases x with
  | inl ik =>
      rcases ik with ⟨i, k⟩
      cases hf : f i <;> cases hh : h k <;>
        simp [distributeRight, Partition.tensorCoproductRightDistributivity,
          Partition.PartitionIso.toOperation, coproductMap, tensor, comp,
          hf, hh, Option.map, Option.bind]
  | inr jk =>
      rcases jk with ⟨j, k⟩
      cases hg : g j <;> cases hh : h k <;>
        simp [distributeRight, Partition.tensorCoproductRightDistributivity,
          Partition.PartitionIso.toOperation, coproductMap, tensor, comp,
          hg, hh, Option.map, Option.bind]

/-- Left distributivity is natural in all three coordinates. -/
theorem distributeLeft_natural
    {R R' P P' Q Q' : Partition}
    (h : Operation R R') (f : Operation P P') (g : Operation Q Q') :
    (distributeLeft R' P' Q').comp
        (coproductMap (h.tensor f) (h.tensor g)) =
      (h.tensor (coproductMap f g)).comp (distributeLeft R P Q) := by
  apply Operation.ext
  intro x
  cases x with
  | inl ki =>
      rcases ki with ⟨k, i⟩
      cases hh : h k <;> cases hf : f i <;>
        simp [distributeLeft, Partition.tensorCoproductLeftDistributivity,
          Partition.PartitionIso.toOperation, coproductMap, tensor, comp,
          hh, hf, Option.map, Option.bind]
  | inr kj =>
      rcases kj with ⟨k, j⟩
      cases hh : h k <;> cases hg : g j <;>
        simp [distributeLeft, Partition.tensorCoproductLeftDistributivity,
          Partition.PartitionIso.toOperation, coproductMap, tensor, comp,
          hh, hg, Option.map, Option.bind]

end Operation
end ArchiScript
