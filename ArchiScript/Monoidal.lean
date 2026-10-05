import ArchiScript.Operation

namespace ArchiScript

namespace Partition

/-- A classification-preserving isomorphism induces a member operation. The
carrier map witnesses semantic preservation; the operation uses only indices. -/
def PartitionIso.toOperation {P Q : Partition} (e : PartitionIso P Q) :
    Operation P Q := ⟨fun i => some (e.memberIndex.toFun i)⟩

def PartitionIso.inverseOperation {P Q : Partition} (e : PartitionIso P Q) :
    Operation Q P := ⟨fun j => some (e.memberIndex.invFun j)⟩

@[simp] theorem PartitionIso.left_operation_inv {P Q : Partition} (e : PartitionIso P Q) :
    e.inverseOperation.comp e.toOperation = Operation.id P := by
  apply Operation.ext
  intro i
  simp [PartitionIso.toOperation, PartitionIso.inverseOperation, Operation.comp,
    Operation.id, e.memberIndex.left_inv]

@[simp] theorem PartitionIso.right_operation_inv {P Q : Partition} (e : PartitionIso P Q) :
    e.toOperation.comp e.inverseOperation = Operation.id Q := by
  apply Operation.ext
  intro j
  simp [PartitionIso.toOperation, PartitionIso.inverseOperation, Operation.comp,
    Operation.id, e.memberIndex.right_inv]

/-- Tensor two VDP isomorphisms componentwise. -/
def PartitionIso.tensor {P P' Q Q' : Partition}
    (e : PartitionIso P P') (f : PartitionIso Q Q') :
    PartitionIso (P.tensor Q) (P'.tensor Q') where
  carrier := {
    toFun := fun xy => (e.carrier.toFun xy.1, f.carrier.toFun xy.2)
    invFun := fun xy => (e.carrier.invFun xy.1, f.carrier.invFun xy.2)
    left_inv := by
      intro ⟨x, y⟩
      simp only
      rw [e.carrier.left_inv, f.carrier.left_inv]
    right_inv := by
      intro ⟨x, y⟩
      simp only
      rw [e.carrier.right_inv, f.carrier.right_inv]
  }
  memberIndex := {
    toFun := fun ij => (e.memberIndex.toFun ij.1, f.memberIndex.toFun ij.2)
    invFun := fun ij => (e.memberIndex.invFun ij.1, f.memberIndex.invFun ij.2)
    left_inv := by
      intro ⟨i, j⟩
      simp only
      rw [e.memberIndex.left_inv, f.memberIndex.left_inv]
    right_inv := by
      intro ⟨i, j⟩
      simp only
      rw [e.memberIndex.right_inv, f.memberIndex.right_inv]
  }
  classify_commutes := by
    intro ⟨x, y⟩
    change
      (P'.classify (e.carrier.toFun x), Q'.classify (f.carrier.toFun y)) =
        (e.memberIndex.toFun (P.classify x), f.memberIndex.toFun (Q.classify y))
    rw [e.classify_commutes, f.classify_commutes]

/-- Rebracket both carrier positions and member indices. -/
def tensorAssociator (P Q R : Partition) :
    PartitionIso ((P.tensor Q).tensor R) (P.tensor (Q.tensor R)) where
  carrier := {
    toFun := fun x => (x.1.1, (x.1.2, x.2))
    invFun := fun x => ((x.1, x.2.1), x.2.2)
    left_inv := by intro ⟨⟨p, q⟩, r⟩; rfl
    right_inv := by intro ⟨p, ⟨q, r⟩⟩; rfl
  }
  memberIndex := {
    toFun := fun x => (x.1.1, (x.1.2, x.2))
    invFun := fun x => ((x.1, x.2.1), x.2.2)
    left_inv := by intro ⟨⟨p, q⟩, r⟩; rfl
    right_inv := by intro ⟨p, ⟨q, r⟩⟩; rfl
  }
  classify_commutes := by intro ⟨⟨p, q⟩, r⟩; rfl

/-- Delete the unique left Unit coordinate. -/
def tensorLeftUnitor (P : Partition) : PartitionIso (unit.tensor P) P where
  carrier := {
    toFun := fun x => x.2
    invFun := fun x => ((), x)
    left_inv := by intro ⟨u, x⟩; cases u; rfl
    right_inv := by intro x; rfl
  }
  memberIndex := {
    toFun := fun x => x.2
    invFun := fun x => ((), x)
    left_inv := by intro ⟨u, i⟩; cases u; rfl
    right_inv := by intro i; rfl
  }
  classify_commutes := by intro ⟨u, x⟩; cases u; rfl

/-- Delete the unique right Unit coordinate. -/
def tensorRightUnitor (P : Partition) : PartitionIso (P.tensor unit) P where
  carrier := {
    toFun := fun x => x.1
    invFun := fun x => (x, ())
    left_inv := by intro ⟨x, u⟩; cases u; rfl
    right_inv := by intro x; rfl
  }
  memberIndex := {
    toFun := fun x => x.1
    invFun := fun x => (x, ())
    left_inv := by intro ⟨i, u⟩; cases u; rfl
    right_inv := by intro i; rfl
  }
  classify_commutes := by intro ⟨x, u⟩; cases u; rfl

/-- Swap two independent coordinates; this does not identify their values. -/
def tensorSymmetry (P Q : Partition) : PartitionIso (P.tensor Q) (Q.tensor P) where
  carrier := {
    toFun := fun x => (x.2, x.1)
    invFun := fun x => (x.2, x.1)
    left_inv := by intro ⟨p, q⟩; rfl
    right_inv := by intro ⟨q, p⟩; rfl
  }
  memberIndex := {
    toFun := fun x => (x.2, x.1)
    invFun := fun x => (x.2, x.1)
    left_inv := by intro ⟨p, q⟩; rfl
    right_inv := by intro ⟨q, p⟩; rfl
  }
  classify_commutes := by intro ⟨p, q⟩; rfl

/-- The two pentagon paths also agree on carrier values, beyond their induced
member operations. -/
theorem tensorAssociator_carrier_pentagon (P Q R S : Partition)
    (x : (((P.tensor Q).tensor R).tensor S).Carrier) :
    (tensorAssociator P Q (R.tensor S)).carrier.toFun
      ((tensorAssociator (P.tensor Q) R S).carrier.toFun x) =
    (Prod.map id (tensorAssociator Q R S).carrier.toFun)
      ((tensorAssociator P (Q.tensor R) S).carrier.toFun
        ((Prod.map (tensorAssociator P Q R).carrier.toFun id) x)) := by
  rcases x with ⟨⟨⟨p, q⟩, r⟩, s⟩
  rfl

theorem tensorAssociator_carrier_triangle (P Q : Partition)
    (x : ((P.tensor unit).tensor Q).Carrier) :
    (Prod.map id (tensorLeftUnitor Q).carrier.toFun)
      ((tensorAssociator P unit Q).carrier.toFun x) =
    (Prod.map (tensorRightUnitor P).carrier.toFun id) x := by
  rcases x with ⟨⟨p, u⟩, q⟩
  cases u
  rfl

theorem tensorSymmetry_carrier_hexagon (P Q R : Partition)
    (x : ((P.tensor Q).tensor R).Carrier) :
    (tensorAssociator Q R P).carrier.toFun
      ((tensorSymmetry P (Q.tensor R)).carrier.toFun
        ((tensorAssociator P Q R).carrier.toFun x)) =
    (Prod.map id (tensorSymmetry P R).carrier.toFun)
      ((tensorAssociator Q P R).carrier.toFun
        ((Prod.map (tensorSymmetry P Q).carrier.toFun id) x)) := by
  rcases x with ⟨⟨p, q⟩, r⟩
  rfl

end Partition

namespace Operation

/-- The canonical associator as a partial-member-category morphism. -/
def associator (P Q R : Partition) :
    Operation ((P.tensor Q).tensor R) (P.tensor (Q.tensor R)) :=
  (Partition.tensorAssociator P Q R).toOperation

def associatorInv (P Q R : Partition) :
    Operation (P.tensor (Q.tensor R)) ((P.tensor Q).tensor R) :=
  (Partition.tensorAssociator P Q R).inverseOperation

def leftUnitor (P : Partition) : Operation (Partition.unit.tensor P) P :=
  (Partition.tensorLeftUnitor P).toOperation

def leftUnitorInv (P : Partition) : Operation P (Partition.unit.tensor P) :=
  (Partition.tensorLeftUnitor P).inverseOperation

def rightUnitor (P : Partition) : Operation (P.tensor Partition.unit) P :=
  (Partition.tensorRightUnitor P).toOperation

def rightUnitorInv (P : Partition) : Operation P (P.tensor Partition.unit) :=
  (Partition.tensorRightUnitor P).inverseOperation

def symmetry (P Q : Partition) : Operation (P.tensor Q) (Q.tensor P) :=
  (Partition.tensorSymmetry P Q).toOperation

@[simp] theorem associator_left_inv (P Q R : Partition) :
    (associatorInv P Q R).comp (associator P Q R) =
      id ((P.tensor Q).tensor R) :=
  (Partition.tensorAssociator P Q R).left_operation_inv

@[simp] theorem associator_right_inv (P Q R : Partition) :
    (associator P Q R).comp (associatorInv P Q R) =
      id (P.tensor (Q.tensor R)) :=
  (Partition.tensorAssociator P Q R).right_operation_inv

@[simp] theorem leftUnitor_left_inv (P : Partition) :
    (leftUnitorInv P).comp (leftUnitor P) = id (Partition.unit.tensor P) :=
  (Partition.tensorLeftUnitor P).left_operation_inv

@[simp] theorem leftUnitor_right_inv (P : Partition) :
    (leftUnitor P).comp (leftUnitorInv P) = id P :=
  (Partition.tensorLeftUnitor P).right_operation_inv

@[simp] theorem rightUnitor_left_inv (P : Partition) :
    (rightUnitorInv P).comp (rightUnitor P) = id (P.tensor Partition.unit) :=
  (Partition.tensorRightUnitor P).left_operation_inv

@[simp] theorem rightUnitor_right_inv (P : Partition) :
    (rightUnitor P).comp (rightUnitorInv P) = id P :=
  (Partition.tensorRightUnitor P).right_operation_inv

@[simp] theorem symmetry_involutive (P Q : Partition) :
    (symmetry Q P).comp (symmetry P Q) = id (P.tensor Q) := by
  apply Operation.ext
  intro ⟨i, j⟩
  rfl

/-- Rebracketing commutes with three independent member maps. -/
theorem associator_natural {P P' Q Q' R R' : Partition}
    (f : Operation P P') (g : Operation Q Q') (h : Operation R R') :
    (associator P' Q' R').comp ((f.tensor g).tensor h) =
      (f.tensor (g.tensor h)).comp (associator P Q R) := by
  apply Operation.ext
  intro ⟨⟨i, j⟩, k⟩
  cases hf : f i <;> cases hg : g j <;> cases hh : h k <;>
    simp [associator, Partition.tensorAssociator, Partition.PartitionIso.toOperation, tensor, comp,
      hf, hg, hh, Option.bind]

theorem leftUnitor_natural {P Q : Partition} (f : Operation P Q) :
    f.comp (leftUnitor P) =
      (leftUnitor Q).comp ((id Partition.unit).tensor f) := by
  apply Operation.ext
  intro ⟨u, i⟩
  cases u
  cases hf : f i <;>
    simp [leftUnitor, Partition.tensorLeftUnitor, Partition.PartitionIso.toOperation, tensor, comp,
      id, hf, Option.bind]

theorem rightUnitor_natural {P Q : Partition} (f : Operation P Q) :
    f.comp (rightUnitor P) =
      (rightUnitor Q).comp (f.tensor (id Partition.unit)) := by
  apply Operation.ext
  intro ⟨i, u⟩
  cases u
  cases hf : f i <;>
    simp [rightUnitor, Partition.tensorRightUnitor, Partition.PartitionIso.toOperation, tensor, comp,
      id, hf, Option.bind]

theorem symmetry_natural {P P' Q Q' : Partition}
    (f : Operation P P') (g : Operation Q Q') :
    (symmetry P' Q').comp (f.tensor g) =
      (g.tensor f).comp (symmetry P Q) := by
  apply Operation.ext
  intro ⟨i, j⟩
  cases hf : f i <;> cases hg : g j <;>
    simp [symmetry, Partition.tensorSymmetry, Partition.PartitionIso.toOperation, tensor, comp,
      hf, hg, Option.bind]

/-- Mac Lane's pentagon, checked on member operations. -/
theorem pentagon (P Q R S : Partition) :
    (associator P Q (R.tensor S)).comp
        (associator (P.tensor Q) R S) =
      ((id P).tensor (associator Q R S)).comp
        ((associator P (Q.tensor R) S).comp
          ((associator P Q R).tensor (id S))) := by
  apply Operation.ext
  intro ⟨⟨⟨i, j⟩, k⟩, l⟩
  rfl

/-- Compatibility of associator with the two unitors. -/
theorem triangle (P Q : Partition) :
    ((id P).tensor (leftUnitor Q)).comp
        (associator P Partition.unit Q) =
      (rightUnitor P).tensor (id Q) := by
  apply Operation.ext
  intro ⟨⟨i, u⟩, j⟩
  cases u
  rfl

/-- One symmetric hexagon; the other follows by inverse symmetry. -/
theorem hexagon (P Q R : Partition) :
    (associator Q R P).comp
        ((symmetry P (Q.tensor R)).comp (associator P Q R)) =
      ((id Q).tensor (symmetry P R)).comp
        ((associator Q P R).comp ((symmetry P Q).tensor (id R))) := by
  apply Operation.ext
  intro ⟨⟨i, j⟩, k⟩
  rfl

end Operation
end ArchiScript
