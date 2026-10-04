import ArchiScriptExamples.Monoidal

namespace ArchiScriptTests.Monoidal
open ArchiScript ArchiScriptExamples.Monoidal

#guard Partition.unit.memberIndices.length == 1
example : Partition.unit.member () () := rfl
example : SemanticPartition.unit.members () () := trivial

example (i j : Bool) : (i, j) ∈ (bit.tensor bit).memberIndices :=
  (bit.tensor bit).memberIndices_complete (i, j)

example (i j : Bool) : ∃ xy, (bit.tensor bit).member (i, j) xy :=
  (bit.tensor bit).member_nonempty (i, j)

example (i j x y : Bool) :
    (bit.tensor bit).member (i, j) (x, y) ↔ bit.member i x ∧ bit.member j y :=
  Partition.tensor_member_iff bit bit i j x y

example (xy : (bit.tensor bit).Carrier) : ∃ ij, pair.members ij xy :=
  pair.members_cover xy

example : (bit.tensor bit).classify (false, true) ≠
    (bit.tensor bit).classify (true, false) := by decide

example : independent (false, false) = none := rfl
example : independent (false, true) = some (true, true) := rfl

example : (Operation.id bit).tensor (Operation.id bit) = Operation.id (bit.tensor bit) :=
  Operation.tensor_id bit bit

def identityTensorIso :
    Partition.PartitionIso (bit.tensor bit) (bit.tensor bit) :=
  (Partition.PartitionIso.refl bit).tensor (Partition.PartitionIso.refl bit)

#guard identityTensorIso.memberIndex.toFun (false, true) == (false, true)

def doubleSwapIso :
    Partition.PartitionIso (bit.tensor bit) (bit.tensor bit) :=
  (Partition.tensorSymmetry bit bit).trans (Partition.tensorSymmetry bit bit)

#guard doubleSwapIso.memberIndex.toFun (false, true) == (false, true)

example : (flip.comp keepTrue).tensor (keepTrue.comp flip) =
    (flip.tensor keepTrue).comp (keepTrue.tensor flip) :=
  Operation.tensor_comp keepTrue flip flip keepTrue

example : (Operation.associatorInv bit bit bit).comp
    (Operation.associator bit bit bit) = Operation.id ((bit.tensor bit).tensor bit) :=
  Operation.associator_left_inv bit bit bit

example : (Operation.leftUnitorInv bit).comp (Operation.leftUnitor bit) =
    Operation.id (Partition.unit.tensor bit) := Operation.leftUnitor_left_inv bit

example : (Operation.rightUnitorInv bit).comp (Operation.rightUnitor bit) =
    Operation.id (bit.tensor Partition.unit) := Operation.rightUnitor_left_inv bit

example : (Operation.symmetry bit bit).comp (Operation.symmetry bit bit) =
    Operation.id (bit.tensor bit) := Operation.symmetry_involutive bit bit

example : (Operation.associator bit bit bit).comp ((flip.tensor keepTrue).tensor flip) =
    (flip.tensor (keepTrue.tensor flip)).comp (Operation.associator bit bit bit) :=
  Operation.associator_natural flip keepTrue flip

example : flip.comp (Operation.leftUnitor bit) =
    (Operation.leftUnitor bit).comp ((Operation.id Partition.unit).tensor flip) :=
  Operation.leftUnitor_natural flip

example : flip.comp (Operation.rightUnitor bit) =
    (Operation.rightUnitor bit).comp (flip.tensor (Operation.id Partition.unit)) :=
  Operation.rightUnitor_natural flip

example : (Operation.symmetry bit bit).comp (flip.tensor keepTrue) =
    (keepTrue.tensor flip).comp (Operation.symmetry bit bit) :=
  Operation.symmetry_natural flip keepTrue

example : (Operation.associator bit bit (bit.tensor bit)).comp
    (Operation.associator (bit.tensor bit) bit bit) =
    ((Operation.id bit).tensor (Operation.associator bit bit bit)).comp
      ((Operation.associator bit (bit.tensor bit) bit).comp
        ((Operation.associator bit bit bit).tensor (Operation.id bit))) :=
  Operation.pentagon bit bit bit bit

example : ((Operation.id bit).tensor (Operation.leftUnitor bit)).comp
    (Operation.associator bit Partition.unit bit) =
    (Operation.rightUnitor bit).tensor (Operation.id bit) :=
  Operation.triangle bit bit

example : (Operation.associator bit bit bit).comp
    ((Operation.symmetry bit (bit.tensor bit)).comp (Operation.associator bit bit bit)) =
    ((Operation.id bit).tensor (Operation.symmetry bit bit)).comp
      ((Operation.associator bit bit bit).comp
        ((Operation.symmetry bit bit).tensor (Operation.id bit))) :=
  Operation.hexagon bit bit bit

example (x : (((bit.tensor bit).tensor bit).tensor bit).Carrier) :
    (Partition.tensorAssociator bit bit (bit.tensor bit)).carrier.toFun
      ((Partition.tensorAssociator (bit.tensor bit) bit bit).carrier.toFun x) =
    (Prod.map id (Partition.tensorAssociator bit bit bit).carrier.toFun)
      ((Partition.tensorAssociator bit (bit.tensor bit) bit).carrier.toFun
        ((Prod.map (Partition.tensorAssociator bit bit bit).carrier.toFun id) x)) :=
  Partition.tensorAssociator_carrier_pentagon bit bit bit bit x

end ArchiScriptTests.Monoidal
