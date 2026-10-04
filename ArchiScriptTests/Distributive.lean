import ArchiScript.Distributive

namespace ArchiScriptTests.Distributive
open ArchiScript

example :
    (Operation.distributeRightInv Partition.unit Partition.unit Partition.unit).comp
        (Operation.distributeRight Partition.unit Partition.unit Partition.unit) =
      Operation.id
        ((Partition.unit.tensor Partition.unit).coproduct
          (Partition.unit.tensor Partition.unit)) :=
  Operation.distributeRight_left_inv _ _ _

example :
    (Operation.distributeLeft Partition.unit Partition.unit Partition.unit).comp
        (Operation.distributeLeftInv Partition.unit Partition.unit Partition.unit) =
      Operation.id
        (Partition.unit.tensor (Partition.unit.coproduct Partition.unit)) :=
  Operation.distributeLeft_right_inv _ _ _

example :
    (Operation.distributeRight Partition.unit Partition.unit Partition.unit).comp
        (Operation.coproductMap
          ((Operation.id Partition.unit).tensor (Operation.id Partition.unit))
          ((Operation.id Partition.unit).tensor (Operation.id Partition.unit))) =
      ((Operation.coproductMap
          (Operation.id Partition.unit) (Operation.id Partition.unit)).tensor
            (Operation.id Partition.unit)).comp
        (Operation.distributeRight Partition.unit Partition.unit Partition.unit) :=
  Operation.distributeRight_natural
    (Operation.id Partition.unit)
    (Operation.id Partition.unit)
    (Operation.id Partition.unit)

end ArchiScriptTests.Distributive
