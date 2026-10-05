import ArchiScript.Expression

namespace ArchiScriptTests.Expression
open ArchiScript

def unitId : Expression Partition.unit Partition.unit :=
  .atom (Operation.id Partition.unit)

def unitFamily : Expression.Family :=
  Expression.Family.singleton unitId

#guard unitFamily.expressions.length == 1
#guard unitFamily.targets.length == 1

example :
    Expression.denote
      (Expression.comp (Expression.identity Partition.unit) unitId) =
      Expression.denote unitId :=
  (Expression.Rewrite.id_left unitId).sound

example :
    Expression.denote
      (Expression.comp unitId (Expression.identity Partition.unit)) =
      Expression.denote unitId :=
  (Expression.Rewrite.id_right unitId).sound

example :
    Expression.Rewrite
      (Expression.comp
        (Expression.copair unitId unitId)
        (Expression.coproductInl Partition.unit Partition.unit))
      unitId :=
  Expression.Rewrite.copair_inl unitId unitId

example :
    Expression.Rewrite
      (Expression.comp
        (Expression.copair unitId unitId)
        (Expression.coproductInr Partition.unit Partition.unit))
      unitId :=
  Expression.Rewrite.copair_inr unitId unitId

example :
    Expression.Rewrite
      (Expression.comp
        (Expression.comp unitId unitId)
        unitId)
      (Expression.comp
        unitId
        (Expression.comp unitId unitId)) :=
  Expression.Rewrite.comp_assoc unitId unitId unitId

example :
    Expression.Rewrite
      (Expression.tensor
        (Expression.identity Partition.unit)
        (Expression.identity Partition.unit))
      (Expression.identity (Partition.unit.tensor Partition.unit)) :=
  Expression.Rewrite.tensor_identity _ _

example :
    Expression.Rewrite
      (Expression.comp
        unitId
        (Expression.comp (Expression.identity Partition.unit) unitId))
      (Expression.comp unitId unitId) :=
  Expression.Rewrite.comp
    (Expression.Rewrite.refl unitId)
    (Expression.Rewrite.id_left unitId)

example :
    Expression.Rewrite
      (Expression.tensor
        (Expression.comp (Expression.identity Partition.unit) unitId)
        unitId)
      (Expression.tensor unitId unitId) :=
  Expression.Rewrite.tensor
    (Expression.Rewrite.id_left unitId)
    (Expression.Rewrite.refl unitId)

example :
    Expression.Rewrite
      (Expression.copair
        (Expression.comp (Expression.identity Partition.unit) unitId)
        unitId)
      (Expression.copair unitId unitId) :=
  Expression.Rewrite.copair
    (Expression.Rewrite.id_left unitId)
    (Expression.Rewrite.refl unitId)

def unitTargetTransport :
    Expression.Transport unitId
      (Expression.comp
        (Expression.iso (Partition.PartitionIso.refl Partition.unit))
        unitId) :=
  Expression.Transport.target unitId
    (Partition.PartitionIso.refl Partition.unit)

example :
    Expression.Rewrite unitId
      (Expression.comp (Expression.identity Partition.unit) unitId) :=
  (Expression.Rewrite.id_left unitId).symm

end ArchiScriptTests.Expression
