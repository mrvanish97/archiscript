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
      (Expression.tensor
        (Expression.identity Partition.unit)
        (Expression.identity Partition.unit))
      (Expression.identity (Partition.unit.tensor Partition.unit)) :=
  Expression.Rewrite.tensor_identity _ _

end ArchiScriptTests.Expression
