import ArchiScript.Presentation

namespace ArchiScriptTests.Presentation
open ArchiScript

def unitId : Presentation Partition.unit Partition.unit :=
  .atom (Operation.id Partition.unit)

def unitFamily : Presentation.Family :=
  Presentation.Family.singleton unitId

#guard unitFamily.presentations.length == 1
#guard unitFamily.targets.length == 1

example :
    Presentation.denote
      (Presentation.comp (Presentation.identity Partition.unit) unitId) =
      Presentation.denote unitId :=
  (Presentation.Rewrite.id_left unitId).sound

example :
    Presentation.denote
      (Presentation.comp unitId (Presentation.identity Partition.unit)) =
      Presentation.denote unitId :=
  (Presentation.Rewrite.id_right unitId).sound

example :
    Presentation.Rewrite
      (Presentation.comp
        (Presentation.copair unitId unitId)
        (Presentation.coproductInl Partition.unit Partition.unit))
      unitId :=
  Presentation.Rewrite.copair_inl unitId unitId

example :
    Presentation.Rewrite
      (Presentation.comp
        (Presentation.copair unitId unitId)
        (Presentation.coproductInr Partition.unit Partition.unit))
      unitId :=
  Presentation.Rewrite.copair_inr unitId unitId

example :
    Presentation.Rewrite
      (Presentation.comp
        (Presentation.comp unitId unitId)
        unitId)
      (Presentation.comp
        unitId
        (Presentation.comp unitId unitId)) :=
  Presentation.Rewrite.comp_assoc unitId unitId unitId

example :
    Presentation.Rewrite
      (Presentation.tensor
        (Presentation.identity Partition.unit)
        (Presentation.identity Partition.unit))
      (Presentation.identity (Partition.unit.tensor Partition.unit)) :=
  Presentation.Rewrite.tensor_identity _ _

example :
    Presentation.Rewrite
      (Presentation.comp
        unitId
        (Presentation.comp (Presentation.identity Partition.unit) unitId))
      (Presentation.comp unitId unitId) :=
  Presentation.Rewrite.comp
    (Presentation.Rewrite.refl unitId)
    (Presentation.Rewrite.id_left unitId)

example :
    Presentation.Rewrite
      (Presentation.tensor
        (Presentation.comp (Presentation.identity Partition.unit) unitId)
        unitId)
      (Presentation.tensor unitId unitId) :=
  Presentation.Rewrite.tensor
    (Presentation.Rewrite.id_left unitId)
    (Presentation.Rewrite.refl unitId)

example :
    Presentation.Rewrite
      (Presentation.copair
        (Presentation.comp (Presentation.identity Partition.unit) unitId)
        unitId)
      (Presentation.copair unitId unitId) :=
  Presentation.Rewrite.copair
    (Presentation.Rewrite.id_left unitId)
    (Presentation.Rewrite.refl unitId)

def unitTargetTransport :
    Presentation.Transport unitId
      (Presentation.comp
        (Presentation.iso (Partition.PartitionIso.refl Partition.unit))
        unitId) :=
  Presentation.Transport.target unitId
    (Partition.PartitionIso.refl Partition.unit)

example :
    Presentation.Rewrite unitId
      (Presentation.comp (Presentation.identity Partition.unit) unitId) :=
  (Presentation.Rewrite.id_left unitId).symm

end ArchiScriptTests.Presentation
