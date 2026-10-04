import ArchiScript.Coproduct

namespace ArchiScriptExamples.Coproduct
open ArchiScript

/--
These are architecture-defined command universes. The coproduct composes the
already justified alternatives; it does not claim that an external boundary can
produce only these commands.
-/
inductive UserCommand where
  | create
  | update
  | delete
  deriving DecidableEq

inductive SystemCommand where
  | reconcile
  | expire
  deriving DecidableEq

inductive CommandDisposition where
  | accept
  | defer
  deriving DecidableEq

def userCommandPartition : Partition where
  Carrier := UserCommand
  MemberIndex := UserCommand
  carrierNonempty := ⟨.create⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.create, .update, .delete]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def systemCommandPartition : Partition where
  Carrier := SystemCommand
  MemberIndex := SystemCommand
  carrierNonempty := ⟨.reconcile⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.reconcile, .expire]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def dispositionPartition : Partition where
  Carrier := CommandDisposition
  MemberIndex := CommandDisposition
  carrierNonempty := ⟨.accept⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [.accept, .defer]
  memberIndices_complete := by intro i; cases i <;> simp
  classify := id
  member_inhabited := by intro i; exact ⟨i, rfl⟩

def commandPartition : Partition :=
  userCommandPartition.coprod systemCommandPartition

def handleUser : Operation userCommandPartition dispositionPartition where
  run
    | .create => some .accept
    | .update => some .accept
    | .delete => some .defer

def handleSystem : Operation systemCommandPartition dispositionPartition where
  run
    | .reconcile => some .accept
    | .expire => some .defer

def handleCommand : Operation commandPartition dispositionPartition :=
  Operation.copair handleUser handleSystem

end ArchiScriptExamples.Coproduct
