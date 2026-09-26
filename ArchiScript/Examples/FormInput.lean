import ArchiScript.Operation

namespace ArchiScript.Examples.FormInput
open ArchiScript

/-- The boundary supplies two arbitrary strings, including empty ones. -/
abbrev Input := String × String

-- These predicates model presence only, not email syntax or personal-name validity.
def emailProvided : Domain Input := fun x => x.1 ≠ ""
def nameProvided : Domain Input := fun x => x.2 ≠ ""
def completeForm : Domain Input := fun x => emailProvided x ∧ nameProvided x

instance (x : Input) : Decidable (emailProvided x) := inferInstanceAs (Decidable (x.1 ≠ ""))
instance (x : Input) : Decidable (nameProvided x) := inferInstanceAs (Decidable (x.2 ≠ ""))

/-- Four distinctions for a consumer that needs field-specific failures. -/
def fieldPartition : Partition where
  Carrier := Input
  MemberIndex := Bool × Bool
  carrierNonempty := ⟨("", "")⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [(false, false), (false, true), (true, false), (true, true)]
  memberIndices_complete := by intro ⟨e, n⟩; cases e <;> cases n <;> simp
  classify x := (decide (emailProvided x), decide (nameProvided x))
  member_inhabited
    | (false, false) => ⟨("", ""), rfl⟩
    | (false, true) => ⟨("", "Ada"), rfl⟩
    | (true, false) => ⟨("a@example.test", ""), rfl⟩
    | (true, true) => ⟨("a@example.test", "Ada"), rfl⟩

def fieldRegions : fieldPartition.MemberIndex → Domain Input
  | (true, true) => completeForm
  | (true, false) => Domain.relativeComplement emailProvided completeForm (fun _ h => h.1)
  | (false, true) => Domain.relativeComplement nameProvided completeForm (fun _ h => h.2)
  | (false, false) => fun x => ¬ emailProvided x ∧ ¬ nameProvided x

theorem fieldPartition_realizes_regions : fieldPartition.Realizes fieldRegions := by
  intro ⟨e, n⟩ x
  by_cases he : emailProvided x <;> by_cases hn : nameProvided x <;>
    cases e <;> cases n <;>
    simp [Partition.member, fieldPartition, fieldRegions, completeForm,
      Domain.relativeComplement, he, hn]

/-- Three incomplete regions become one member; the carrier stays unchanged. -/
def formPartition : Partition where
  Carrier := Input
  MemberIndex := Bool
  carrierNonempty := ⟨("", "")⟩
  memberIndexDecidableEq := inferInstance
  memberIndices := [false, true]
  memberIndices_complete := by intro i; cases i <;> simp
  classify x := (fieldPartition.classify x).1 && (fieldPartition.classify x).2
  member_inhabited
    | false => ⟨("", ""), rfl⟩
    | true => ⟨("a@example.test", "Ada"), rfl⟩

def formRegions : formPartition.MemberIndex → Domain Input
  | true => completeForm
  | false => Domain.complement completeForm

theorem formPartition_realizes_regions : formPartition.Realizes formRegions := by
  intro i x
  cases i <;>
    simp [Partition.member, formPartition, fieldPartition, formRegions,
      completeForm, Domain.complement]

/-- The member map forgets detail; it does not transform the input strings. -/
def forgetFieldFailures : Operation fieldPartition formPartition where
  run i := some (i.1 && i.2)

theorem forgetFieldFailures_preserves_classification (x : Input) :
    forgetFieldFailures (fieldPartition.classify x) = some (formPartition.classify x) := rfl

end ArchiScript.Examples.FormInput
