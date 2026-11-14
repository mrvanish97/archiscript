import ArchiScriptExamples.ProofSupport
import ArchiScript.Operation.Declaration
import ArchiScript.Resolution

namespace ArchiScriptExamples.FormInput
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
def fieldPartitionLookup (x : Input) : Bool × Bool := (decide (emailProvided x), decide (nameProvided x))

def fieldMembers : Bool × Bool → Domain Input
  | (true, true) => completeForm
  | (true, false) => Domain.relativeComplement emailProvided completeForm (fun _ h => h.1)
  | (false, true) => Domain.relativeComplement nameProvided completeForm (fun _ h => h.2)
  | (false, false) => fun x => ¬ emailProvided x ∧ ¬ nameProvided x

theorem fieldPartitionLookup_correct : ∀ i x, fieldPartitionLookup x = i ↔ fieldMembers i x := by
  intro ⟨e, n⟩ x
  by_cases he : emailProvided x <;> by_cases hn : nameProvided x <;>
    cases e <;> cases n <;>
    simp [fieldPartitionLookup, fieldMembers, completeForm,
      Domain.relativeComplement, he, hn]


theorem fieldPartitionLookup_inhabited : ∀ i : Bool × Bool, ∃ x : Input, fieldPartitionLookup x = i := fun
    | (false, false) => ⟨("", ""), rfl⟩
    | (false, true) => ⟨("", "Ada"), rfl⟩
    | (true, false) => ⟨("a@example.test", ""), rfl⟩
    | (true, true) => ⟨("a@example.test", "Ada"), rfl⟩

abbrev fieldPartition : Partition :=
  partitionOfRegions Input (Bool × Bool) "fieldPartition" fieldMembers
    (⟨[(false, false), (false, true), (true, false), (true, true)], by intro ⟨e, n⟩; cases e <;> cases n <;> simp⟩) fieldPartitionLookup fieldPartitionLookup_correct
    (by
      intro i
      obtain ⟨x, hx⟩ := fieldPartitionLookup_inhabited i
      exact ⟨x, (fieldPartitionLookup_correct i x).mp hx⟩)
    (by
      obtain ⟨x, _⟩ := fieldPartitionLookup_inhabited (Classical.choice (show Nonempty (Bool × Bool) from ⟨(false, false)⟩))
      exact ⟨fieldPartitionLookup x⟩)

theorem fieldPartition_has_members : fieldPartition.HasMembers fieldMembers := by
  intro i x
  rfl

abbrev fieldSemanticPartition : SemanticPartition where
  partition := fieldPartition
  members := fieldMembers
  hasMembers := fieldPartition_has_members

/-- Three incomplete regions become one member; the carrier stays unchanged. -/
def formPartitionLookup (x : Input) : Bool := (fieldPartitionLookup x).1 && (fieldPartitionLookup x).2

def formMembers : Bool → Domain Input
  | true => completeForm
  | false => Domain.complement completeForm

theorem formPartitionLookup_correct : ∀ i x, formPartitionLookup x = i ↔ formMembers i x := by
  intro i x
  cases i <;>
    simp [formPartitionLookup, fieldPartitionLookup, formMembers,
      completeForm, Domain.complement]


theorem formPartitionLookup_inhabited : ∀ i : Bool, ∃ x : Input, formPartitionLookup x = i := fun
    | false => ⟨("", ""), rfl⟩
    | true => ⟨("a@example.test", "Ada"), rfl⟩

abbrev formPartition : Partition :=
  partitionOfRegions Input Bool "formPartition" formMembers
    (⟨[false, true], by intro i; cases i <;> simp⟩) formPartitionLookup formPartitionLookup_correct
    (by
      intro i
      obtain ⟨x, hx⟩ := formPartitionLookup_inhabited i
      exact ⟨x, (formPartitionLookup_correct i x).mp hx⟩)
    (by
      obtain ⟨x, _⟩ := formPartitionLookup_inhabited (Classical.choice (show Nonempty Bool from ⟨false⟩))
      exact ⟨formPartitionLookup x⟩)

theorem formPartition_has_members : formPartition.HasMembers formMembers := by
  intro i x
  rfl

abbrev formSemanticPartition : SemanticPartition where
  partition := formPartition
  members := formMembers
  hasMembers := formPartition_has_members

/-- The unique coarse member containing each fine field-presence member. -/
def forgetFieldFailuresMap : fieldPartition.MemberIndex → formPartition.MemberIndex :=
  fun i => i.1 && i.2

/--
The four-member field partition refines the two-member form partition. This is
semantic containment of whole fine members, not merely a total surjective label
map.
-/
theorem fieldPartition_refines_formPartition :
    fieldPartition.RefinesVia formPartition forgetFieldFailuresMap := by
  refine ⟨rfl, ?_⟩
  intro i x hx
  have hi := (fieldPartitionLookup_correct i x).mpr hx
  exact (formPartitionLookup_correct _ x).mp (by
    rw [← hi]
    rfl)

/-- The canonical coarsening map as an ordinary ArchiScript Operation. -/
def forgetFieldFailures : Operation fieldPartition formPartition :=
  Partition.coarseningOperation forgetFieldFailuresMap

theorem forgetFieldFailures_preserves_classification (x : Input) :
    forgetFieldFailures (fieldPartition.classify x) = some (formPartition.classify x) := by
  have hf := (fieldPartitionLookup_correct (fieldPartition.classify x) x).mpr (fieldPartition.classify_spec x)
  have hm : formPartitionLookup x = forgetFieldFailuresMap (fieldPartition.classify x) := by
    rw [← hf]
    rfl
  have h := (formPartition.self_member _ x).mp ((formPartitionLookup_correct _ x).mp hm)
  exact congrArg some h.symm

end ArchiScriptExamples.FormInput
