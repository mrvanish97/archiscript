import ArchiScript
import ArchiScriptExamples.FormInput

namespace ArchiScriptTests.Domains
open ArchiScript ArchiScriptExamples.FormInput

-- Supporting subdomains may overlap and need not cover the whole carrier.
example : emailProvided ("a@example.test", "Ada") ∧ nameProvided ("a@example.test", "Ada") := by
  decide

example : ¬ emailProvided ("", "") ∧ ¬ nameProvided ("", "") := by decide

-- The intersection has both parents; neither parent requires a global tree.
example (x : Input) (h : completeForm x) : emailProvided x ∧ nameProvided x := h

-- Relative complement must stay inside its parent.
example : ¬ Domain.relativeComplement emailProvided completeForm (fun _ h => h.1) ("", "") := by
  unfold Domain.relativeComplement completeForm
  decide
example : Domain.relativeComplement emailProvided completeForm (fun _ h => h.1)
    ("a@example.test", "") := by
  unfold Domain.relativeComplement completeForm
  decide

example : fieldPartition.HasMembers fieldMembers := fieldPartition_has_members
example : formPartition.HasMembers formMembers := formPartition_has_members

-- Concrete counterexamples rule out treating the supporting domains as members.
example : ¬ formPartition.HasMembers (fun | true => emailProvided | false => nameProvided) := by
  intro h
  have bad := (h false ("a@example.test", "Ada")).mpr (by decide)
  exact bad ⟨by decide, by decide⟩

-- The incomplete member must include mixed cases, not just both-empty inputs.
example : ¬ formPartition.HasMembers
    (fun | true => completeForm | false => fun x => ¬ emailProvided x ∧ ¬ nameProvided x) := by
  intro h
  have bad := (h false ("a@example.test", "")).mp (by intro hb; exact hb.2 rfl)
  exact bad.1 (by decide)

-- All three incomplete combinations survive and share one coarser member.
#guard fieldPartitionLookup ("", "") == (false, false)
#guard fieldPartitionLookup ("", "Ada") == (false, true)
#guard fieldPartitionLookup ("a@example.test", "") == (true, false)
#guard fieldPartitionLookup ("a@example.test", "Ada") == (true, true)
#guard formPartitionLookup ("", "") == false
#guard formPartitionLookup ("", "Ada") == false
#guard formPartitionLookup ("a@example.test", "") == false
#guard formPartitionLookup ("a@example.test", "Ada") == true

example (x : Input) : forgetFieldFailures (fieldPartition.classify x) =
    some (formPartition.classify x) := forgetFieldFailures_preserves_classification x

-- Ordinary flat declarations and aliases compile without missing-tree warnings.
#guard_msgs in
def flat : Partition := formPartition

#guard_msgs in
def aliasComposition : Operation formPartition flat :=
  (Operation.id flat).comp (Operation.id formPartition)

end ArchiScriptTests.Domains
