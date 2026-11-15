import ArchiScriptExamples.SharedTargets
import ArchiScriptExamples.CyclicCone

namespace ArchiScriptTests.TerminalOccurrences
open ArchiScript ArchiScriptExamples.SharedTargets

-- One nominal C, with two automatically derived coordinates, including when
-- both incoming Operations and their images agree extensionally.
example : (signature 0 id).output ⟨2, by decide⟩ =
    (signature 0 id).output ⟨3, by decide⟩ := rfl
example : equalImages.model.effect () =
    .tensor (.node ⟨3, by decide⟩) (.tensor (.node ⟨3, by decide⟩) .unit) := rfl
example : (equalImages.model.S.effectCoordinates equalImages.model.effectAnalysis ()).length = 2 := rfl
example : (leftC 0 id).history ≠ (rightC 0 id).history := by decide
example : equalImages.model.reachEffect () (false, (false, ())) :=
  (base_joint_relation id false false).mpr rfl
example : ¬ equalImages.model.reachEffect () (false, (true, ())) := by
  rw [base_joint_relation]; decide

-- Full left image, singleton right image: the relation remains source-correlated.
example : differentImages.model.reachEffect () (false, (true, ())) :=
  (base_joint_relation (fun _ => true) false true).mpr rfl
example : differentImages.model.reachEffect () (true, (true, ())) :=
  (base_joint_relation (fun _ => true) true true).mpr rfl
example : ¬ differentImages.model.reachEffect () (false, (false, ())) := by
  rw [base_joint_relation]; decide
example (value : Bool) : differentImages.model.effectIncoming () (.inl ()) value :=
  incoming_left_image (fun _ => true) value
example : ¬ differentImages.model.effectIncoming () (.inr (.inl ())) false := by
  intro incoming
  obtain ⟨root, impossible⟩ := (incoming_right_image (fun _ => true) false).mp incoming
  cases impossible
example (value : Bool) : equalImages.model.effectIncoming () (.inr (.inl ())) value :=
  (incoming_right_image id value).mpr ⟨value, rfl⟩

-- Both marginals are full, yet the joint image is the anti-diagonal.
example : correlatedImages.model.reachEffect () (false, (true, ())) :=
  (base_joint_relation Bool.not false true).mpr rfl
example : correlatedImages.model.reachEffect () (true, (false, ())) :=
  (base_joint_relation Bool.not true false).mpr rfl
example : ¬ correlatedImages.model.reachEffect () (true, (true, ())) := by
  rw [base_joint_relation]; decide

-- One h;k declaration, one E; equal and different images both retain two slots.
example : sharedSuffix.model.effect () =
    .tensor (.node ⟨5, by decide⟩) (.tensor (.node ⟨5, by decide⟩) .unit) := rfl
example : sharedSuffix.model.reachEffect () (true, (true, ())) :=
  (suffix_joint_relation id true true).mpr rfl
example : ¬ sharedSuffix.model.reachEffect () (false, (true, ())) := by
  rw [suffix_joint_relation]; decide
example : differentSuffix.model.reachEffect () (false, (true, ())) :=
  (suffix_joint_relation (fun _ => true) false true).mpr rfl
example : (sharedChain.supply (leftC 2 id)).history ≠
    (sharedChain.supply (rightC 2 id)).history := by decide

-- Even identical values cannot supply the wrong producer-derived slot.
def collapsed : (signature 0 id).Occurrence (equalImages.model.effect ()) :=
  .tensor (leftC 0 id) (.tensor (leftC 0 id) .unit)

theorem collapsed_rejected : ¬ equalImages.model.EffectProvenance () collapsed := by
  intro faithful
  have wrong := faithful (.inr (.inl ()))
  change ProducerHistory.operation (2 : Fin 4) (.operation 0 (.cause () ())) =
    ProducerHistory.operation 3 (.operation 1 (.cause () ())) at wrong
  cases wrong

-- The candidate product does not add a join to the generator inventory.
example : (signature 0 id).generators.length = 4 := rfl
example (g : (signature 0 id).Generator) :
    ∃ n, (signature 0 id).input g = .node n := ⟨sourceIndex 0 g, rfl⟩

abbrev redundantBasis : (signature 0 id).ProvenanceAnalysis (fun _ => none) :=
  { baseBasis id with entries := (baseBasis id).entries ++ (baseBasis id).entries }
example : (signature 0 id).effectInputs redundantBasis () = equalImages.model.effect () := rfl

end ArchiScriptTests.TerminalOccurrences
