import ArchiScriptExamples.SharedTargets

namespace ArchiScriptTests.SharedTargetCycles
open ArchiScript ArchiScriptExamples ArchiScriptExamples.SharedTargets

-- Extend the same four-node graph by one loop at its single C.
abbrev signature : ArchitectureSignature := {
  SharedTargets.signature 0 id with
  Generator := Sum (Fin 4) Unit
  generatorDecidableEq := inferInstance
  generators := (List.finRange 4).map Sum.inl ++ [.inr ()]
  generators_complete := by
    intro g; cases g with
    | inl i => exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    | inr u => cases u; simp
  input := fun | .inl g => (SharedTargets.signature 0 id).input g | .inr _ => .node 3
  output := fun | .inl g => (SharedTargets.signature 0 id).output g | .inr _ => 3
  operation := fun | .inl g => (SharedTargets.signature 0 id).operation g | .inr _ => Operation.id bit
  localFactor := by
    intro g; cases g with
    | inl g => exact (SharedTargets.signature 0 id).localFactor g
    | inr u => exact ⟨3, List.mem_cons_self, rfl⟩ }

def boundary : ArchitectureSignature.Term.CycleBoundary signature 3 where
  route := ArchitectureSignature.Term.operation (S := signature)
    (Hole := fun n => PLift ((3 : Fin 4) = n)) (.inr ())
      (ArchitectureSignature.Term.hole (S := signature)
        (Hole := fun n => PLift ((3 : Fin 4) = n)) 3 ⟨rfl⟩)
  oneEntry := rfl
  nontrivial := by decide

abbrev marked : signature.Markers := fun n =>
  if same : n = 3 then some (same.symm ▸ boundary) else none
abbrev basis : signature.ProvenanceAnalysis marked := derive_provenance([()], 2)
example : basis.Valid := ⟨by intro r; cases r; simp, by decide⟩

abbrev fromLeft : signature.Occurrence (.node 3) :=
  ArchitectureSignature.Term.operation (S := signature) (.inl 2)
    (ArchitectureSignature.Term.operation (S := signature) (.inl 0)
      (ArchitectureSignature.Term.cause (S := signature) () ()))
abbrev fromRight : signature.Occurrence (.node 3) :=
  ArchitectureSignature.Term.operation (S := signature) (.inl 3)
    (ArchitectureSignature.Term.operation (S := signature) (.inl 1)
      (ArchitectureSignature.Term.cause (S := signature) () ()))

def repeatReturn : Nat → signature.Occurrence (.node 3) → signature.Occurrence (.node 3)
  | 0, t => t
  | n + 1, t => ArchitectureSignature.Term.operation (S := signature) (.inr ()) (repeatReturn n t)

theorem repeat_provenance (n : Nat) (t : signature.Occurrence (.node 3)) :
    (repeatReturn n t).provenance marked = t.provenance marked := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change signature.normalizeOperation marked (.inr ()) ((repeatReturn n t).provenance marked) = _
    rw [ih]
    rfl

example (n m : Nat) : (repeatReturn n fromLeft).provenance marked ≠
    (repeatReturn m fromRight).provenance marked := by
  rw [repeat_provenance, repeat_provenance]
  decide
example : (signature.effectCoordinates basis ()).map Prod.fst = [3, 3] := rfl

end ArchiScriptTests.SharedTargetCycles
