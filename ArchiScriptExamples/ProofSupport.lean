import ArchiScript

namespace ArchiScriptExamples
open ArchiScript

/-- Migration proof helper. The independently stated semantic regions remain
the primary members. A candidate lookup is used only as a coverage proof tool;
its correspondence with every predicate and all inhabitants must be proved. -/
abbrev partitionOfRegions (α : Type) (M : Type) [DecidableEq M]
    (name : String) (regions : M → Domain α)
    (finite : ∃ xs : List M, ∀ i, i ∈ xs)
    (lookup : α → M) (correct : ∀ i x, lookup x = i ↔ regions i x)
    (inhabited : ∀ i, ∃ x, regions i x) (hasIndex : Nonempty M) : Partition where
  Carrier := α
  MemberIndex := M
  memberIndexDecidableEq := inferInstance
  memberIndexFinite := finite
  memberIndexNonempty := hasIndex
  members := fun i => Subdomain.root name (regions i) (inhabited i) (.predicate _)
  coverage := fun x => ⟨lookup x, (correct _ _).mp rfl⟩
  disjoint := by
    intro i j different x h
    exact different (((correct _ _).mpr h.1).symm.trans ((correct _ _).mpr h.2))

end ArchiScriptExamples
