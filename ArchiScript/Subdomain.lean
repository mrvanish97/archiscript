import Std

namespace ArchiScript

/-- Intermediate predicates may be empty. Named Subdomains may not. -/
abbrev Domain (α : Type u) := α → Prop

namespace Domain

def complement (s : Domain α) : Domain α := fun x => ¬ s x

def relativeComplement (parent excluded : Domain α)
    (_contained : ∀ x, excluded x → parent x) : Domain α :=
  fun x => parent x ∧ ¬ excluded x

theorem mem_complement_iff (s : Domain α) (x : α) : complement s x ↔ ¬ s x := Iff.rfl

theorem cover_complement (s : Domain α) (x : α) : s x ∨ complement s x :=
  Classical.em (s x)

theorem disjoint_complement (s : Domain α) (x : α) : ¬ (s x ∧ complement s x) :=
  fun h => h.2 h.1

end Domain

/-- Definition evidence is indexed by its actual denotation. An opaque
predicate records a boundary assumption, never an asserted proof. -/
inductive DomainDerivation (α : Type u) : Domain α → Type (u + 1) where
  | predicate (meaning : Domain α) : DomainDerivation α meaning
  | opaque (reason : String) (identified : reason ≠ "")
      (meaning : Domain α) : DomainDerivation α meaning
  | named (name : String) {meaning : Domain α}
      (definition : DomainDerivation α meaning) : DomainDerivation α meaning
  | intersection {a b : Domain α} (left : DomainDerivation α a)
      (right : DomainDerivation α b) : DomainDerivation α (fun x => a x ∧ b x)
  | union {a b : Domain α} (left : DomainDerivation α a)
      (right : DomainDerivation α b) : DomainDerivation α (fun x => a x ∨ b x)
  | relativeComplement {parent excluded : Domain α}
      (base : DomainDerivation α parent) (removed : DomainDerivation α excluded)
      (contained : ∀ x, excluded x → parent x) :
      DomainDerivation α (Domain.relativeComplement parent excluded contained)

def DomainDerivation.hasOpaque {meaning : Domain α}
    (definition : DomainDerivation α meaning) : Bool :=
  match definition with
  | .predicate _ => false
  | .opaque _ _ _ => true
  | .named _ d => d.hasOpaque
  | .intersection left right | .union left right => left.hasOpaque || right.hasOpaque
  | .relativeComplement base removed _ => base.hasOpaque || removed.hasOpaque

/-- A declared semantic region, including its justified base and an inhabitant.
There is no disjointness requirement between arbitrary Subdomains. -/
structure Subdomain (α : Type u) where
  name : String
  base : Domain α
  parent : DomainDerivation α base
  meaning : Domain α
  contained : ∀ x, meaning x → base x
  definition : DomainDerivation α meaning
  nonempty : ∃ x, meaning x

namespace Subdomain

def root (name : String) (meaning : Domain α) (nonempty : ∃ x, meaning x)
    (definition : DomainDerivation α meaning) : Subdomain α where
  name := name
  base := fun _ => True
  parent := .predicate (fun _ => True)
  meaning := meaning
  contained := fun _ _ => True.intro
  definition := .named name definition
  nonempty := nonempty

/-- Refinement retains the entire parent's semantics, not just its name. -/
def child (name : String) (parent : Subdomain α) (criterion : Domain α)
    (nonempty : ∃ x, parent.meaning x ∧ criterion x) : Subdomain α where
  name := name
  base := parent.meaning
  parent := .named parent.name parent.definition
  meaning := fun x => parent.meaning x ∧ criterion x
  contained := fun _ h => h.1
  definition := .intersection (.named parent.name parent.definition) (.predicate criterion)
  nonempty := nonempty

def remainder (name : String) (parent excluded : Subdomain α)
    (within : ∀ x, excluded.meaning x → parent.meaning x)
    (nonempty : ∃ x, parent.meaning x ∧ ¬ excluded.meaning x) : Subdomain α where
  name := name
  base := parent.meaning
  parent := .named parent.name parent.definition
  meaning := Domain.relativeComplement parent.meaning excluded.meaning within
  contained := fun _ h => h.1
  definition := .relativeComplement (.named parent.name parent.definition)
    (.named excluded.name excluded.definition) within
  nonempty := nonempty

end Subdomain

/-- Proof helper for one declared split. Several splits may have the same root.
Every registered split is a value of this type, never an unchecked claim. -/
structure SemanticSplit (parent : Subdomain α) where
  Index : Type v
  indices : List Index
  indices_complete : ∀ i, i ∈ indices
  indexNonempty : Nonempty Index
  indexDecidableEq : DecidableEq Index
  children : Index → Subdomain α
  within : ∀ i x, (children i).meaning x → parent.meaning x
  covers : ∀ x, parent.meaning x → ∃ i, (children i).meaning x
  disjoint : ∀ i j, i ≠ j → ∀ x, ¬ ((children i).meaning x ∧ (children j).meaning x)

namespace SemanticSplit

def singleton (parent : Subdomain α) : SemanticSplit parent where
  Index := Unit
  indices := [()]
  indices_complete := by intro i; cases i; simp
  indexNonempty := ⟨()⟩
  indexDecidableEq := inferInstance
  children := fun _ => parent
  within := fun _ _ h => h
  covers := fun _ h => ⟨(), h⟩
  disjoint := by intro i j h; exact False.elim (h (Subsingleton.elim _ _))

/-- Exact positive/remainder split, retaining the parent's excluded values. -/
def complement (parent positive : Subdomain α)
    (within : ∀ x, positive.meaning x → parent.meaning x)
    (remainderName : String)
    (remainderNonempty : ∃ x, parent.meaning x ∧ ¬ positive.meaning x) :
    SemanticSplit parent where
  Index := Bool
  indices := [false, true]
  indices_complete := by intro i; cases i <;> simp
  indexNonempty := ⟨false⟩
  indexDecidableEq := inferInstance
  children
    | true => positive
    | false => parent.remainder remainderName positive within remainderNonempty
  within := by intro i x h; cases i; exact h.1; exact within x h
  covers := by
    intro x hx
    by_cases h : positive.meaning x
    · exact ⟨true, h⟩
    · exact ⟨false, hx, h⟩
  disjoint := by
    intro i j different x h
    cases i <;> cases j
    · exact different rfl
    · exact h.1.2 h.2
    · exact h.2.2 h.1
    · exact different rfl

/-- Flatten proved child splits. The leaves cover the original parent by
deduction; overlap in a different tree is immaterial. -/
def refine {parent : Subdomain α} (s : SemanticSplit parent)
    (below : (i : s.Index) → SemanticSplit (s.children i)) : SemanticSplit parent where
  Index := (i : s.Index) × (below i).Index
  indices := s.indices.flatMap fun i => (below i).indices.map fun j => ⟨i, j⟩
  indices_complete := by
    intro ⟨i, j⟩
    exact List.mem_flatMap.mpr ⟨i, s.indices_complete i,
      List.mem_map.mpr ⟨j, (below i).indices_complete j, rfl⟩⟩
  indexNonempty := by
    obtain ⟨i⟩ := s.indexNonempty
    obtain ⟨j⟩ := (below i).indexNonempty
    exact ⟨⟨i, j⟩⟩
  indexDecidableEq := by
    letI := s.indexDecidableEq
    letI := fun i => (below i).indexDecidableEq
    infer_instance
  children := fun ij => (below ij.1).children ij.2
  within := fun ij x h => s.within ij.1 x ((below ij.1).within ij.2 x h)
  covers := by
    intro x hx
    obtain ⟨i, hi⟩ := s.covers x hx
    obtain ⟨j, hj⟩ := (below i).covers x hi
    exact ⟨⟨i, j⟩, hj⟩
  disjoint := by
    intro ⟨i, j⟩ ⟨k, l⟩ different x h
    by_cases hik : i = k
    · subst k
      exact (below i).disjoint j l (by intro e; subst l; exact different rfl) x h
    · exact s.disjoint i k hik x
        ⟨(below i).within j x h.1, (below k).within l x h.2⟩

end SemanticSplit
end ArchiScript
