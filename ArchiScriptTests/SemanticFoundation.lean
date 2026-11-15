import ArchiScript
import ArchiScriptExamples.ProjectReference

namespace ArchiScriptTests.SemanticFoundation
open ArchiScript

def root : Subdomain (Bool × Bool) :=
  .root "two coordinates" (fun _ => True) ⟨(false, false), trivial⟩ (.predicate _)

def first : Subdomain (Bool × Bool) :=
  .child "first true" root (fun p => p.1 = true) ⟨(true, false), trivial, rfl⟩

def second : Subdomain (Bool × Bool) :=
  .child "second true" root (fun p => p.2 = true) ⟨(false, true), trivial, rfl⟩

def firstTree : SemanticSplit root :=
  .complement root first first.contained "first false" ⟨(false, true), trivial, by rintro ⟨_, h⟩; cases h⟩

def secondTree : SemanticSplit root :=
  .complement root second second.contained "second false" ⟨(true, false), trivial, by rintro ⟨_, h⟩; cases h⟩

example : first.meaning (true, true) ∧ second.meaning (true, true) :=
  ⟨⟨trivial, rfl⟩, ⟨trivial, rfl⟩⟩

example (p : Bool × Bool) : ∃ i, (firstTree.children i).meaning p := firstTree.covers p trivial
example (p : Bool × Bool) : ∃ i, (secondTree.children i).meaning p := secondTree.covers p trivial

def naturals : Subdomain Nat := .root "Nat" (fun _ => True) ⟨0, trivial⟩ (.predicate _)
def positive : Subdomain Nat := .child "positive" naturals (fun n => 0 < n) ⟨1, trivial, by decide⟩
def naturalSplit : SemanticSplit naturals :=
  .complement naturals positive positive.contained "zero" ⟨0, trivial, by rintro ⟨_, h⟩; omega⟩
abbrev infiniteCarrier : VDP := Partition.ofSplit naturalSplit (fun _ => trivial)

example (n : Nat) : ∃ i, infiniteCarrier.member i n := infiniteCarrier.coverage n
example : infiniteCarrier.MemberIndex = Bool := rfl

def emptyString : Subdomain String := .root "empty string" (fun s => s = "") ⟨"", rfl⟩ (.predicate _)
def emptyArray : Subdomain (List Nat) := .root "empty array" (fun s => s = []) ⟨[], rfl⟩ (.predicate _)
def absentValue : Subdomain (Option Nat) := .root "absent" (fun x => x = none) ⟨none, rfl⟩ (.predicate _)

example : ∃ s, emptyString.meaning s := emptyString.nonempty
example : ∃ s, emptyArray.meaning s := emptyArray.nonempty
example : ∃ s, absentValue.meaning s := absentValue.nonempty
example : ¬ (∃ _ : Nat, False) := by rintro ⟨_, impossible⟩; exact impossible

abbrev bit : VDP := Partition.closed Bool "Boolean" ⟨[false, true], by intro b; cases b <;> simp⟩ ⟨false⟩
def constant : Operation bit bit := ⟨fun _ => some true⟩
def partialMap : Operation bit bit := ⟨fun | false => none | true => some true⟩

example (b : Bool) : constant.image (fun _ => True) b ↔ b = true := by
  constructor
  · rintro ⟨_, _, h⟩
    exact (Option.some.inj h).symm
  · intro h; subst b; exact ⟨false, trivial, rfl⟩

example : ¬ Operation.IsSurjective constant := by
  intro h
  obtain ⟨i, hi⟩ := h false
  cases hi

example : ¬ partialMap.image (fun _ => True) false := by
  rintro ⟨i, _, hi⟩
  cases i <;> cases hi

example : bit.member false false := rfl
example : ¬ bit.member false true := by change ¬ true = false; decide

end ArchiScriptTests.SemanticFoundation
