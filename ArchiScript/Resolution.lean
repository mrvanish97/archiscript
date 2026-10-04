import ArchiScript.Operation

namespace ArchiScript

namespace Partition

/--
An explicit total member map witnesses that P refines Q when both VDPs classify
one carrier and every fine semantic member is contained in its mapped coarse
member.

The public meaning is extensional member containment. The carrier equality only
transports values between the two Lean representations.
-/
def RefinesVia (P Q : Partition) (q : P.MemberIndex → Q.MemberIndex) : Prop :=
  ∃ sameCarrier : P.Carrier = Q.Carrier,
    ∀ i x, P.member i x → Q.member (q i) (sameCarrier ▸ x)

/-- Standard refinement order: some total member map preserves whole members. -/
def Refines (P Q : Partition) : Prop :=
  ∃ q : P.MemberIndex → Q.MemberIndex, P.RefinesVia Q q

/-- A proved refinement induces an ordinary total ArchiScript Operation. -/
def coarseningOperation {P Q : Partition} (q : P.MemberIndex → Q.MemberIndex) :
    Operation P Q :=
  ⟨fun i => some (q i)⟩

/-- A coarsening map is forced by semantic containment. -/
theorem coarseningMap_unique {P Q : Partition}
    {q r : P.MemberIndex → Q.MemberIndex}
    (hq : P.RefinesVia Q q) (hr : P.RefinesVia Q r) :
    q = r := by
  rcases hq with ⟨eq₁, hq⟩
  rcases hr with ⟨eq₂, hr⟩
  cases eq₁
  cases eq₂
  funext i
  obtain ⟨x, hx⟩ := P.member_nonempty i
  have hqi := hq i x hx
  have hri := hr i x hx
  change Q.classify x = q i at hqi
  change Q.classify x = r i at hri
  exact hqi.symm.trans hri

/-- Every coarse member has a fine preimage. -/
theorem coarseningMap_surjective {P Q : Partition}
    {q : P.MemberIndex → Q.MemberIndex}
    (hq : P.RefinesVia Q q) :
    Function.Surjective q := by
  rcases hq with ⟨eqCarrier, hcontain⟩
  cases eqCarrier
  intro j
  obtain ⟨x, hx⟩ := Q.member_nonempty j
  let i := P.classify x
  refine ⟨i, ?_⟩
  have hi : P.member i x := rfl
  have hqi := hcontain i x hi
  change Q.classify x = q i at hqi
  change Q.classify x = j at hx
  exact hqi.symm.trans hx

theorem refines_refl (P : Partition) : P.Refines P := by
  refine ⟨id, rfl, ?_⟩
  intro i x hx
  exact hx

theorem refines_trans {P Q R : Partition} :
    P.Refines Q → Q.Refines R → P.Refines R := by
  rintro ⟨q, eqPQ, hpq⟩ ⟨r, eqQR, hqr⟩
  refine ⟨fun i => r (q i), eqPQ.trans eqQR, ?_⟩
  intro i x hx
  have hq := hpq i x hx
  have hr := hqr (q i) (eqPQ ▸ x) hq
  simpa using hr

end Partition

namespace Operation

/-- Every source member has a defined target member. -/
def IsTotal {P Q : Partition} (f : Operation P Q) : Prop :=
  ∀ i, ∃ j, f i = some j

/-- Every target member is reached by a defined source member. -/
def IsSurjective {P Q : Partition} (f : Operation P Q) : Prop :=
  ∀ j, ∃ i, f i = some j

theorem coarseningOperation_total {P Q : Partition}
    (q : P.MemberIndex → Q.MemberIndex) :
    IsTotal (Partition.coarseningOperation q) := by
  intro i
  exact ⟨q i, rfl⟩

theorem coarseningOperation_surjective {P Q : Partition}
    {q : P.MemberIndex → Q.MemberIndex}
    (hq : P.RefinesVia Q q) :
    IsSurjective (Partition.coarseningOperation q) := by
  intro j
  obtain ⟨i, hi⟩ := Partition.coarseningMap_surjective hq j
  exact ⟨i, congrArg some hi⟩

/-- A consumer ignores every distinction collapsed by q. -/
def ConstantOnFibers {P Q Y : Partition}
    (q : Operation P Q) (f : Operation P Y) : Prop :=
  ∀ a b, q a = q b → f a = f b

/-- Ordinary morphism factorization through q. -/
def FactorsThrough {P Q Y : Partition}
    (q : Operation P Q) (f : Operation P Y) : Prop :=
  ∃ g : Operation Q Y, g.comp q = f

theorem factorsThrough_constantOnFibers {P Q Y : Partition}
    {q : Operation P Q} {f : Operation P Y}
    (h : FactorsThrough q f) :
    ConstantOnFibers q f := by
  rcases h with ⟨g, rfl⟩
  intro a b hab
  simp only [comp_apply]
  rw [hab]

/--
A proof-carrying counterexample showing that a consumer distinguishes two source
members that q places in the same fiber.
-/
structure FiberConflict {P Q Y : Partition}
    (q : Operation P Q) (f : Operation P Y) where
  left : P.MemberIndex
  right : P.MemberIndex
  sameFiber : q left = q right
  differentResult : f left ≠ f right

private def findConflictWith {P Q Y : Partition}
    (q : Operation P Q) (f : Operation P Y) (a : P.MemberIndex) :
    List P.MemberIndex → Option (FiberConflict q f)
  | [] => none
  | b :: rest =>
      if hq : q a = q b then
        if hf : f a = f b then
          findConflictWith q f a rest
        else
          some ⟨a, b, hq, hf⟩
      else
        findConflictWith q f a rest

private def scanConflicts {P Q Y : Partition}
    (q : Operation P Q) (f : Operation P Y) :
    List P.MemberIndex → Option (FiberConflict q f)
  | [] => none
  | a :: rest =>
      match findConflictWith q f a P.memberIndices with
      | some conflict => some conflict
      | none => scanConflicts q f rest

/-- Executable finite search for a concrete obstruction to factorization. -/
def firstFiberConflict {P Q Y : Partition}
    (q : Operation P Q) (f : Operation P Y) :
    Option (FiberConflict q f) :=
  scanConflicts q f P.memberIndices

/--
Choose the unique candidate coarse consumer using surjectivity of q. The
factorization theorem below states exactly when this candidate is correct.
-/
noncomputable def factorizedThrough {P Q Y : Partition}
    (q : Operation P Q) (f : Operation P Y)
    (surjective : IsSurjective q) :
    Operation Q Y where
  run j := f (Classical.choose (surjective j))

theorem factorizedThrough_spec {P Q Y : Partition}
    {q : Operation P Q} {f : Operation P Y}
    (total : IsTotal q)
    (surjective : IsSurjective q)
    (constant : ConstantOnFibers q f) :
    (factorizedThrough q f surjective).comp q = f := by
  ext i
  obtain ⟨j, hij⟩ := total i
  have hchosen := Classical.choose_spec (surjective j)
  have hsame : q (Classical.choose (surjective j)) = q i := by
    exact hchosen.trans hij.symm
  have hf := constant (Classical.choose (surjective j)) i hsame
  simp [factorizedThrough, comp, hij, hf]

theorem factorization_unique {P Q Y : Partition}
    {q : Operation P Q} {f : Operation P Y}
    (surjective : IsSurjective q)
    {g₁ g₂ : Operation Q Y}
    (h₁ : g₁.comp q = f)
    (h₂ : g₂.comp q = f) :
    g₁ = g₂ := by
  ext j
  obtain ⟨i, hij⟩ := surjective j
  have hg₁ := congrArg (fun op : Operation P Y => op i) h₁
  have hg₂ := congrArg (fun op : Operation P Y => op i) h₂
  have e₁ : g₁ j = f i := by
    simpa [comp, hij] using hg₁
  have e₂ : g₂ j = f i := by
    simpa [comp, hij] using hg₂
  exact e₁.trans e₂.symm

theorem factorsThrough_of_constantOnFibers {P Q Y : Partition}
    {q : Operation P Q} {f : Operation P Y}
    (total : IsTotal q)
    (surjective : IsSurjective q)
    (constant : ConstantOnFibers q f) :
    FactorsThrough q f :=
  ⟨factorizedThrough q f surjective,
    factorizedThrough_spec total surjective constant⟩

theorem existsUnique_factorization {P Q Y : Partition}
    {q : Operation P Q} {f : Operation P Y}
    (total : IsTotal q)
    (surjective : IsSurjective q)
    (constant : ConstantOnFibers q f) :
    ∃! g : Operation Q Y, g.comp q = f := by
  refine ⟨factorizedThrough q f surjective,
    factorizedThrough_spec total surjective constant, ?_⟩
  intro g hg
  exact factorization_unique surjective hg
    (factorizedThrough_spec total surjective constant)

end Operation

end ArchiScript
