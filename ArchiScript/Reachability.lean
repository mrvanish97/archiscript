import ArchiScript.Partition

namespace ArchiScript.Reachability

/-- Reference closure under any finite number of transitions. No termination,
fairness, or eventual-identity statement is included. -/
inductive Reach (initial : State → Prop) (step : State → State → Prop) : State → Prop where
  | initial {x} : initial x → Reach initial step x
  | next {x y} : Reach initial step x → step x y → Reach initial step y

theorem least {initial : State → Prop} {step : State → State → Prop}
    {closed : State → Prop} (seeds : ∀ x, initial x → closed x)
    (successors : ∀ x y, closed x → step x y → closed y) :
    ∀ x, Reach initial step x → closed x := by
  intro x h
  induction h with
  | initial hi => exact seeds _ hi
  | next _ edge ih => exact successors _ _ ih edge

/-- Finiteness concerns complete semantic configurations. A finite VDP member
set alone is not a constructor for this enumeration. -/
structure FiniteAnalysis (State : Type) where
  states : List State
  complete : ∀ s, s ∈ states
  initial : State → Prop
  step : State → State → Prop
  initialDecidable : DecidablePred initial
  stepDecidable : ∀ s, DecidablePred (step s)
  stateDecidableEq : DecidableEq State

namespace FiniteAnalysis

instance (a : FiniteAnalysis State) : DecidablePred a.initial := a.initialDecidable
instance (a : FiniteAnalysis State) (x : State) : DecidablePred (a.step x) := a.stepDecidable x

/-- Fuel bounds this computation, not the reference reachability relation. -/
def compute (a : FiniteAnalysis State) : Nat → List State
  | 0 => a.states.filter (fun s => decide (a.initial s))
  | fuel + 1 =>
    letI := a.stateDecidableEq
    let before := a.compute fuel
    a.states.filter fun y => decide (y ∈ before ∨ ∃ x ∈ before, a.step x y)

theorem compute_sound (a : FiniteAnalysis State) (fuel) :
    ∀ s ∈ a.compute fuel, Reach a.initial a.step s := by
  letI := a.stateDecidableEq
  induction fuel with
  | zero =>
    intro s h
    have hi := (List.mem_filter.mp h).2
    exact .initial (of_decide_eq_true hi)
  | succ fuel ih =>
    intro s h
    have hposs : s ∈ a.compute fuel ∨ ∃ x ∈ a.compute fuel, a.step x s :=
      of_decide_eq_true (List.mem_filter.mp h).2
    rcases hposs with old | ⟨x, hx, edge⟩
    · exact ih s old
    · exact .next (ih x hx) edge

theorem seeds_in_compute (a : FiniteAnalysis State) (fuel) :
    ∀ s, a.initial s → s ∈ a.compute fuel := by
  letI := a.stateDecidableEq
  induction fuel with
  | zero =>
    intro s hs
    exact List.mem_filter.mpr ⟨a.complete s, decide_eq_true hs⟩
  | succ fuel ih =>
    intro s hs
    apply List.mem_filter.mpr
    refine ⟨a.complete s, ?_⟩
    apply decide_eq_true
    exact Or.inl (ih s hs)

def Closed (a : FiniteAnalysis State) (xs : List State) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ a.states, a.step x y → y ∈ xs

instance (a : FiniteAnalysis State) (xs : List State) : Decidable (a.Closed xs) :=
  letI := a.stateDecidableEq
  inferInstanceAs (Decidable (∀ x ∈ xs, ∀ y ∈ a.states, a.step x y → y ∈ xs))

theorem compute_complete_of_closed (a : FiniteAnalysis State) (fuel)
    (closed : a.Closed (a.compute fuel)) :
    ∀ s, Reach a.initial a.step s → s ∈ a.compute fuel :=
  least (a.seeds_in_compute fuel)
    (fun x y hx edge => closed x hx y (a.complete y) edge)

/-- Both directions are proof terms. A truncated or unstable approximation
cannot be presented as an exact result. -/
structure Exact (a : FiniteAnalysis State) where
  members : List State
  sound : ∀ s ∈ members, Reach a.initial a.step s
  complete : ∀ s, Reach a.initial a.step s → s ∈ members

def certify (a : FiniteAnalysis State) (fuel : Nat) : Option a.Exact :=
  if closed : a.Closed (a.compute fuel) then
    some ⟨a.compute fuel, a.compute_sound fuel, a.compute_complete_of_closed fuel closed⟩
  else none

theorem Exact.membership {a : FiniteAnalysis State} (result : a.Exact) (s) :
    s ∈ result.members ↔ Reach a.initial a.step s :=
  ⟨result.sound s, result.complete s⟩

end FiniteAnalysis

/-- An analyzer for a finite abstraction certifies an architectural claim only
after this exactness theorem is supplied. No finite-history premise is inferred. -/
structure ExactAbstraction (Semantic : State → Prop) (a : FiniteAnalysis State) : Prop where
  equivalent : ∀ s, Semantic s ↔ Reach a.initial a.step s

theorem certified_abstraction {Semantic : State → Prop} {a : FiniteAnalysis State}
    (abstraction : ExactAbstraction Semantic a) (result : a.Exact) (s) :
    s ∈ result.members ↔ Semantic s :=
  (result.membership s).trans (abstraction.equivalent s).symm

end ArchiScript.Reachability
