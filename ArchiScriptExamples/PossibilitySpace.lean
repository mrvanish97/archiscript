import ArchiScript.Operation

/-!
One external lobby-entry click is interpreted against a declared mathematical
scenario boundary: an arbitrary waiting budget and an optional readiness delay,
both measured in abstract natural-number ticks. `none` in `readyAfter` means
that this scenario never becomes ready; a delay beyond the budget is also a
timeout scenario. Readiness at the deadline counts as success.

This is not raw-input validation, a simulator, or a prediction available to the
running program at click time. The interpretation assumes that readiness can be
summarized by this delay; cancellations, malformed requests and other real-world
conditions need their own declared semantics if they matter. The carrier has
not been restricted to successful delays or three outcome constructors.

`click` is the sole proposed starting VDP for that one event. This independent
example proves its semantic partition and member map only; it does not construct
or certify a Cause inventory, a Cone, a tensor use, or implementation liveness.
-/
namespace ArchiScriptExamples.PossibilitySpace
open ArchiScript

structure Scenario where
  budget : Nat
  readyAfter : Option Nat
  deriving DecidableEq

def shortMeaning (s : Scenario) : Prop :=
  ∃ delay, s.readyAfter = some delay ∧ delay ≤ 2 ∧ delay ≤ s.budget

def longMeaning (s : Scenario) : Prop :=
  ∃ delay, s.readyAfter = some delay ∧ 2 < delay ∧ delay ≤ s.budget

def timeoutMeaning (s : Scenario) : Prop :=
  match s.readyAfter with
  | none => True
  | some delay => s.budget < delay

def scenarios : Subdomain Scenario :=
  Subdomain.root "ClickScenario" (fun _ => True) ⟨⟨0, none⟩, trivial⟩ (.predicate _)

def shortWait : Subdomain Scenario :=
  scenarios.child "ShortWait" shortMeaning
    ⟨⟨5, some 1⟩, trivial, 1, rfl, by decide, by decide⟩

def longWait : Subdomain Scenario :=
  scenarios.child "LongWait" longMeaning
    ⟨⟨5, some 4⟩, trivial, 4, rfl, by decide, by decide⟩

def timeout : Subdomain Scenario :=
  scenarios.child "Timeout" timeoutMeaning ⟨⟨5, none⟩, trivial, trivial⟩

inductive WaitClass where
  | shortWait | longWait | timeout
  deriving DecidableEq

def region : WaitClass → Subdomain Scenario
  | .shortWait => shortWait
  | .longWait => longWait
  | .timeout => timeout

theorem short_not_long (s : Scenario) : ¬ (shortMeaning s ∧ longMeaning s) := by
  rintro ⟨⟨a, ha, short, _⟩, ⟨b, hb, long, _⟩⟩
  have same : a = b := Option.some.inj (ha.symm.trans hb)
  omega

theorem short_not_timeout (s : Scenario) : ¬ (shortMeaning s ∧ timeoutMeaning s) := by
  rintro ⟨⟨delay, ready, _, within⟩, late⟩
  simp only [timeoutMeaning, ready] at late
  omega

theorem long_not_timeout (s : Scenario) : ¬ (longMeaning s ∧ timeoutMeaning s) := by
  rintro ⟨⟨delay, ready, _, within⟩, late⟩
  simp only [timeoutMeaning, ready] at late
  omega

def scenarioSplit : SemanticSplit scenarios where
  Index := WaitClass
  indices := [.shortWait, .longWait, .timeout]
  indices_complete := by intro i; cases i <;> simp
  indexNonempty := ⟨.shortWait⟩
  indexDecidableEq := inferInstance
  children := region
  within := by intro _ _ _; trivial
  covers := by
    intro s _
    cases ready : s.readyAfter with
    | none => exact ⟨.timeout, trivial, by simp [timeoutMeaning, ready]⟩
    | some delay =>
      by_cases within : delay ≤ s.budget
      · by_cases short : delay ≤ 2
        · exact ⟨.shortWait, trivial, delay, ready, short, within⟩
        · exact ⟨.longWait, trivial, delay, ready, by omega, within⟩
      · exact ⟨.timeout, trivial, by simp only [timeoutMeaning, ready]; omega⟩
  disjoint := by
    intro i j different s h
    cases i <;> cases j
    · exact different rfl
    · exact short_not_long s ⟨h.1.2, h.2.2⟩
    · exact short_not_timeout s ⟨h.1.2, h.2.2⟩
    · exact short_not_long s ⟨h.2.2, h.1.2⟩
    · exact different rfl
    · exact long_not_timeout s ⟨h.1.2, h.2.2⟩
    · exact short_not_timeout s ⟨h.2.2, h.1.2⟩
    · exact long_not_timeout s ⟨h.2.2, h.1.2⟩
    · exact different rfl

abbrev click : VDP := Partition.ofSplit scenarioSplit (fun _ => trivial)

inductive Decision where
  | success | timeout
  deriving DecidableEq

abbrev result : VDP := Partition.closed Decision "Decision"
  ⟨[.success, .timeout], by intro d; cases d <;> simp⟩ ⟨.success⟩

def decide : Operation click result where
  run
    | .shortWait | .longWait => some .success
    | .timeout => some .timeout

theorem all_scenarios_covered (s : Scenario) : ∃ i, click.member i s := click.coverage s

theorem all_regions_nonempty (i : WaitClass) : ∃ s, click.member i s :=
  click.member_nonempty i

theorem regions_disjoint (i j : WaitClass) (different : i ≠ j) (s : Scenario) :
    ¬ (click.member i s ∧ click.member j s) := click.disjoint different s

/-- The broad boundary includes immediate readiness even with zero budget. -/
example : click.member .shortWait ⟨0, some 0⟩ := ⟨trivial, 0, rfl, by decide, by decide⟩

/-- Equality with the deadline remains in the successful long-wait region. -/
example : click.member .longWait ⟨5, some 5⟩ := ⟨trivial, 5, rfl, by decide, by decide⟩

/-- A late arrival and no arrival are different values in the same timeout region. -/
example : click.member .timeout ⟨5, some 6⟩ := ⟨trivial, Nat.lt_succ_self 5⟩
example : click.member .timeout ⟨5, none⟩ := ⟨trivial, trivial⟩

/-- Arbitrarily large delays remain present rather than being filtered out. -/
example (delay : Nat) : click.member .timeout ⟨delay, some (delay + 1)⟩ :=
  ⟨trivial, Nat.lt_succ_self delay⟩

example : decide .shortWait = some .success := rfl
example : decide .longWait = some .success := rfl
example : decide .timeout = some .timeout := rfl

/-- One Operation cannot introduce a missing distinction at a coarse input member. -/
theorem no_hidden_branch {X : Partition} (f : Operation X result) (i : X.MemberIndex) :
    ¬ (f i = some .success ∧ f i = some .timeout) := by
  rintro ⟨success, timedOut⟩
  have impossible := f.single_output success timedOut
  cases impossible

end ArchiScriptExamples.PossibilitySpace
