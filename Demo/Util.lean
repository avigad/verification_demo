import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring

open BigOperators
open Finset

/-
Consider a simple imperative program in Lean.
-/

def foo (n : Nat) : Nat := Id.run do
  let mut sum := 0
  for i in [:n] do
    sum := sum + i
  sum

#eval foo 10

/-
How do we prove that it does what it is supposed to? Well, the program translates essentially to
the following tail-recursive version.
-/

def foo_tail_recursive (n : Nat) : Nat :=
  go n 0 0
where
  go : (b : Nat) → (i : Nat) → (sum : Nat) → Nat
  | 0,       _, sum => sum
  | (b + 1), i, sum => go b (i + 1) (sum + i)

/-
In that form, it is not hard to add the invariants. Note that there are three proof obligations:
showing that the initial invariant holds, showing that it is preserved, and showing that, when
you exit the loop, the final invariant suffices for whatever comes next.
-/

def foo_with_invariant (n : Nat) : { sum : Nat // sum = ∑ i in range n, i } :=
  -- show that the initial invariant holds
  have : n + 0 = n ∧ 0 = Finset.sum (range 0) id := by
    constructor
    . rw [add_zero]
    . rw [sum_range_zero]
  go n 0 0 this
where
  go : (b : Nat) → (i : Nat) → (sum : Nat) →
      (hinv : b + i = n ∧ sum = ∑ j in range i, j ) → { sum : Nat // sum = ∑ j in range n, j }
  | 0,       i, sum, hinv => by
      -- show that the final state of the loop yields the function postcondition
      use sum
      rw [zero_add] at hinv
      rw [hinv.2, hinv.1]
  | (b + 1), i, sum, hinv =>
    have : b + (i + 1) = n ∧ sum + i = ∑ j in range (i + 1), j := by
      -- show that the invariant is preserved
      constructor
      . rw [add_comm i, ←add_assoc, hinv.1]
      . rw [sum_range_succ, hinv.2]
    go b (i + 1) (sum + i) this

/-
It's easy to abstract this. For simplicity, let's stick to loops that start from 0, but we can
allow arbitrary states and invariants. This is the analogue of a recursor that Mario had in mind.
-/

def loop_with_invariant {State : Type _}
      (invariant : Nat → State → Prop)
      (start_state : State)
      (init : invariant 0 start_state)
      (next_state : Nat → State → State)
      (step : ∀ i state, invariant i state → invariant (i + 1) (next_state i state))
      (n : Nat) :
    { state // invariant n state } :=
  have : n + 0 = n ∧ invariant 0 start_state := by
    constructor
    . rw [add_zero]
    . trivial
  go n 0 start_state this
where
  go : (b : Nat) → (i : Nat) → (state : State) →
      (hinv : b + i = n ∧ invariant i state) → { state : State // invariant n state }
  | 0,       i, state, hinv => by
      use state
      rw [zero_add] at hinv
      rw [←hinv.1]
      exact hinv.2
  | (b + 1), i, state, hinv =>
    have : b + (i + 1) = n ∧ invariant (i + 1) (next_state i state) := by
      constructor
      . rw [add_comm i, ←add_assoc, hinv.1]
      . exact step _ _ hinv.2
    go b (i + 1) (next_state i state) this

/-
With this simple gadget, it is a lot easier to do the loop plumbing. It is natural to write the
function `foo` as follows. Notice that if you replace any of the proof obligations with an
underscore, Lean tells you what the obligations are.
-/

def nicer_foo (n : Nat) : {sum : Nat // sum = ∑ j in range n, j } :=
  let ⟨sum, property⟩ := loop_with_invariant
    (invariant := fun i sum => sum = ∑ j in range i, j )
    (start_state := 0)
    -- show invariant holds initially
    (init := rfl)
    (next_state := fun i sum => sum + i)
    -- show invariant is preserved
    (step := by rintro i state rfl; rw [sum_range_succ])
    n
  -- show that final state and invariant satisfies the postcondition
  ⟨sum, property⟩

/-
In this case, the final invariant is exactly the postcondition, so we can be even briefer.
-/

def nicer_foo_alt (n : Nat) : {sum : Nat // sum = ∑ j in range n, j } :=
  loop_with_invariant
    (invariant := fun i sum => sum = ∑ j in range i, j )
    (start_state := 0)
    (init := rfl)
    (next_state := fun i sum => sum + i)
    (step := by rintro i state rfl; rw [sum_range_succ])
    n

/-
It shouldn't be too hard to turn the more general formulation into something like the following
syntax:
def foo (n : Nat) : { sum : Nat // sum = ∑ j in range n, j } := Id.run do
  let mut sum := 0
  for i in [:n] with inv
    {invariant: sum = ∑ j in range i, j}
    {init := rfl}
  do
    sum := sum + i
    {step := by rintro i state rfl; rw [sum_range_succ]}
  ⟨sum, inv⟩
Replacing any of the obligations by an underscore should show us what they are, and it should be
possible to use any Lean proof to fill them. Ideally, they should all be filled with `by auto`,
or annotations that are almost as short and easy to write. Indeed, it would be good to have syntax
that silently calls generic automation whenever the proofs are left out.
It might even be nice to introduce something like `{assert: ...}` syntax for `have` clauses,
and similar notation for preconditions and postconditions. Users might find it attractive to have
notation that separates computation from proof obligations. It's a somewhat perverse (though
admittedly useful) fact that dependent type theory blurs the distinction between them.
So what do we need to do to replace Why3 by Lean?
- Generalize the loop construction to all the things handled by "do unchained."
- Get better back-end automation to fill in most of the proof obligations. Ideally, the automation
  will be proof producing, but even trusted automation that allows better user interaction will
  be a win over Why3.
For the first, we need to generalize to arbitrary iterables and handle early returns, as well as
nested loops. It would be helpful to think about this in algebraic terms, and to think about how
the operations compose. What we are using is essentially what people call a "Dijsktra monad,"
described nicely in Section 3 of the paper "Dijkstra monads forever." The name is a misnomer,
since it really isn't a monad; it's a monad plus the invariants on the monad. But the point is
there is a way of composing things nicely, so we should just adapt the "do unchained" notation
to something like that framework.
-/

-- open Lean

example : 2 = 2 :=
  calc
    2 = 2 := sorry
    _ = 2 := sorry

-- syntax calcStep := ppIndent(colGe term " := " withPosition(term))
-- syntax calcSteps := ppLine withPosition(calcStep) ppLine withPosition((calcStep ppLine)*)

syntax "for" ident "upto" term
  withPosition("state:" ident ":=" term
  "invariant:" ident ":=" term
  "init:=" term
  "next:" term
  "step:=" term)
  term : term

macro_rules
  | `(for $i upto $n
        state: $s := $start_state
        invariant: $p := $inv
        init:= $init
        next: $next_state
        step:= $step
      $rest) =>
      `(let ⟨$s, $p⟩ := loop_with_invariant
          (invariant := fun $i $s => $inv)
          (start_state := $start_state)
          (init := $init)
          (next_state := fun $i $s => $next_state)
          (step := $step)
          $n
        $rest)

