import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring
import Std
import Demo.Util

def fib : Nat → Nat := sorry

-- set_option trace.Meta.Tactic.simp.rewrite true in
-- theorem fib_add_two {n : ℕ} : fib (n + 2) = fib n + fib (n + 1) := by
--   simp [fib, add_comm]

lemma fib_add (m n : ℕ) :
    fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  sorry

def fib₀ : Nat → Nat := sorry

-- lemma fib₀_aux_eq (n : Nat) : fib₀.aux n = (fib n, fib (n + 1)) := by

def fib₁ (n : Nat) :=
  aux n 0 1
where aux : Nat → Nat → Nat → Nat := sorry

-- #eval fib₁ 400000

def fib₂ (n : Nat) : Nat := Id.run do
  let mut p := (0, 1)
  for _ in [:n] do
    let (a, b) := p
    p := (b, a + b)
  return p.1

def fib₄ (n : Nat) : { m // m = fib n } :=
  let ⟨pair, property⟩ :=
  loop_with_invariant
    (invariant := sorry)
    (start_state := (0, 1))
    (init := sorry)
    (next_state := fun i p =>
      sorry)
    (step := sorry)
    n
  sorry

def fib₅ (n : Nat) : { m // m = fib n } := sorry


/-
Notes.

Conventional wisdom:
- Functional programming is easier to reason about.
- Functional proramming is better for concurrency.
- Imperative programming is more efficient.

Lean somewhat simulates an imperative style.
It uses dynamic arrays with destructive updates when they are not shared.
The standard library has arrays and hashmaps.

Two questions:
- Are the imperative features good enough for real applications? Which ones?
- Can we reason about them?

Two big Lean programming projects:
- https://github.com/leanprover/lean4
- https://github.com/leanprover-community/duper

Thesis: we should be able to simulate the functionality of e.g. Dafny.
- SMT proofs can be trusted, reconstructed, or checked.
- We can use varying degrees of interaction.
- Lean can call external functions and link them to reference implementations

-/

-- set_option trace.Meta.Tactic.simp true in
-- set_option trace.Meta.synthInstance true in
example : (x + 2) + 2 = x + 4 := by simp [add_assoc]

#check add_assoc