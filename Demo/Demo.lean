import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring
import Std
import Demo.Util

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

#eval fib 15
#eval List.map fib (List.range 20)

--set_option trace.Meta.Tactic.simp.rewrite true in
theorem fib_add_two {n : ℕ} : fib (n + 2) = fib n + fib (n + 1) := by
  simp [fib, add_comm]

lemma fib_add (m n : ℕ) :
    fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n generalizing m
  case zero =>
    simp [fib]
  case succ n ih =>
    specialize ih (m + 1)
    rw [add_assoc m 1 n, add_comm 1 n] at ih
    simp only [fib_add_two, ih]
    ring

def fib₀ : Nat → Nat
  | 0 => 0
  | n + 1 => (aux n).2
where
  aux : Nat → Nat × Nat
    | 0 => (0, 1)
    | n + 1 =>
      let (a, b) := aux n
      (b, a + b)

#eval fib₀ 1000

lemma fib₀_aux_eq (n : Nat) : fib₀.aux n = (fib n, fib (n + 1)) := by
  induction n
  . simp [fib]
  . next _ ih => simp [fib₀.aux, fib, ih, add_comm]

@[csimp] theorem fib_eq : fib = fib₀ := by
  ext n
  cases n <;> simp [fib, fib₀, fib₀_aux_eq, add_comm]

#eval fib 1000

def fib₁ (n : Nat) :=
  aux n 0 1
where aux : Nat → Nat → Nat → Nat
  | 0, _, b => b
  | n+1, a, b => aux n b (a + b)

#eval fib₁ 400000
-- #eval fib₁ 400000

def fib₂ (n : Nat) : Nat := Id.run do
  let mut p := (0, 1)
  for _ in [:n] do
    let (a, b) := p
    p := (b, a + b)
  return p.1

#eval fib₂ 100

def fib₃ (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [:n] do
    let temp := a
    a := b
    b := temp + b
  return b

def fib₄ (n : Nat) : { m // m = fib n } :=
  let ⟨pair, property⟩ :=
  loop_with_invariant
    (invariant := fun i p => p = (fib i, fib (i + 1)))
    (start_state := (0, 1))
    (init := by simp [fib])
    (next_state := fun i p =>
      let (a, b) := p
      (b, a + b))
    (step := by intro i; simp [fib, add_comm])
    n
  ⟨pair.1, by simp [property]⟩

#eval fib₄ 10000

def fib₅ (n : Nat) : { m // m = fib n } :=
  for i upto n
    state: p := (0, 1)
    invariant: inv := p = (fib i, fib (i + 1))
    init:= by simp
    next:
      let (a, b) := p
      (b, a + b)
    step:= by intro i; simp [fib, add_comm]
  ⟨p.1, by simp [inv]⟩

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
set_option trace.Meta.synthInstance true in
example : (x + 2) + 2 = x + 4 := by simp [add_assoc]

#check add_assoc