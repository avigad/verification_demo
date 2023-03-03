import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring
import Std
import Demo.Util
import Smt
import Aesop

-- set_option smt.solver.path "..."
-- set_option smt.solver.kind "vampire"

example (n m : Int) (h : 0 < m) : n % m < m := by
  smt [h]
  sorry

example (n m k l : Int) : (n - m) * k + l = n*k - m*k + l := by
  smt
  sorry

example (n m k l : Int) (hN : n ≤ m) (hK : k ≤ l) : n + k ≤ m + l := by
  smt [hN, hK]
  sorry

theorem cong (x y : Int) (f : Int → Int) : x = y → f x = f y := by
  smt
  simp_all

@[aesop safe]
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

@[aesop safe]
theorem fib_zero : fib 0 = 0 := rfl

@[aesop safe]
theorem fib_one : fib 1 = 1 := rfl

@[aesop safe]
theorem fib_add_two (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := by
  simp [fib, add_comm]

lemma fib_add (m n : ℕ) :
    fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n generalizing m
  · case zero =>
    simp [fib]
  · case succ n ih =>
    intros
    specialize ih (m + 1)
    rw [add_assoc m 1 n, add_comm 1 n] at ih
    simp only [fib_add_two, ih]
    ring

-- lemma fib_add' (m n : ℕ) :
--     fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
--   induction n generalizing m
--   · case zero =>
--     smt [fib_zero, fib_one]
--     sorry
--   · case succ n ih =>
--     intros
--     specialize ih (m + 1)
--     smt [fib_zero, fib_one, fib_add_two, ih]
--     rw [add_assoc m 1 n, add_comm 1 n] at ih
--     simp only [fib_add_two, ih]
--     ring

lemma fib_add'' (m n : ℕ) :
    fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n generalizing m
  · case zero =>
    aesop
  · case succ n ih =>
    intros
    specialize ih (m + 1)
    rw [add_assoc m 1 n, add_comm 1 n] at ih
    simp only [fib_add_two, ih]
    ring


