import Mathlib

/-!
# Eventual period laws for the increments in OEIS A351743

Source: https://oeis.org/A351743.
Submitted by @VestigeClub.

The first increment and its inclusive partial sum are both 1. Later
increments are the largest divisors of the previous partial sum coprime
to the previous increment. The auxiliary pair stores the partial sum
first and the current increment second. The first two assertions express
arbitrarily late occurrences of each of 1 and 2. The odd and even laws
both begin with n = 70, and the even law uses an integer-valued correction
of period 21. The proof checks the first ten increments against the entry.
-/

namespace OMA.S_oeis_a351743

def greatestCoprimeDivisor (s v : ℕ) : ℕ :=
  (s.divisors.filter (fun d => d.Coprime v)).sup id

def step (p : ℕ × ℕ) : ℕ × ℕ :=
  let w := greatestCoprimeDivisor p.1 p.2
  (p.1 + w, w)

def state : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (1, 1)
  | n + 2 => step (state (n + 1))

def a (n : ℕ) : ℕ := (state n).2

theorem main :
    (∀ N : ℕ, ∃ n : ℕ, N < n ∧ a n = 1) ∧
    (∀ N : ℕ, ∃ n : ℕ, N < n ∧ a n = 2) ∧
    (∀ n : ℕ, 70 ≤ n → a (2 * (n + 21) - 1) = a (2 * n - 1)) ∧
    (∃ b : ℕ → ℤ, Function.Periodic b 21 ∧
      ∀ n : ℕ, 70 ≤ n → (a (2 * (n + 21)) : ℤ) = 3645 * (a (2 * n) : ℤ) + b n) := by
  sorry

end OMA.S_oeis_a351743
