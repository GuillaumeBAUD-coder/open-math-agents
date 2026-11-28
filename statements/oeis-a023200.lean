import Mathlib

/-!
# A023200: a Firoozbakht-type conjecture for cousin primes

Source: https://oeis.org/A023200
Credit: @jagraj28

A023200 lists the primes `p` such that `p + 4` is also prime (3, 7, 13, 19, 37, ...). The entry
records a conjecture of Jahangeer Kholdi and Farideh Firoozbakht (2014): the sequence is infinite
and for every `n`, `a(n+1) < a(n)^(1 + 1/n)`; that is, `a(n)^(1/n)` is strictly decreasing.

`main` is the conjunction of the two parts.

Conventions: the sequence has offset 1, so `a(n)` is the `n`-th such prime with `a(1) = 3`, in
Mathlib `Nat.nth S (n - 1)`; the inequality is stated for every `n ≥ 1`, with a real power.
A check of the inequality for all such primes below `10^6` finds no exception.
-/

namespace OMA.S_oeis_a023200

/-- The terms of OEIS A023200: primes `p` with `p + 4` prime. -/
def S : Set ℕ := {p | p.Prime ∧ (p + 4).Prime}

/-- `a n`: the `n`-th term, with `a 1 = 3`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (· ∈ S) (n - 1)

/-- The Kholdi–Firoozbakht conjecture in OEIS A023200. -/
theorem main :
    S.Infinite ∧
    ∀ n : ℕ, 1 ≤ n → (a (n + 1) : ℝ) < (a n : ℝ) ^ (1 + 1 / (n : ℝ)) := by
  sorry

end OMA.S_oeis_a023200
