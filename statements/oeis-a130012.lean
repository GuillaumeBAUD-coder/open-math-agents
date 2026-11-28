import Mathlib

/-!
# A130012: Smallest natural number whose cube is the sum of n cubes of distinct natural numbers, or 0 if no such number exists.

Source: https://oeis.org/A130012
Credit: @azmiozgen

Conjecture (Zhining Yang, Apr 24 2026): the sequence is nondecreasing for n > 4.

Formalization notes:
* Natural numbers are the positive integers here (offset 1, a(1) = 1, a(3) = 6 from
  3^3 + 4^3 + 5^3 = 6^3). a(n) is the least k ≥ 1 such that k^3 is the sum of the cubes of n
  distinct positive integers; when there is none, `sInf ∅ = 0` gives the entry's value 0
  (a(2) = 0 by Fermat's Last Theorem for exponent 3).
* Nondecreasing for n > 4 is stated as a(n) ≤ a(n+1) for every n > 4.
* Controls: a search over k ≤ 15 gives a(1..7) = 1, 0, 6, 13, 9, 13, 14, as in the entry.
-/

namespace OMA.S_oeis_a130012

/-- A130012(n): the least `k ≥ 1` with `k³` a sum of `n` cubes of distinct positive integers,
or `0` if there is none. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ∃ S : Finset ℕ, S.card = n ∧ 0 ∉ S ∧ ∑ x ∈ S, x ^ 3 = k ^ 3}

/-- Yang's conjecture: `a` is nondecreasing from `n = 5` on. -/
theorem main : ∀ n : ℕ, 4 < n → a n ≤ a (n + 1) := by
  sorry

end OMA.S_oeis_a130012
