import Mathlib

/-!
# Is there a permutation `π ∈ Sₙ` with `∑_{0<k<n} 1 / (π(k)² - π(k+1)²) = 0` for each `n > 7`?

Source: https://mathoverflow.net/questions/316208 (Zhi-Wei Sun, 2018).
Credit: @jagraj28

The post asks whether, for each `n = 8, 9, …`, some permutation `π` of `{1, …, n}` satisfies
`∑_{0<k<n} 1 / (π(k)² - π(k+1)²) = 0`, and conjectures a positive answer. The post and its
comments give examples for `8 ≤ n ≤ 13`; OEIS A322099 counts such permutations (with
`π(1) < π(n)`) and is positive for `8 ≤ n ≤ 15`. The post has no answer.

Formalization notes:
* A permutation `π` of `{1, …, n}` is written as the list `[π(1), …, π(n)]`: a list that is a
  permutation of `List.range' 1 n = [1, …, n]`.
* The sum runs over consecutive pairs `(π(k), π(k+1))`, `1 ≤ k ≤ n - 1`
  (`List.zipWith` of the list with its tail), and is computed in `ℚ`. The entries are distinct
  positive integers, so no denominator is zero.
-/

namespace OMA.S_mo_316208

/-- `∑_{0<k<n} 1 / (π(k)² - π(k+1)²)` for the list `[π(1), …, π(n)]`. -/
def adjSum (l : List ℕ) : ℚ :=
  (List.zipWith (fun x y : ℕ => 1 / ((x : ℚ) ^ 2 - (y : ℚ) ^ 2)) l l.tail).sum

/-- Sun's conjecture: for every `n > 7` some permutation of `{1, …, n}` makes the sum zero. -/
theorem main : ∀ n : ℕ, 7 < n → ∃ l : List ℕ, l.Perm (List.range' 1 n) ∧ adjSum l = 0 := by
  sorry

end OMA.S_mo_316208
