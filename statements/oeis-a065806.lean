import Mathlib

/-!
# A065806: A pseudo-random sequence.

Source: https://oeis.org/A065806
Credit: @tczyzycki

Defined by Klaus Strassburger (Nov 21 2001): initialize `b(x) = x` for all `x : ℤ`, and for
`i = 0, 1, 2, ...` set `j = b(i) - b(i - 1)`, output `a(i + 1) = j + 1` (1-indexed, offset 1),
and swap `b(i)` with `b(j)`.

The entry states four conjectures, recorded here as a conjunction in the order given:
1. For all `n ≥ 1`, `-1 < a(n) < n + 2`.
2. For all `n ≥ 1`, if `a(n) = n + 1` then `a(n + 1) = 0`.
3. Every integer `k > 1` occurs in the sequence.
4. For every `c ∈ [0, 1]`, there exists a subsequence `i_j` (strictly increasing, `i_j ≥ 1`)
   such that `(a(i_j) + 1) / (i_j + 3) → c` as `j → ∞`.
-/

namespace OMA.S_oeis_a065806

/-- The array state `b : ℤ → ℤ` before computing `a(i + 1)`: starts at `id`, and at step `i`
    swaps the entries at indices `i` and `j = b(i) - b(i - 1)`. -/
def state : ℕ → (ℤ → ℤ)
  | 0 => id
  | i + 1 =>
      let b := state i
      let j := b (i : ℤ) - b ((i : ℤ) - 1)
      fun x =>
        if x = (i : ℤ) then b j
        else if x = j then b (i : ℤ)
        else b x

/-- `A065806(n)` (1-indexed, for `n ≥ 1`). -/
def a (n : ℕ) : ℤ :=
  let i : ℕ := n - 1
  let b := state i
  b (i : ℤ) - b ((i : ℤ) - 1) + 1

theorem main :
    (∀ n : ℕ, 1 ≤ n → (-1 : ℤ) < a n ∧ a n < (n : ℤ) + 2) ∧
    (∀ n : ℕ, 1 ≤ n → a n = (n : ℤ) + 1 → a (n + 1) = 0) ∧
    (∀ k : ℤ, 1 < k → ∃ n : ℕ, 1 ≤ n ∧ a n = k) ∧
    (∀ c : ℝ, c ∈ Set.Icc (0 : ℝ) 1 →
      ∃ idx : ℕ → ℕ, StrictMono idx ∧ (∀ j, 1 ≤ idx j) ∧
        Filter.Tendsto
          (fun j => ((a (idx j) : ℝ) + 1) / ((idx j : ℝ) + 3))
          Filter.atTop (nhds c)) := by
  sorry

end OMA.S_oeis_a065806
