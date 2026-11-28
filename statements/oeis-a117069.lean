import Mathlib

/-!
# A117069: Leading terms in rows obtained by repeatedly computing consecutive absolute differences, starting with the squares of prime numbers.

Source: https://oeis.org/A117069
Credit: @luciusacarr

Conjecture (Pe's conjecture, as recorded in the entry). For any positive integer n, the number of
prime leading elements in the first n rows is greater than the number of composite leading
elements. (The source adds: in the first million rows, only 70767 leading terms are composite.)

Reading of the source:
* Row 0 is the sequence of squares of primes 4, 9, 25, 49, 121, ...; row `j + 1` is the sequence
  of absolute differences of consecutive terms of row `j`. `D j i` is the `i`-th term (from 0) of
  row `j`, with `prime(0) = 2` written `Nat.nth Nat.Prime 0`.
* The sequence is `a(n) = D n 0` for `n ≥ 1` (offset 1: a(1) = 5, a(2) = 11, a(3) = 3, a(4) = 37,
  ...), so "the first n rows" are the difference rows 1, ..., n, whose leading elements are
  a(1), ..., a(n).
* "Composite" means `1 < m` and `m` is not prime. A leading element equal to `0` or `1` is counted
  as neither.

Not stated here: a further comment in the entry proposes a generalization to n-th powers of primes
with "k-almost prime leading elements, 0 < k < n"; as written its range of `k` is empty for
`n = 1`, contradicting the comment's own remark that `n = 1` gives a weak form of Gilbreath's
conjecture, so its intended meaning is unclear. Only Pe's conjecture is formalized.
-/

namespace OMA.S_oeis_a117069

/-- `D j i`: the `i`-th term of row `j` of the absolute-difference table whose row 0 is the
squares of the primes. -/
noncomputable def D : ℕ → ℕ → ℕ
  | 0, i => (Nat.nth Nat.Prime i) ^ 2
  | j + 1, i => Nat.dist (D j (i + 1)) (D j i)

/-- A117069: the leading term of difference row `n` (for `n ≥ 1`). -/
noncomputable def a (n : ℕ) : ℕ := D n 0

theorem main :
    ∀ n : ℕ, 0 < n →
      ((Finset.Icc 1 n).filter (fun j => 1 < a j ∧ ¬ (a j).Prime)).card <
        ((Finset.Icc 1 n).filter (fun j => (a j).Prime)).card := by
  sorry

end OMA.S_oeis_a117069
