import Mathlib

/-!
# A284815: Least number k such that k mod (2, 3, 4, ..., n+1) = (d_n, d_n-1, ..., d_1), where d_1, d_2, ..., d_n are the digits of k, with MSD(k) = d_1 and LSD(k) = d_n. 0 if such a number does not exist.

Source: https://oeis.org/A284815
Credit: @jagraj28

Conjecture (Max Alekseyev, 2022, stated in A284815): `a(n) = 0` for all `n ≥ 15`, that is, for
`n ≥ 15` no number `k` has this property.

Formalization notes:
* `k` has `n` decimal digits `d_1, …, d_n` (most significant first), so `k mod (j + 1)` is
  compared with `d_{n+1-j}` for `j = 1, …, n`. `Nat.digits 10 k` lists the digits least
  significant first, `[d_n, …, d_1]`, so the condition reads `k % (j + 2) = (Nat.digits 10 k)[j]`
  for `j < n`, with `(Nat.digits 10 k).length = n`.
* `a(n) = 0` means that no such `k` exists (a number with `n ≥ 1` digits is positive).
* A brute-force search gives the listed values `a(1), …, a(6) = 1, 10, 0, 1101, 11311, 340210`
  with this reading.
-/

namespace OMA.S_oeis_a284815

/-- `k` has `n` decimal digits and `k mod (2, 3, …, n + 1)` are its digits from the least
significant to the most significant. -/
def Matches (n k : ℕ) : Prop :=
  (Nat.digits 10 k).length = n ∧
    ∀ j (hj : j < (Nat.digits 10 k).length), k % (j + 2) = (Nat.digits 10 k)[j]

/-- The conjecture of A284815: for `n ≥ 15` there is no such `k`. -/
theorem main : ∀ n : ℕ, 15 ≤ n → ∀ k : ℕ, ¬ Matches n k := by
  sorry

end OMA.S_oeis_a284815
