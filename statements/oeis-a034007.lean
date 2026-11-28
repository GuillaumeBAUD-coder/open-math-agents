import Mathlib

/-!
# A034007: First differences of A045891.

Source: https://oeis.org/A034007
Credit: @<your GitHub handle>

The entry records two conjectures (Gregory L. Simay, Feb 18 and Feb 20 2018):

"Conjecture 1: For compositions of n+k-1, a(n) is the number of runs of 1 of length k. Example:
Among the compositions of 4+2-1 = 5, there are a(4) = 4 runs of two 1's: 3,[1,1]; [1,1],3;
1,2,[1,1] and [1,1],2,1."

"Conjecture 2: More generally, let R(n,m,k) = the number of runs of k m's in all compositions of
n. Then R(n,m,k) = A045623(n-m*k) - 2*A045623(n-m*(k+1)) + A045623(n-m*(k+2)). For example,
R(7,1,1) = A045623(6) - 2*A045623(5) + A045623(4) = 144 - 2*64 + 28 = 44 = a(7)."

Conventions (please review):
* `a034007 n` is A034007 with the entry's offset `0`: `1, 0, 2, 4, 9, 20, 44, 96, ...`. We use the
  formula recorded in the entry (N. J. A. Sloane): `a(n) = Sum_{k=0..n-3} (k+4) C(n-3,k)` for
  `n ≥ 3`, with `a(0) = 1, a(1) = 0, a(2) = 2`.
* Indexing in Conjecture 1: both worked examples in the entry use `a(n)` one step later than the
  offset-0 data (`a(4) = 4` and `a(7) = 44`, while the data has `a(3) = 4`, `a(6) = 44`). We follow
  the examples: the number of runs of exactly `k` ones in all compositions of `n + k - 1` equals
  the offset-0 term `a034007 (n - 1)`, for `n ≥ 1` and `k ≥ 1`. (With the literal offset-0 reading
  the claim already fails at `n = 0`.) The trailing "= a(7)" of Conjecture 2's example is only an
  illustration and is not part of `main`.
* A "run of k m's" in a composition (an ordered list of positive parts) is a maximal block of
  exactly `k` consecutive parts equal to `m`. `runCount m k l` counts them in the list `l`.
  `R n m k` sums this over all compositions of `n` (Mathlib's `Composition n`). Conjecture 2 is
  stated for `m ≥ 1`, `k ≥ 1` (parts are positive; a run has positive length).
* A045623(j) (offset 0: `1, 2, 5, 12, 28, 64, 144, ...`) is, by its definition, the number of 1's in
  all compositions of `j + 1`. Arguments `n - m*k` etc. may be negative; there A045623 is taken
  to be `0` (the convention under which the formula is meant, e.g. `R(n,m,k) = 0` for `n < m*k`).
-/

namespace OMA.S_oeis_a034007

/-- A034007 (offset 0): `a(0) = 1`, `a(1) = 0`, `a(2) = 2`,
`a(n) = Sum_{k=0..n-3} (k+4) C(n-3,k)` for `n ≥ 3`. -/
def a034007 (n : ℕ) : ℕ :=
  if n = 0 then 1 else if n = 1 then 0 else if n = 2 then 2
  else ∑ k ∈ Finset.range (n - 2), (k + 4) * Nat.choose (n - 3) k

/-- Number of maximal runs of exactly `k` consecutive entries equal to `m` in the list `l`:
positions `i` such that `l[i], ..., l[i+k-1]` all equal `m`, and neither `l[i-1]` (if `i > 0`)
nor `l[i+k]` (if it exists) equals `m`. -/
def runCount (m k : ℕ) (l : List ℕ) : ℕ :=
  (List.range l.length).countP fun i =>
    (List.range k).all (fun t => decide (i + t < l.length ∧ l.getD (i + t) 0 = m)) &&
    (i == 0 || l.getD (i - 1) 0 != m) && (i + k == l.length || l.getD (i + k) 0 != m)

/-- `R(n,m,k)`: the number of runs of `k` `m`'s in all compositions of `n`. -/
def R (n m k : ℕ) : ℕ := ∑ c : Composition n, runCount m k c.blocks

/-- A045623(j): the number of 1's in all compositions of `j + 1`. -/
def a045623 (j : ℕ) : ℕ := ∑ c : Composition (j + 1), c.blocks.count 1

/-- A045623 extended by `0` to negative arguments. -/
def a045623Z (j : ℤ) : ℤ := if j < 0 then 0 else (a045623 j.toNat : ℤ)

/-- Simay's Conjectures 1 and 2 in OEIS A034007. -/
theorem main :
    (∀ n k : ℕ, 1 ≤ n → 1 ≤ k → R (n + k - 1) 1 k = a034007 (n - 1)) ∧
    (∀ n m k : ℕ, 1 ≤ m → 1 ≤ k →
      (R n m k : ℤ) = a045623Z ((n : ℤ) - m * k) - 2 * a045623Z ((n : ℤ) - m * (k + 1)) +
        a045623Z ((n : ℤ) - m * (k + 2))) := by
  sorry

end OMA.S_oeis_a034007
