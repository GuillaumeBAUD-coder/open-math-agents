import Mathlib

/-!
# A000425: Coefficients of ménage hit polynomials.

Source: https://oeis.org/A000425
Credit: @thatoneguy006

The two conjectures recorded in the entry (R. J. Mathar, Nov 02 2015):

  Conjecture: (n-1)*(n-3)*a(n) -n*(n-2)*(n-3)*a(n-1) -n*(n-1)*(n-3)*a(n-2) -n *(n-1)*a(n-3)=0.
  Conjecture: a(n) = 2*n*A000271(n).

Definitions.
* A000425 (offset 1: 2, 0, 0, 8, 30, 192, 1344, 10800, ...). Its terms are the coefficients of
  t^1 in the ménage hit polynomials: for n >= 2, a(n) is the number of permutations s of
  {0, ..., n-1} with exactly one hit, a hit being a position i with s(i) = i or
  s(i) = i + 1 (mod n). This reproduces the data for n = 2..9. For n = 1 the two forbidden
  positions coincide and the data gives a(1) = 2 (Riordan's convention), which is used as is.
* A000271 (offset 0: 1, 0, 0, 1, 3, 16, 96, ...) is the number of permutations p of
  {0, ..., n-1} with p(i) - i not in {0, 1} (Andrew Howroyd, in A000271).

Reading.
* The recurrence is stated for n >= 4, where all of a(n-3), ..., a(n) are terms; it holds on the
  data for n = 4..9.
* With A000271 at its offset 0, the second conjecture read literally contradicts the data
  (n = 1: 2*1*A000271(1) = 0 but a(1) = 2; n = 4: 2*4*A000271(4) = 24 but a(4) = 8), while
  a(n) = 2*n*A000271(n-1) holds for every n of the data (2 = 2*1*1, 8 = 2*4*1, 30 = 2*5*3,
  192 = 2*6*16, ...). The conjecture is therefore read with that index shift.
-/

namespace OMA.S_oeis_a000425

open Finset

/-- The number of hits of `s`: positions `i` with `s i = i` or `s i = i + 1 (mod n)`. -/
def hits {n : ℕ} (s : Equiv.Perm (Fin n)) : ℕ :=
  (univ.filter (fun i : Fin n => s i = i ∨ (s i).val = (i.val + 1) % n)).card

/-- A000425: `a 1 = 2`, and for `n ≥ 2` the permutations of `Fin n` with exactly one hit. -/
def a (n : ℕ) : ℕ :=
  if n = 1 then 2 else (univ.filter (fun s : Equiv.Perm (Fin n) => hits s = 1)).card

/-- A000271: permutations `p` of `Fin n` with `p i - i ∉ {0, 1}`. -/
def A000271 (n : ℕ) : ℕ :=
  (univ.filter (fun p : Equiv.Perm (Fin n) =>
    ∀ i : Fin n, (p i).val ≠ i.val ∧ (p i).val ≠ i.val + 1)).card

/-- Mathar's two conjectures (the second with the index shift explained above). -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      ((n : ℤ) - 1) * ((n : ℤ) - 3) * a n - (n : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * a (n - 1)
        - (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 3) * a (n - 2)
        - (n : ℤ) * ((n : ℤ) - 1) * a (n - 3) = 0) ∧
    (∀ n : ℕ, 1 ≤ n → a n = 2 * n * A000271 (n - 1)) := by
  sorry

end OMA.S_oeis_a000425
