import Mathlib

/-!
# A308121: Irregular triangle read by rows: T(n,k) = A109395(n)*k - A076512(n)*A038566(n,k).

Source: https://oeis.org/A308121

Conjecture in the entry (Charlie Neder, Jun 05 2019):
If n is odd, then row 2n can be obtained from row n by interchanging the first and second
halves.

Formalization notes:
* Offset 1: rows are indexed by n ≥ 1 and row n has length A000010(n) = phi(n), with
  1 ≤ k ≤ phi(n). The data begin 0, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1 (rows 1 to 6).
* A038566(n,k) is the k-th number in [1, n] coprime to n, in increasing order (row 1 is the
  single number 1). Here `coprimes n` is that list.
* A109395(n) is the denominator and A076512(n) the numerator of phi(n)/n. Both are read off
  the reduced rational number phi(n)/n in Mathlib (`Rat.den` and `Rat.num`), as in the names
  of those entries and in the PARI program of this entry. All arithmetic in T is in the
  integers, since T can be negative.
* `row n` is the list T(n,1), ..., T(n,phi(n)); the k-th entry (k starting at 1) uses k and
  the k-th coprime number.
* Interchanging the first and second halves of row n means: the last phi(n)/2 values,
  followed by the first phi(n)/2 values, keeping order inside each half. This needs row n to
  have even length. For odd n ≥ 3 the length phi(n) is even, so the split is exact. For n = 1
  the row has length 1 and has no halves (row 1 is 0 and row 2 is 1), so the claim is stated
  for odd n with n > 1.
-/

namespace OMA.S_oeis_a308121

/-- A038566 row n: the numbers in [1, n] coprime to n, in increasing order. -/
def coprimes (n : ℕ) : List ℕ := (List.range' 1 n).filter (fun k => Nat.Coprime k n)

/-- A076512(n): the numerator of phi(n)/n. -/
def num (n : ℕ) : ℤ := ((Nat.totient n : ℚ) / (n : ℚ)).num

/-- A109395(n): the denominator of phi(n)/n. -/
def den (n : ℕ) : ℤ := (((Nat.totient n : ℚ) / (n : ℚ)).den : ℤ)

/-- Row n of A308121: T(n,k) = A109395(n)*k - A076512(n)*A038566(n,k), for k = 1, ..., phi(n).
The list index i corresponds to k = i + 1. -/
def row (n : ℕ) : List ℤ :=
  (coprimes n).mapIdx (fun i t => den n * ((i : ℤ) + 1) - num n * (t : ℤ))

/-- Neder's conjecture on A308121: for odd n > 1, row 2n is row n with its first and second
halves interchanged. -/
theorem main :
    ∀ n : ℕ, Odd n → 1 < n →
      row (2 * n) = (row n).drop (Nat.totient n / 2) ++ (row n).take (Nat.totient n / 2) := by
  sorry

end OMA.S_oeis_a308121
