import Mathlib

/-!
# A219543: Denominators of Bernoulli numbers which are == 3 (mod 9).

Source: https://oeis.org/A219543
Credit: @ShoQo

Conjecture: "all the first differences 36, 72, 144, 72,... of the sequence are multiples of 36."
(Charles R Greathouse IV, Nov 22 2012: "The conjecture is true, since elements of A090801 are
2 mod 4.")

Formalization notes:
* The terms are the denominators `(bernoulli n).den` (A027642, A090801 is its set of distinct
  values) that are ≡ 3 (mod 9), listed in increasing order (data: 30, 66, 138, 282, ...).
* Consecutive terms of that list are in particular two such denominators, so the statement
  below, that any two denominators ≡ 3 (mod 9) differ by a multiple of 36, implies the
  conjecture for every first difference whatever the ordering of the list.
* Mathlib's `bernoulli` has B(1) = -1/2; the sign convention does not affect denominators.
-/

namespace OMA.S_oeis_a219543

theorem main : ∀ i j : ℕ, (bernoulli i).den % 9 = 3 → (bernoulli j).den % 9 = 3 →
    (36 : ℤ) ∣ ((bernoulli j).den : ℤ) - (bernoulli i).den := by
  sorry

end OMA.S_oeis_a219543
