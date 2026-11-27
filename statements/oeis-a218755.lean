import Mathlib

/-!
# A218755: Denominators of Bernoulli numbers which are == 6 (mod 9).

Source: https://oeis.org/A218755
Credit: @ShoQo

Conjecture: "all first differences 36, 288, 180, 180,... of the sequence are multiples of 36."
(Charles R Greathouse IV, Nov 22 2012: "The conjecture is true, since elements of A090801 are
2 mod 4.")

Formalization notes:
* The terms are the denominators `(bernoulli n).den` (A027642, A090801 is its set of distinct
  values) that are ≡ 6 (mod 9), listed in increasing order (data: 6, 42, 330, 510, ...).
* Consecutive terms of that list are in particular two such denominators, so the statement
  below, that any two denominators ≡ 6 (mod 9) differ by a multiple of 36, implies the
  conjecture for every first difference whatever the ordering of the list.
* Mathlib's `bernoulli` has B(1) = -1/2; the sign convention does not affect denominators.
-/

namespace OMA.S_oeis_a218755

theorem main : ∀ i j : ℕ, (bernoulli i).den % 9 = 6 → (bernoulli j).den % 9 = 6 →
    (36 : ℤ) ∣ ((bernoulli j).den : ℤ) - (bernoulli i).den := by
  sorry

end OMA.S_oeis_a218755
