import Mathlib

/-!
# Show this number always is composite number

Source: https://mathoverflow.net/questions/299705 (2018), cross-posted as
https://math.stackexchange.com/questions/2771998.
Credit: @jagraj28

Conjecture of the post: for every positive integer `m`,
`f(m) = (2m) ^ (2m+1) + m ^ (2m+1) · (2m+1) ^ m + (2m+1) ^ (2m)` is not a prime number.
For odd `m`, `f(m)` is even; the post checks even `m ≤ 1300`, and comments give covering
congruences for some residue classes (for example `5 ∣ f(m)` when `m ≡ 8 (mod 20)`). Neither copy
of the question has an answer.

Formalization notes:
* `m` is a positive natural number and `f m` is computed in `ℕ`.
* "Not a prime number" is `¬ (f m).Prime`.
* A direct primality test finds no prime value for `1 ≤ m ≤ 150`.
-/

namespace OMA.S_mo_299705

/-- `f(m) = (2m)^(2m+1) + m^(2m+1) (2m+1)^m + (2m+1)^(2m)`. -/
def f (m : ℕ) : ℕ :=
  (2 * m) ^ (2 * m + 1) + m ^ (2 * m + 1) * (2 * m + 1) ^ m + (2 * m + 1) ^ (2 * m)

/-- The conjecture: `f(m)` is never prime for a positive integer `m`. -/
theorem main : ∀ m : ℕ, 0 < m → ¬ (f m).Prime := by
  sorry

end OMA.S_mo_299705
