import Mathlib

/-!
# A005157: Number of totally symmetric plane partitions in an n x n x n box.

Source: https://oeis.org/A005157
Credit: @rabdelaal

The product formula (Paul Barry, 2008) `a n = prod_{1<=i<=j<=k<=n} (i+j+k-1)/(i+j+k-2)`
gives the count (OEIS A005157); read in `ZMod (p^2)` the denominators are units for
`p` prime and `1 <= i <= j <= k <= p`.

OEIS A005157 records the conjectures (Peter Bala, 2023): if `p = 1 (mod 6)` is prime
then `a p = 2 ^ ((p+5)/6) (mod p^2)`; if `p = 5 (mod 6)` is prime then
`a p = 2 ^ ((p+1)/6) (mod p^2)`.
-/

namespace OMA.S_oeis_a005157

/-- The OEIS A005157 entry, evaluated in `ZMod (p^2)` by its triple product formula
(the integer `a n`, reduced mod `p^2`). -/
noncomputable def aP (p : ℕ) : ZMod (p ^ 2) :=
  ∏ i ∈ Finset.Icc 1 p, ∏ j ∈ Finset.Icc i p, ∏ k ∈ Finset.Icc j p,
    (↑(i + j + k - 1) : ZMod (p ^ 2)) * (↑(i + j + k - 2) : ZMod (p ^ 2))⁻¹

/-- The congruences recorded in OEIS A005157 (Bala): for a prime `p`, according to
`p mod 6`, `aP p` matches the stated power of two in `ZMod (p^2)`. -/
theorem main : ∀ p : ℕ, Nat.Prime p →
    (p % 6 = 1 → aP p = (2 ^ ((p + 5) / 6) : ℕ)) ∧
    (p % 6 = 5 → aP p = (2 ^ ((p + 1) / 6) : ℕ)) := by
  sorry

end OMA.S_oeis_a005157
