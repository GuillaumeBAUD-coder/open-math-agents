import Mathlib

/-!
# Dividing up the unrestricted partitions

Conjecture of David S. Newman, recorded at
https://www.openproblemgarden.org/op/dividing_up_the_unrestricted_partitions.

The generating function of the unrestricted partitions is
`(1 + x + x^2 + ⋯)(1 + x^2 + x^4 + ⋯)(1 + x^3 + x^6 + ⋯)⋯ = ∑ p(n) x^n`.
The conjecture: some of the plus signs can be changed to minus signs so that every coefficient
of the resulting product is `1`, `-1` or `0`.

Reading of the source: the constant term `1` of each factor keeps its sign (it is not preceded by
a plus sign), and each term `x^(j*k)` with `j ≥ 1` of the `k`-th factor independently gets a sign.
The infinite product converges `x`-adically; since the `k`-th factor is `1` modulo `x^k`, the
coefficient of `x^n` in the whole product equals the coefficient of `x^n` in the finite product of
the factors `k = 1, …, n`, which is how it is computed below.

Credit: @Hennyrick
-/

namespace OMA.S_opg_dividing_up_the_unrestricted_partitions

/-- The `k`-th factor `1 ± x^k ± x^(2k) ± ⋯`, where `flip k j = true` means the sign in front of
`x^(j*k)` (for `j ≥ 1`) has been changed to minus. -/
noncomputable def signedFactor (flip : ℕ → ℕ → Bool) (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun m =>
    if m = 0 then 1
    else if k ∣ m then (if flip k (m / k) then -1 else 1)
    else 0

/-- The coefficient of `x^n` in the infinite product `∏_{k ≥ 1} signedFactor flip k`. -/
noncomputable def signedCoeff (flip : ℕ → ℕ → Bool) (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∏ k ∈ Finset.Icc 1 n, signedFactor flip k)

/-- Newman's conjecture: the signs can be chosen so that every coefficient is `1`, `-1` or `0`. -/
theorem main : ∃ flip : ℕ → ℕ → Bool, ∀ n : ℕ, signedCoeff flip n ∈ ({-1, 0, 1} : Set ℤ) := by
  sorry

end OMA.S_opg_dividing_up_the_unrestricted_partitions
