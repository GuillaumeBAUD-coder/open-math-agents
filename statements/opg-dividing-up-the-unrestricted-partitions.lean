import Mathlib

/-!
# Dividing up the unrestricted partitions

Source: https://www.openproblemgarden.org/op/dividing_up_the_unrestricted_partitions
Credit: @BhaveshKSinha

Each nonconstant term in each factor can receive its own sign. To compute the
coefficient of degree `n`, only the factors for part sizes 1 through `n` matter.
-/

namespace OMA.S_opg_dividing_up_the_unrestricted_partitions

open scoped BigOperators

/-- Factor for part size `m + 1`, with independent signs on its positive multiples. -/
def signedFactor (sign : ℕ → ℕ → Bool) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun k =>
    if k = 0 then 1
    else if (m + 1) ∣ k then
      if sign m (k / (m + 1)) then 1 else -1
    else 0

theorem main :
    ∃ sign : ℕ → ℕ → Bool, ∀ n : ℕ,
      let a := PowerSeries.coeff n (∏ m ∈ Finset.range n, signedFactor sign m)
      a = -1 ∨ a = 0 ∨ a = 1 := by
  sorry

end OMA.S_opg_dividing_up_the_unrestricted_partitions
