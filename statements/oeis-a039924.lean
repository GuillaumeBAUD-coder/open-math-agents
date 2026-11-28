import Mathlib

namespace OMA.S_oeis_a039924

open scoped Classical

/-- A partition of `n` into positive integer parts differing by at least `2`
(equivalently a finite set `S` of positive integers summing to `n` such that any two
distinct elements differ by at least `2`). -/
def IsDiff2Partition (n : ℕ) (S : Finset ℕ) : Prop :=
  (∀ x ∈ S, 1 ≤ x) ∧ S.sum id = n ∧ (∀ x ∈ S, ∀ y ∈ S, x < y → x + 2 ≤ y)

/-- Number of partitions of `n` with parts differing by at least `2` and an even number of parts
(`A286041(n)`). -/
noncomputable def a286041 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun S => IsDiff2Partition n S ∧ Even S.card)).card

/-- Number of partitions of `n` with parts differing by at least `2` and an odd number of parts
(`A286316(n)`). -/
noncomputable def a286316 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun S => IsDiff2Partition n S ∧ Odd S.card)).card

/-- OEIS A039924: `a(n)` is the coefficient of `x^n` in
`∑_{k ≥ 0} (-1)^k * x^(k^2) / ∏_{i=1}^k (1 - x^i)`.
Conjecture (George Beck): For all `n : ℕ`, `a(n) = A286041(n) - A286316(n)`. -/
theorem main :
    ∀ G : ℕ → PowerSeries ℤ,
      (∀ k : ℕ, (∏ i ∈ Finset.Icc 1 k, (1 - PowerSeries.X ^ i)) * G k = 1) →
      ∀ n : ℕ,
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℤ) ^ k * PowerSeries.coeff n (PowerSeries.X ^ (k ^ 2) * G k) =
        (a286041 n : ℤ) - (a286316 n : ℤ) := by
  sorry

end OMA.S_oeis_a039924
