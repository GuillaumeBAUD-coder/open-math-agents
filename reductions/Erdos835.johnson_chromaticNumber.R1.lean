import FormalConjectures.ErdosProblems.«835»

-- Reduction Erdos835.johnson_chromaticNumber.R1 of Erdős Problem 835 — johnson chromaticNumber
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 835: the composite case and the `p - 1` case

The question is whether the chromatic number of the Johnson graph `J(2k, k)` always beats
`k + 1`, i.e. `k + 2 ≤ χ(J(2k, k))` for every `k ≥ 3`.

For `k ≥ 3` the number `k + 1` is at least `4`, so it is either composite or prime, and the two
cases are two different pieces of mathematics:

* `H1` is the case where `k + 1` is composite.  This is Ma and Tang's theorem [MT25]: the
  chromatic number is greater than `k + 1`.  It covers every *odd* `k`, because then `k + 1` is
  even and at least `4` — this is exactly the implication proved in the module as
  `johnsonGraph_chromaticNumber_odd_of_johnson_chromaticNumber_composite`.
* `H2` is the case where `k + 1` is prime, i.e. `k = p - 1` with `p` prime.  This is the half
  nobody knows: it is verified only for `k ≤ 202` (that is `p ≤ 203`), and the problem asks
  about every prime `p`.

The reduction's content is the case split on `Nat.Prime (k + 1)`.

*References:*
- [erdosproblems.com/835](https://www.erdosproblems.com/835)
- [MT25] Ma and Tang, *On Problem 835*,
  https://github.com/QuanyuTang/erdos-problem-835/blob/main/On_Problem_835.pdf
-/

namespace OMA.R_Erdos835_johnson_chromaticNumber_R1

open Finset SimpleGraph
open scoped Nat SimpleGraph

/-- The composite case: if `k + 1` is composite then `χ(J(2k, k)) > k + 1` (Ma and Tang). -/
def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k → (k + 1).Composite → k + 2 ≤ χ(J(2 * k, k))

/-- The remaining case: if `k + 1` is prime, so `k = p - 1`, then `χ(J(2k, k)) > k + 1`. -/
def H2 : Prop :=
  ∀ k : ℕ, 3 ≤ k → (k + 1).Prime → k + 2 ≤ χ(J(2 * k, k))

theorem main : H1 → H2 → type_of% @Erdos835.johnson_chromaticNumber := by
  intro h1 h2 k hk
  by_cases hp : (k + 1).Prime
  · exact h2 k hk hp
  · exact h1 k hk ⟨by omega, hp⟩

end OMA.R_Erdos835_johnson_chromaticNumber_R1
