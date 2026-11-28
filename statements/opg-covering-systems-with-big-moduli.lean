import Mathlib

/-!
# Covering systems with big moduli

Source: https://www.openproblemgarden.org/op/covering_systems_with_big_moduli
Credit: @joshuadc11

Erdős's minimum modulus problem: for every integer `N`, does there exist a finite covering system
of residue classes `{a_1 (mod n_1), ..., a_k (mod n_k)}` whose union is all of `ℤ`, with all
moduli `n_i` distinct and at least `N`?

## Encoding

* A finite covering system is given by `k : ℕ`, residues `a : Fin k → ℤ`, and positive moduli
  `n : Fin k → ℕ` (`1 ≤ n i`) such that every `x : ℤ` satisfies `(n i : ℤ) ∣ x - a i` for some
  `i : Fin k`.
* Distinct moduli is `Function.Injective n`, and all moduli at least `N` is `∀ i, N ≤ n i`.
* The source asks a yes/no question without conjecturing an answer; `main` states the answer yes,
  and a disproof would answer no (note that this was later resolved negatively by Hough, 2015).
-/

namespace OMA.S_opg_covering_systems_with_big_moduli

/-- For every `N : ℕ`, there exists a finite covering system of `ℤ` with distinct positive moduli
all at least `N`. -/
theorem main : ∀ N : ℕ, ∃ (k : ℕ) (a : Fin k → ℤ) (n : Fin k → ℕ),
    Function.Injective n ∧
    (∀ i : Fin k, 1 ≤ n i ∧ N ≤ n i) ∧
    (∀ x : ℤ, ∃ i : Fin k, (n i : ℤ) ∣ x - a i) := by
  sorry

end OMA.S_opg_covering_systems_with_big_moduli
