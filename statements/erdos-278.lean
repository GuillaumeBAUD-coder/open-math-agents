import Mathlib

/-!
# Erdős Problem 278

Source: https://www.erdosproblems.com/278
Credit: @sntntHb

Let `A = {n_1 < ⋯ < n_r}` be a finite set of positive integers. What is the maximum density of
integers covered by a suitable choice of congruences `a_i (mod n_i)`? Is the minimum density
achieved when all the `a_i` are equal?

We state the affirmative answer to the second (yes/no) question: for every finite set `A` of
positive integers, every choice of residues `a_i` covers a set of integers of density at least
the density covered when all the `a_i` are equal to a common value `c`.

Conventions:
- The residues are given as a function `a : ℕ → ℤ`, the congruence attached to the modulus
  `n ∈ A` being `x ≡ a n (mod n)`; only the values on `A` matter.
- The set of integers covered by the congruences is periodic modulo `L = lcm A`, so its
  (natural) density exists and equals the number of covered residues in `[0, L)` divided
  by `L`. This is the density used below (for `A = ∅` it is `0`).
-/

namespace OMA.S_erdos_278

/-- The density of the set of integers `x` with `x ≡ a n (mod n)` for some `n ∈ A`, computed over
one period `[0, lcm A)`. -/
noncomputable def coveredDensity (A : Finset ℕ) (a : ℕ → ℤ) : ℚ := by
  classical
  exact (((Finset.range (A.lcm id)).filter
    (fun x : ℕ => ∃ n ∈ A, (x : ℤ) ≡ a n [ZMOD (n : ℤ)])).card : ℚ) / ((A.lcm id : ℕ) : ℚ)

/-- The minimum covered density is attained when all the residues are equal. -/
theorem main : ∀ A : Finset ℕ, (∀ n ∈ A, 0 < n) → ∀ (a : ℕ → ℤ) (c : ℤ),
    coveredDensity A (fun _ => c) ≤ coveredDensity A a := by
  sorry

end OMA.S_erdos_278
