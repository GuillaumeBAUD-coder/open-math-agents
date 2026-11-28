import OMAStatements.S_oeis_a383700
import Mathlib

/-!
# A383700 from an arithmetic-progression polynomial identity

The OEIS entry credits R. J. Mathar with the recurrence and Robert Israel
with a generating-function proof. Here the recurrence follows from a
polynomial identity valid for any first constant and common difference.
The difference polynomial is divisible by X cubed, so taking any of its
coefficients below degree three gives zero.

Source: https://oeis.org/A383700
-/

namespace OMA.A383700

open Polynomial

/-- The product of linear factors with arithmetic-progression constant terms. -/
noncomputable def progressionProduct (first step : ℤ) (n : ℕ) : ℤ[X] :=
  ∏ j ∈ Finset.range n, (X + C (step * (j : ℤ) + first))

private theorem progressionProduct_succ (first step : ℤ) (n : ℕ) :
    progressionProduct first step (n + 1) =
      progressionProduct first step n * (X + C (step * (n : ℤ) + first)) := by
  exact Finset.prod_range_succ ..

/-- Combining four consecutive products leaves exactly the old product times X cubed. -/
theorem progressionProduct_identity (first step : ℤ) (n : ℕ) :
    let c := step * (n : ℤ) + first
    progressionProduct first step (n + 3) -
      C (3 * (c + step)) * progressionProduct first step (n + 2) +
      C (3 * c ^ 2 + 3 * c * step + step ^ 2) * progressionProduct first step (n + 1) -
      C (c ^ 3) * progressionProduct first step n =
        progressionProduct first step n * X ^ 3 := by
  dsimp only
  rw [progressionProduct_succ first step (n + 2),
    progressionProduct_succ first step (n + 1), progressionProduct_succ first step n]
  push_cast
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one]
  ring

end OMA.A383700

open Polynomial OMA.S_oeis_a383700 in
theorem OMA.solution : type_of% @OMA.S_oeis_a383700.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  push_cast
  have h := congrArg (fun p : ℤ[X] => p.coeff 2) (OMA.A383700.progressionProduct_identity 1 4 m)
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_mul_X_pow'] at h
  norm_num at h
  unfold OMA.A383700.progressionProduct at h
  unfold OMA.S_oeis_a383700.a
  linear_combination h
