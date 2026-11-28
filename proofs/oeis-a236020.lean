import OMAStatements.S_oeis_a236020
import Mathlib

/-!
# A236020: `log σ(n) / log τ(n)` does not determine `n`

`14` and `15` have the same divisor sum (`1 + 2 + 7 + 14 = 1 + 3 + 5 + 15 = 24`) and the same
number of divisors (`4`), hence the same value of `log σ / log τ`.
-/

namespace OMA.S_oeis_a236020

lemma sigma_14 : ∑ d ∈ (14 : ℕ).divisors, d = 24 := by decide +kernel
lemma sigma_15 : ∑ d ∈ (15 : ℕ).divisors, d = 24 := by decide +kernel
lemma tau_14 : (14 : ℕ).divisors.card = 4 := by decide +kernel
lemma tau_15 : (15 : ℕ).divisors.card = 4 := by decide +kernel

end OMA.S_oeis_a236020

open OMA.S_oeis_a236020 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a236020.main) := by
  intro h
  have hk : kVal 14 = kVal 15 := by
    unfold kVal
    rw [sigma_14, sigma_15, tau_14, tau_15]
  have := h 14 15 (by norm_num) (by norm_num) hk
  omega
