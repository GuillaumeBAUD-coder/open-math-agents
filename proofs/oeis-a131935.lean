import OMAStatements.S_oeis_a131935
import Mathlib
open OMA.S_oeis_a131935
theorem OMA.a131rec (k : ℕ) : a (k + 5) + a (k + 2) + a (k + 1) = a (k + 4) + 3 * a (k + 3) := by
  simp only [a, state]
  rcases state k with ⟨_ | _, ⟨p, q, r, s⟩⟩ <;>
    simp [advance, oddToEven, evenToOdd, Endpoints.total] <;> ring
theorem OMA.solution : type_of% @OMA.S_oeis_a131935.main := by
  have hr : ∀ n : Nat, 1 ≤ n → a (n + 4) + a (n + 1) + a n = a (n + 3) + 3 * a (n + 2) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact OMA.a131rec k
  refine ⟨hr, ?_⟩
  intro n
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | 3 => decide +kernel
  | 4 => decide +kernel
  | m + 5 =>
    have h := hr (m + 1) (by omega)
    simp only [productCoeff, numeratorCoeff]
    have h' : ((a (m + 1 + 4) : ℤ) + a (m + 1 + 1) + a (m + 1)) = a (m + 1 + 3) + 3 * a (m + 1 + 2) := by
      exact_mod_cast h
    simp only [show m + 1 + 4 = m + 5 by omega, show m + 1 + 3 = m + 4 by omega,
      show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at h'
    linear_combination h'
