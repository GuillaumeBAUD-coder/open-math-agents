import OMAStatements.S_oeis_a235089
import Mathlib

open PowerSeries OMA.S_oeis_a235089 in
theorem OMA.solution : type_of% @OMA.S_oeis_a235089.main := by
  have hc : ∀ n, a n = 5*n - 2*(n%2) ∧ a (n+1) = 5*(n+1) - 2*((n+1)%2) := by
    intro n
    induction n with
    | zero => simp [a]
    | succ n ih => exact ⟨ih.2, by rw [a, ih.2]; split_ifs <;> omega⟩
  replace hc := fun n => (hc n).1
  have r (n : ℕ) : ((a (n+3) : ℕ) : ℚ) = a (n+2) + a (n+1) - a n := by
    have : (a (n+3) : ℤ) = a (n+2) + a (n+1) - a n := by rw [hc, hc, hc, hc]; omega
    exact_mod_cast this
  refine ⟨⟨fun n _ => by rw [hc, hc]; omega,
      fun k => ⟨?_, fun ⟨_, _⟩ => ⟨(k+2)/5, by omega, by rw [hc]; omega⟩⟩⟩,
    fun n _ => ?_, fun n _ => by rw [hc, hc, hc, hc]; omega, ?_, fun n _ => by rw [hc]; omega⟩
  · rintro ⟨n, _, rfl⟩
    rw [hc]
    obtain ⟨j, rfl | rfl⟩ := n.even_or_odd' <;> omega
  · have := hc n
    obtain ⟨j, rfl | rfl⟩ := n.even_or_odd' <;> simp [pow_succ, pow_mul] <;> omega
  · rw [show (fun n => if n = 0 then (0:ℚ) else (a n : ℚ)) = fun n => (a n : ℚ) from
        funext fun n => by cases n <;> simp [a],
      show (((X:ℚ⟦X⟧) - 1)^2 * (X + 1)) = C 1 * X^0 + C (-1) * X^1 + C (-1) * X^2 + C 1 * X^3 by
        simp only [map_neg, map_one]; ring,
      show ((X:ℚ⟦X⟧) * (7 * X + 3)) = C 3 * X^1 + C 7 * X^2 by simp only [map_ofNat]; ring]
    ext n
    simp only [mul_add, map_add, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C, coeff_mk]
    rcases n with _|_|_|n
    iterate 3 norm_num [a]
    simp [r] <;> ring
