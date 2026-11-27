import OMAStatements.S_oeis_a242560
import Mathlib

-- Problem: A242560, least positive k such that (n! - k)/(n - k) is an integer; a(2n) = n.
-- Upstream: formal-conjectures statements/oeis-a242560.lean (declaration OMA.S_oeis_a242560.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: k = n works since n | (2n)!. For 0 < k < n the modulus d = 2n - k divides (2n)!, so
-- d | (2n)! - k would force d | k with 0 < k < d, which is impossible.

namespace OMA.P_oeis_a242560

open OMA.S_oeis_a242560

theorem main' : ∀ n : ℕ, 1 ≤ n → a (2 * n) = n := by
  intro n hn
  unfold a
  rw [Nat.find_eq_iff]
  constructor
  · refine ⟨by omega, by omega, ?_⟩
    rw [show ((2 * n : ℕ) : ℤ) - (n : ℤ) = (n : ℤ) by push_cast; ring]
    apply Int.emod_eq_zero_of_dvd
    have h1 : (n : ℤ) ∣ ((2 * n).factorial : ℤ) := by
      exact_mod_cast Nat.dvd_factorial (by omega) (by omega)
    exact dvd_sub h1 (dvd_refl _)
  · rintro k hk ⟨hk0, _, hmod⟩
    have hd : ((2 * n : ℕ) : ℤ) - (k : ℤ) = ((2 * n - k : ℕ) : ℤ) := by
      rw [Nat.cast_sub (show k ≤ 2 * n by omega)]
    rw [hd] at hmod
    have h1 : ((2 * n - k : ℕ) : ℤ) ∣ ((2 * n).factorial : ℤ) - k := Int.dvd_of_emod_eq_zero hmod
    have h2 : ((2 * n - k : ℕ) : ℤ) ∣ ((2 * n).factorial : ℤ) := by
      exact_mod_cast Nat.dvd_factorial (by omega) (by omega)
    have h3 : ((2 * n - k : ℕ) : ℤ) ∣ (k : ℤ) := by
      have := dvd_sub h2 h1
      simpa using this
    have h4 := Int.le_of_dvd (by exact_mod_cast hk0) h3
    have h5 : ((2 * n - k : ℕ) : ℤ) = 2 * (n : ℤ) - k := by
      rw [Nat.cast_sub (show k ≤ 2 * n by omega)]; push_cast; ring
    omega

end OMA.P_oeis_a242560

theorem OMA.solution : type_of% @OMA.S_oeis_a242560.main := OMA.P_oeis_a242560.main'
