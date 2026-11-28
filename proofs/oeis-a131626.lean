import OMAStatements.S_oeis_a131626
import Mathlib

namespace OMA.Helpers

theorem countPrimeA131626_23 : Nat.count Nat.Prime 23 = 8 := by decide

theorem countPrimeA131626_29 : Nat.count Nat.Prime 29 = 9 := by decide

theorem nthPrimeA131626_8 : Nat.nth Nat.Prime 8 = 23 := by
  rw [← countPrimeA131626_23]; exact Nat.nth_count (by norm_num)

theorem nthPrimeA131626_9 : Nat.nth Nat.Prime 9 = 29 := by
  rw [← countPrimeA131626_29]; exact Nat.nth_count (by norm_num)

/-- A multiple of 3 that exceeds 3 is not prime. -/
theorem notPrimeA131626 {N : ℕ} (h3 : 3 ∣ N) (hN : 3 < N) : ¬ Nat.Prime N := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd 3 h3 with h | h <;> omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a131626.main := by
  intro x hx
  have h := Nat.mod_lt x (show 0 < 3 by norm_num)
  interval_cases hr : x % 3
  · refine ⟨0, ?_⟩
    rw [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
    exact OMA.Helpers.notPrimeA131626 (by omega) (by omega)
  · refine ⟨8, ?_⟩
    rw [OMA.Helpers.nthPrimeA131626_8, OMA.Helpers.nthPrimeA131626_9]
    exact OMA.Helpers.notPrimeA131626 (by omega) (by omega)
  · refine ⟨2, ?_⟩
    rw [Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]
    exact OMA.Helpers.notPrimeA131626 (by omega) (by omega)
