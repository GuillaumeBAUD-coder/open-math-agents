import OMAStatements.S_oeis_a087037
import Mathlib

open OMA.S_oeis_a087037

private theorem not_prime_add_125 {x : ℕ} (hx : 0 < x) : ¬ (x ^ x + 125).Prime := by
  intro hp
  rcases Nat.even_or_odd x with ⟨k, hk⟩ | ho
  · by_cases h3 : 3 ∣ x
    · obtain ⟨m, hm⟩ := h3
      have e : x ^ x = (x ^ m) ^ 3 := by rw [← pow_mul, mul_comm, ← hm]
      rw [e] at hp
      have := hp.eq_one_or_self_of_dvd _ ((by decide : Odd 3).nat_add_dvd_pow_add_pow (x ^ m) 5)
      have := Nat.le_self_pow (by decide : 3 ≠ 0) (x ^ m)
      omega
    · have e : x ^ x = (x ^ 2) ^ k := by rw [← pow_mul]; congr 1; omega
      have h2 : x ^ 2 % 3 = 1 := by
        rw [Nat.pow_mod]
        rcases (by omega : x % 3 = 1 ∨ x % 3 = 2) with h | h <;> simp [h]
      have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero (by
        rw [Nat.add_mod, e, Nat.pow_mod, h2]; simp))
      omega
  · have := hp.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.1 (ho.pow.add_odd (by decide)))
    omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a087037.main) := by
  intro h
  obtain ⟨x, hx, hp⟩ := h 125 (by decide)
  exact not_prime_add_125 hx hp
