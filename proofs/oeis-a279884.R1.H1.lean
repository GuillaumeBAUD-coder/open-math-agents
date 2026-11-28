import OMAReductions.R_oeis_a279884_R1
import Mathlib

-- Step oeis-a279884.R1.H1: hypothesis H1 of reduction oeis-a279884.R1
-- Credit: @Raimo33

theorem OMA.solution : OMA.R_oeis_a279884_R1.H1 := by
  intro n hn he hp
  unfold OMA.S_oeis_a279884.f at hp
  have hodd : Odd (n + 1) := he.add_one
  have hd : (n - 1) + 1 ∣ (n - 1) ^ (n + 1) + 1 ^ (n + 1) := hodd.nat_add_dvd_pow_add_pow _ _
  rw [one_pow, Nat.sub_add_cancel (by omega)] at hd
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · omega
  · have h3 : 3 ≤ n - 1 := by omega
    have : (n - 1) ^ 2 ≤ (n - 1) ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have ht : (n - 1) ^ (n + 1) = n - 1 := by omega
    rw [ht] at this
    generalize n - 1 = x at h3 this
    nlinarith
