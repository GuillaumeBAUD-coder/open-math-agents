import OMAReductions.R_CarmichaelTotient_charmichaelTotient_R1

-- Step CarmichaelTotient.charmichaelTotient.R1.H3: hypothesis H3 of reduction
-- CarmichaelTotient.charmichaelTotient.R1
-- Credit: @JamesSlash. Carmichael's exchange of prime factors with equal totient (Bull. AMS 1922),
-- as listed in the reduction: phi (p * k) = p * phi k when p | k and (q - 1) * phi k when q does not divide k.

namespace OMACarmichael

open Nat

theorem tot_dvd {p k : ℕ} (hp : p.Prime) (h : p ∣ k) : φ (p * k) = p * φ k :=
  Nat.totient_mul_of_prime_of_dvd hp h

theorem tot_ndvd {q k : ℕ} (hq : q.Prime) (h : ¬ q ∣ k) : φ (q * k) = (q - 1) * φ k := by
  rw [Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hq).mpr h), Nat.totient_prime hq]

end OMACarmichael

open Nat OMACarmichael in
theorem OMA.solution : OMA.R_CarmichaelTotient_charmichaelTotient_R1.H3 := by
  intro n h36 h49 h1849
  have h1764 : 1764 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 36 49) h36 h49
  have p43 : (43 : ℕ).Prime := by norm_num
  have p7 : (7 : ℕ).Prime := by norm_num
  by_cases h43 : 43 ∣ n
  · obtain ⟨j, rfl⟩ := h43
    have hj43 : ¬ 43 ∣ j := by
      rintro ⟨i, rfl⟩
      exact h1849 ⟨i, by ring⟩
    have hj : 1764 ∣ j := Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 1764 43) h1764
    have hj2 : 2 ∣ 3 * (7 * j) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_right ((by norm_num : 2 ∣ 1764).trans hj) 7) 3
    have hj3 : 3 ∣ 7 * j := dvd_mul_of_dvd_right ((by norm_num : 3 ∣ 1764).trans hj) 7
    have hj7 : 7 ∣ j := (by norm_num : 7 ∣ 1764).trans hj
    refine ⟨2 * (3 * (7 * j)), by omega, ?_⟩
    rw [tot_dvd Nat.prime_two hj2, tot_dvd Nat.prime_three hj3, tot_dvd p7 hj7, tot_ndvd p43 hj43]
    ring
  · obtain ⟨k, hk⟩ : 42 ∣ n := (by norm_num : 42 ∣ 1764).trans h1764
    subst hk
    have hk42 : 42 ∣ k := by omega
    have hk2 : 2 ∣ 3 * (7 * k) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_right ((by norm_num : 2 ∣ 42).trans hk42) 7) 3
    have hk3 : 3 ∣ 7 * k := dvd_mul_of_dvd_right ((by norm_num : 3 ∣ 42).trans hk42) 7
    have hk7 : 7 ∣ k := (by norm_num : 7 ∣ 42).trans hk42
    have hk43 : ¬ 43 ∣ k := fun h => h43 (dvd_mul_of_dvd_right h 42)
    refine ⟨43 * k, by omega, ?_⟩
    rw [show 42 * k = 2 * (3 * (7 * k)) by ring, tot_dvd Nat.prime_two hk2, tot_dvd Nat.prime_three hk3,
      tot_dvd p7 hk7, tot_ndvd p43 hk43]
    ring
