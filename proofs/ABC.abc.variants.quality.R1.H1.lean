import OMAReductions.R_ABC_abc_variants_quality_R1
import Mathlib

/-!
The radical of `a * b * c` is divisible by the radical of each factor. A squarefree `c` is its
own radical. If `a * b` is squarefree, then `a * b` and the radical of `c` are coprime divisors
of the radical, and `c = a + b ≤ 2 * a * b ≤ a * b * rad c`.
-/

namespace O2ABCQuality

theorem rad_pos (n : ℕ) : 0 < ABC.radical n := by
  unfold ABC.radical
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

theorem rad_dvd_rad {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) : ABC.radical m ∣ ABC.radical n := by
  unfold ABC.radical
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono h hn)

theorem rad_dvd_self (n : ℕ) : ABC.radical n ∣ n := by
  unfold ABC.radical
  simpa using Nat.prod_primeFactors_dvd n

theorem rad_of_squarefree {n : ℕ} (h : Squarefree n) : ABC.radical n = n := by
  unfold ABC.radical
  simpa using Nat.prod_primeFactors_of_squarefree h

theorem two_le_rad {n : ℕ} (hn : 2 ≤ n) : 2 ≤ ABC.radical n := by
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hmem : n.minFac ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd n, by omega⟩
  have hd : n.minFac ∣ ABC.radical n := by
    unfold ABC.radical
    exact Finset.dvd_prod_of_mem id hmem
  exact le_trans hp.two_le (Nat.le_of_dvd (rad_pos n) hd)

end O2ABCQuality

open O2ABCQuality in
theorem OMA.solution : OMA.R_ABC_abc_variants_quality_R1.H1 := by
  intro a b c ha hb hcop habc
  have hc2 : 2 ≤ c := by omega
  have hc0 : c ≠ 0 := by omega
  have hN : a * b * c ≠ 0 := by positivity
  have hcabc : c ∣ a * b * c := dvd_mul_left c (a * b)
  have radc2 := two_le_rad hc2
  have radc_le : ABC.radical c ≤ ABC.radical (a * b * c) :=
    Nat.le_of_dvd (rad_pos _) (rad_dvd_rad hN hcabc)
  refine ⟨by omega, ?_⟩
  rintro (hsq | hsq)
  · rw [rad_of_squarefree hsq] at radc_le
    exact radc_le
  · have hac : Nat.Coprime a c := hcop (by simp) (by simp) (by omega)
    have hbc : Nat.Coprime b c := hcop (by simp) (by simp) (by omega)
    have habc' : Nat.Coprime (a * b) (ABC.radical c) :=
      (Nat.Coprime.mul_left hac hbc).coprime_dvd_right (rad_dvd_self c)
    have hab : a * b ∣ ABC.radical (a * b * c) := by
      have := rad_dvd_rad hN (dvd_mul_right (a * b) c)
      rwa [rad_of_squarefree hsq] at this
    have hdiv : a * b * ABC.radical c ∣ ABC.radical (a * b * c) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd habc' hab (rad_dvd_rad hN hcabc)
    have hle := Nat.le_of_dvd (rad_pos _) hdiv
    have h1 : a + b ≤ a * b * 2 := by nlinarith
    have h2 : a * b * 2 ≤ a * b * ABC.radical c := Nat.mul_le_mul_left _ radc2
    omega
