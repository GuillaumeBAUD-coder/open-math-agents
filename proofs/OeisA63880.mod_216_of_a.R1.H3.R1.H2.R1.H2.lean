import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H3_R1_H2_R1

-- Step OeisA63880.mod_216_of_a.R1.H3.R1.H2.R1.H2: the structural bridge.
-- Credit: @arindale

open OeisA63880
open scoped ArithmeticFunction.sigma

theorem OMA.solution :
    OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H2_R1.H2 := by
  intro m hm heq hfac
  have hm0 : m ≠ 0 := by
    obtain ⟨k, hk⟩ := hm
    omega
  have h3dvd : 3 ∣ m :=
    (Nat.prime_three.dvd_iff_one_le_factorization hm0).2 (by omega)
  have hnot9 : ¬ 3 ^ 2 ∣ m := by
    intro h
    have hle := (Nat.prime_three.pow_dvd_iff_le_factorization (k := 2) hm0).1 h
    omega
  obtain ⟨e, s, hs_notdvd, hmul⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by norm_num)
  have he1 : e = 1 := by
    have hepos : 1 ≤ e := by
      by_contra h
      have he0 : e = 0 := by omega
      have hms : m = s := by
        rw [he0] at hmul
        simpa using hmul
      exact hs_notdvd (hms ▸ h3dvd)
    have hele : e ≤ 1 := by
      by_contra h
      have h2e : 2 ≤ e := by omega
      have hdvd : 3 ^ 2 ∣ 3 ^ e := Nat.pow_dvd_pow 3 h2e
      have hdvdm : 3 ^ e ∣ m := by
        rw [hmul]
        exact dvd_mul_right (3 ^ e) s
      exact hnot9 (hdvd.trans hdvdm)
    omega
  have hm3 : m = 3 * s := by
    rw [he1] at hmul
    simpa using hmul
  have hs_eq : m / 3 = s := by
    rw [hm3]
    exact Nat.mul_div_cancel_left s (by norm_num)
  have hspos : 0 < s := by
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    rw [hm3] at hmpos
    exact Nat.pos_of_mul_pos_left hmpos
  have hodd : Odd s := by
    have h3s : Odd (3 * s) := by
      rw [← hm3]
      exact hm
    exact Nat.Odd.of_mul_right h3s
  have hfac0 : s.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hs_notdvd
  have hsig : σ 1 (3 * s) = σ 1 s * 4 := by
    rw [mul_comm 3 s, sigma_mul_prime Nat.prime_three hs_notdvd]
  have husig : usigma (3 * s) = usigma s * 4 := by
    rw [mul_comm 3 s, usigma_mul_prime hspos Nat.prime_three hs_notdvd]
  have heq' : 7 * σ 1 s = 10 * usigma s := by
    have h := heq
    rw [hm3, hsig, husig] at h
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hs_eq]
    exact hodd
  · rw [hs_eq]
    exact hfac0
  · rw [hs_eq]
    exact heq'
