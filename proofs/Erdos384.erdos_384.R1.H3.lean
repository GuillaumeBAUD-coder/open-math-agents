import OMAReductions.R_Erdos384_erdos_384_R1
import Mathlib

-- Step Erdos384.erdos_384.R1.H3: hypothesis H3 of reduction Erdos384.erdos_384.R1
-- Credit: @luciusacarr

/-! `k = 2`: a prime factor of `n/2` or `(n-1)/2` divides `C(n,2)`. `k = 3`, `n ≥ 9`: an even `e ∈ {n, n-1}` has
only prime factors `≤ n/2`; if `C(n,3)` had none, it would be coprime to `e` and divide the product of the
other two factors, so `C(n,3) ≤ n(n-1)`, contradicting `6 C(n,3) = n(n-1)(n-2)`. `n = 6, 8` directly. -/

namespace OMA384h3

lemma choose_two_mul (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  have := Nat.descFactorial_eq_factorial_mul_choose n 2
  simp [Nat.descFactorial] at this
  rw [← this]; ring

lemma choose_three_mul (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  have := Nat.descFactorial_eq_factorial_mul_choose n 3
  simp [Nat.descFactorial, Nat.factorial] at this
  rw [← this]; ring

lemma case_two (n : ℕ) (hn : 4 ≤ n) : ∃ p : ℕ, p.Prime ∧ p ∣ n.choose 2 ∧ 2 * p ≤ n := by
  have h2 := choose_two_mul n
  obtain ⟨m, hm⟩ : ∃ m, 2 ≤ m ∧ m ∣ n.choose 2 ∧ 2 * m ≤ n := by
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · refine ⟨m, by omega, ⟨m + m - 1, ?_⟩, by omega⟩
      have : 2 * (m + m).choose 2 = 2 * (m * (m + m - 1)) := by rw [h2]; ring
      omega
    · refine ⟨m, by omega, ⟨2 * m + 1, ?_⟩, by omega⟩
      have : 2 * (2 * m + 1).choose 2 = 2 * (m * (2 * m + 1)) := by
        rw [h2]; simp; ring
      omega
  obtain ⟨hm2, hmd, hmn⟩ := hm
  refine ⟨m.minFac, Nat.minFac_prime (by omega), (Nat.minFac_dvd m).trans hmd, ?_⟩
  have := Nat.minFac_le (show 0 < m by omega)
  omega

lemma case_three (n : ℕ) (hn : 6 ≤ n) (h7 : n ≠ 7) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose 3 ∧ 2 * p ≤ n := by
  have h6 := choose_three_mul n
  rcases (show n = 6 ∨ n = 8 ∨ 9 ≤ n by omega) with rfl | rfl | hn9
  · exact ⟨2, Nat.prime_two, by decide, by norm_num⟩
  · exact ⟨2, Nat.prime_two, by decide, by norm_num⟩
  by_contra hne
  -- every prime factor `p` of `C(n, 3)` has `n < 2 * p`
  have big : ∀ p, p.Prime → p ∣ n.choose 3 → n < 2 * p := fun p hp hd => by
    by_contra h; exact hne ⟨p, hp, hd, by omega⟩
  -- an even number `e ∈ {n, n - 1}`, `4 ≤ e ≤ n`, is coprime to `C(n, 3)`
  obtain ⟨e, r, he4, hen, heven, hprod, hr⟩ : ∃ e r : ℕ, 4 ≤ e ∧ e ≤ n ∧ 2 ∣ e ∧
      n * (n - 1) * (n - 2) = e * r ∧ r ≤ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine ⟨n, (n - 1) * (n - 2), by omega, le_rfl, ⟨m, by omega⟩, by ring, ?_⟩
      calc (n - 1) * (n - 2) ≤ (n - 1) * n := Nat.mul_le_mul_left _ (by omega)
        _ = n * (n - 1) := mul_comm _ _
    · refine ⟨n - 1, n * (n - 2), by omega, by omega, ⟨m, by omega⟩, by ring, ?_⟩
      exact Nat.mul_le_mul_left _ (by omega)
  have hcop : Nat.Coprime (n.choose 3) e := by
    apply Nat.coprime_of_dvd
    intro k hk hkC hke
    have hk2 : 2 * k ≤ e := by
      obtain ⟨t, rfl⟩ := hke
      rcases (show t = 0 ∨ t = 1 ∨ 2 ≤ t by omega) with rfl | rfl | ht
      · omega
      · -- `e = k` is an even prime, so `e = 2 < 4`
        have := (Nat.Prime.eq_one_or_self_of_dvd hk 2 (by simpa using heven))
        omega
      · nlinarith
    have := big k hk hkC
    omega
  have hdvd : n.choose 3 ∣ e * r := by
    rw [← hprod]; exact ⟨6, by rw [← h6]; ring⟩
  have hCr : n.choose 3 ∣ r := hcop.dvd_of_dvd_mul_left hdvd
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h, mul_zero] at hprod
      have : 0 < n * (n - 1) * (n - 2) :=
        Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
      omega
    · exact h
  have hle : n.choose 3 ≤ n * (n - 1) := (Nat.le_of_dvd hrpos hCr).trans hr
  have h1 : 7 * (n * (n - 1)) ≤ n * (n - 1) * (n - 2) :=
    by rw [mul_comm 7]; exact Nat.mul_le_mul_left _ (by omega)
  have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  omega

theorem main_H3 : OMA.R_Erdos384_erdos_384_R1.H3 := by
  unfold OMA.R_Erdos384_erdos_384_R1.H3
  intro n k hk2 hk3 hkn hne
  rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl
  · exact case_two n (by omega)
  · exact case_three n (by omega) (by rintro rfl; exact hne rfl)

end OMA384h3

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H3 := OMA384h3.main_H3
