import OMAReductions.R_Erdos384_erdos_384_R1
import Mathlib

-- Step Erdos384.erdos_384.R1.H3: hypothesis H3 of reduction Erdos384.erdos_384.R1
-- Credit: @NickLeko

/-!
The cases `k = 2` and `k = 3` of Ecklund's theorem.

* `k = 2`: any prime factor of `⌊n/2⌋ ≥ 2` divides `C(n, 2) = n (n - 1) / 2`.
* `k = 3`: write `x = n (n - 1) (n - 2) = 6 C(n, 3)`. If `4 ∣ x` then `2 ∣ C(n, 3)`; if `9 ∣ x`
  then `3 ∣ C(n, 3)`. Otherwise `n ≡ 3 (mod 4)` and `n - 1 = 2m` with `m` odd and `9 ∤ n - 1`, so
  `m` or `m / 3` is an odd number `q > 1` prime to `3` (`q = 1` only for `n = 7`). A prime factor
  `p` of `q` is prime to `6`, so it divides `C(n, 3)`, and `2p ≤ 2q ≤ n - 1`.
-/

namespace OMA384H3

lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 2
  simp [Nat.descFactorial_succ] at h
  rw [← h]
  ring

lemma six_mul_choose_three (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 3
  simp [Nat.descFactorial_succ, Nat.factorial] at h
  rw [← h]
  ring

lemma prime_dvd_of_coprime_six {p c x : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
    (hx : 6 * c = x) (hpx : p ∣ x) : p ∣ c := by
  have hcop : Nat.Coprime p 6 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h6
    have : p ∣ 2 * 3 := h6
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  rw [← hx] at hpx
  exact hcop.dvd_of_dvd_mul_left hpx

lemma case_two (n : ℕ) (hn : 4 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose 2 ∧ 2 * p ≤ n := by
  have h2 := two_mul_choose_two n
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · -- n = 2m, C(n,2) = m (n - 1)
    have hC : n.choose 2 = m * (n - 1) := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
      rw [h2, hm]; ring
    have hm1 : m ≠ 1 := by omega
    refine ⟨m.minFac, Nat.minFac_prime hm1, ?_, ?_⟩
    · rw [hC]; exact Dvd.dvd.mul_right (Nat.minFac_dvd m) _
    · have := Nat.minFac_le (show 0 < m by omega); omega
  · -- n = 2m + 1, C(n,2) = n m
    have hC : n.choose 2 = n * m := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
      rw [h2, hm]; simp; ring
    have hm1 : m ≠ 1 := by omega
    refine ⟨m.minFac, Nat.minFac_prime hm1, ?_, ?_⟩
    · rw [hC]; exact Dvd.dvd.mul_left (Nat.minFac_dvd m) _
    · have := Nat.minFac_le (show 0 < m by omega); omega

lemma case_three (n : ℕ) (hn : 6 ≤ n) (h7 : n ≠ 7) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose 3 ∧ 2 * p ≤ n := by
  have h6 := six_mul_choose_three n
  set x := n * (n - 1) * (n - 2) with hx
  set c := n.choose 3 with hc
  -- If `4 ∣ x`, then `2 ∣ c`.
  by_cases h4 : n % 4 = 3
  swap
  · have hx4 : 4 ∣ x := by
      have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 := by omega
      rcases this with h | h | h
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _) _
      · exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _
    refine ⟨2, Nat.prime_two, ?_, by omega⟩
    omega
  -- If `9 ∣ x`, then `3 ∣ c`.
  by_cases h9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2
  · have hx9 : 9 ∣ x := by
      rcases h9 with h | h | h
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _) _
      · exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _
    refine ⟨3, Nat.prime_three, ?_, by omega⟩
    omega
  -- Otherwise find an odd `q > 1`, prime to `3`, with `q ∣ n - 1` and `2q ≤ n`.
  obtain ⟨q, hqdvd, hq2, hq3, hq1, hqle⟩ :
      ∃ q : ℕ, q ∣ n - 1 ∧ q % 2 = 1 ∧ q % 3 ≠ 0 ∧ q ≠ 1 ∧ 2 * q ≤ n := by
    by_cases hm3 : ((n - 1) / 2) % 3 = 0
    · refine ⟨(n - 1) / 6, ⟨6, by omega⟩, by omega, by omega, by omega, by omega⟩
    · refine ⟨(n - 1) / 2, ⟨2, by omega⟩, by omega, hm3, by omega, by omega⟩
  have hp := Nat.minFac_prime hq1
  have hpq : q.minFac ∣ q := Nat.minFac_dvd q
  have hp2 : q.minFac ≠ 2 := by
    intro h; rw [h] at hpq; omega
  have hp3 : q.minFac ≠ 3 := by
    intro h; rw [h] at hpq; omega
  have hpx : q.minFac ∣ x :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_left (hpq.trans hqdvd) _) _
  refine ⟨q.minFac, hp, prime_dvd_of_coprime_six hp hp2 hp3 h6 hpx, ?_⟩
  have := Nat.minFac_le (show 0 < q by omega)
  omega

theorem main_H3 : OMA.R_Erdos384_erdos_384_R1.H3 := by
  intro n k hk2 hk3 hkn h7
  have : k = 2 ∨ k = 3 := by omega
  rcases this with rfl | rfl
  · exact case_two n (by omega)
  · exact case_three n (by omega) (by intro h; exact h7 (by rw [h]))

end OMA384H3

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H3 := OMA384H3.main_H3
