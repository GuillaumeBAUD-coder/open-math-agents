import OMAReductions.R_Erdos384_erdos_384_R1

/-!
# The cases k = 2 and k = 3 (step H3 of Erdos384.erdos_384.R1)

For `k = 2`, `C(n, 2)` is a multiple of `⌊n/2⌋`, so its least prime factor works. For `k = 3`,
`6 * C(n, 3) = n (n - 1) (n - 2)`; `C(n, 3)` is even unless `n ≡ 3 (mod 4)`, and in that case
`3 * C(n, 3)` is a multiple of `u = (n - 1)/2`, so either `9 ∣ u` (then `3 ∣ C(n, 3)`) or `u` has a
prime factor other than `3`; the only failure is `n = 7`.
-/

open Nat

namespace OMA.EckH3

/-- A prime factor `p ≠ 3` of a divisor `u` of `3 * c` divides `c`. -/
theorem dvd_of_dvd_three_mul {p u c : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hpu : p ∣ u)
    (hu : u ∣ 3 * c) : p ∣ c := by
  have hcop : p.Coprime 3 := (Nat.coprime_primes hp Nat.prime_three).mpr hp3
  exact hcop.dvd_of_dvd_mul_left (hpu.trans hu)

theorem six_mul_choose_three (m : ℕ) : 6 * (m + 3).choose 3 = (m + 1) * (m + 2) * (m + 3) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (m + 3) 3
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial] at h
  have e1 : m + 3 - 2 = m + 1 := by omega
  have e2 : m + 3 - 1 = m + 2 := by omega
  rw [e1, e2, Nat.sub_zero] at h
  linarith

theorem ecklund_k_two_three : ∀ n k : ℕ, 2 ≤ k → k ≤ 3 → 2 * k ≤ n → (n, k) ≠ (7, 3) →
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  intro n k hk2 hk3 hkn h7
  rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl
  · -- k = 2: C(n, 2) is a multiple of ⌊n/2⌋
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have hm2 : 2 ≤ m := by omega
    have hdvd : m ∣ n.choose 2 := by
      rw [Nat.choose_two_right]
      rcases hm with rfl | rfl
      · refine ⟨2 * m - 1, ?_⟩
        rw [show 2 * m * (2 * m - 1) = 2 * (m * (2 * m - 1)) by ring]
        exact Nat.mul_div_cancel_left _ (by norm_num)
      · refine ⟨2 * m + 1, ?_⟩
        rw [show 2 * m + 1 - 1 = 2 * m by omega,
          show (2 * m + 1) * (2 * m) = 2 * (m * (2 * m + 1)) by ring]
        exact Nat.mul_div_cancel_left _ (by norm_num)
    refine ⟨m.minFac, Nat.minFac_prime (by omega), (Nat.minFac_dvd m).trans hdvd, ?_⟩
    have := Nat.minFac_le (show 0 < m by omega)
    omega
  · -- k = 3
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h6 := six_mul_choose_three m
    set C := (m + 3).choose 3 with hC
    obtain ⟨q, hq⟩ : ∃ q, m = 4 * q ∨ m = 4 * q + 1 ∨ m = 4 * q + 2 ∨ m = 4 * q + 3 :=
      ⟨m / 4, by omega⟩
    rcases hq with rfl | rfl | rfl | rfl
    · -- n = 4q + 3, the only odd case
      have hq2 : 2 ≤ q := by
        rcases (show q = 0 ∨ q = 1 ∨ 2 ≤ q by omega) with rfl | rfl | h
        · omega
        · exact absurd (by norm_num) h7
        · exact h
      set u := 2 * q + 1 with hu
      have h3C : 3 * C = u * ((4 * q + 1) * (4 * q + 3)) := by
        have : 6 * C = 2 * (u * ((4 * q + 1) * (4 * q + 3))) := by rw [h6, hu]; ring
        linarith
      have huC : u ∣ 3 * C := ⟨_, h3C⟩
      by_cases h3u : 3 ∣ u
      · obtain ⟨w, hw⟩ := h3u
        by_cases h3w : 3 ∣ w
        · obtain ⟨t, rfl⟩ := h3w
          refine ⟨3, Nat.prime_three, ⟨t * ((4 * q + 1) * (4 * q + 3)), ?_⟩, by omega⟩
          rw [hw] at h3C
          linarith
        · have hw1 : w ≠ 1 := by omega
          have hp := Nat.minFac_prime hw1
          have hp3 : w.minFac ≠ 3 := fun h => h3w (h ▸ Nat.minFac_dvd w)
          refine ⟨w.minFac, hp, dvd_of_dvd_three_mul hp hp3 ((Nat.minFac_dvd w).trans
            ⟨3, by rw [hw]; ring⟩) huC, ?_⟩
          have := Nat.minFac_le (show 0 < w by omega)
          omega
      · have hu1 : u ≠ 1 := by omega
        have hp := Nat.minFac_prime hu1
        have hp3 : u.minFac ≠ 3 := fun h => h3u (h ▸ Nat.minFac_dvd u)
        refine ⟨u.minFac, hp, dvd_of_dvd_three_mul hp hp3 (Nat.minFac_dvd u) huC, ?_⟩
        have := Nat.minFac_le (show 0 < u by omega)
        omega
    · -- n = 4q + 4
      refine ⟨2, Nat.prime_two, ?_, by omega⟩
      have : 6 * C = 8 * ((2 * q + 1) * (4 * q + 3) * (q + 1)) := by rw [h6]; ring
      generalize (2 * q + 1) * (4 * q + 3) * (q + 1) = Y at this
      exact Nat.dvd_of_mod_eq_zero (by omega)
    · -- n = 4q + 5
      refine ⟨2, Nat.prime_two, ?_, by omega⟩
      have : 6 * C = 4 * ((q + 1) * (4 * q + 3) * (4 * q + 5)) := by rw [h6]; ring
      generalize (q + 1) * (4 * q + 3) * (4 * q + 5) = Y at this
      exact Nat.dvd_of_mod_eq_zero (by omega)
    · -- n = 4q + 6
      refine ⟨2, Nat.prime_two, ?_, by omega⟩
      have : 6 * C = 8 * ((q + 1) * (4 * q + 5) * (2 * q + 3)) := by rw [h6]; ring
      generalize (q + 1) * (4 * q + 5) * (2 * q + 3) = Y at this
      exact Nat.dvd_of_mod_eq_zero (by omega)

end OMA.EckH3

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H3 := by
  exact OMA.EckH3.ecklund_k_two_three
