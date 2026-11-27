import OMAReductions.R_CarmichaelTotient_charmichaelTotient_R1

-- A positive integer not divisible by 36 shares its totient with another integer.
-- Original Lean proof of the first step of Carmichael's 1922 argument: for odd n take 2n; for n = 2k with k odd
-- take k; if 4 divides n and 3 does not take 3n/2; if 4 and 3 divide n and 9 does not take 2n/3.
-- A classical partial result, not progress on the conjecture.

namespace OMA.Carmichael1

lemma t_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) : (p * n).totient = p * n.totient :=
  Nat.totient_mul_of_prime_of_dvd hp h

lemma t_ndvd {p n q : ℕ} (hp : p.Prime) (hq : q + 1 = p) (h : ¬ p ∣ n) :
    (p * n).totient = q * n.totient := by
  rw [Nat.totient_mul_of_prime_of_not_dvd hp h]
  subst hq
  simp

theorem not_36 (n : ℕ) (hn : 0 < n) (h36 : ¬ 36 ∣ n) :
    CarmichaelTotient.CarmichaelTotientFor n := by
  unfold CarmichaelTotient.CarmichaelTotientFor
  by_cases h2 : 2 ∣ n
  · obtain ⟨k, rfl⟩ := h2
    by_cases hk2 : 2 ∣ k
    · by_cases h3 : 3 ∣ k
      · obtain ⟨j, rfl⟩ := h3
        have hj2 : 2 ∣ j := by omega
        have hj3 : ¬ 3 ∣ j := by
          intro h
          apply h36
          omega
        refine ⟨2 * (2 * j), by omega, ?_⟩
        rw [t_dvd Nat.prime_two (show 2 ∣ 2 * j by omega), t_dvd Nat.prime_two hj2,
          t_dvd Nat.prime_two (show 2 ∣ 3 * j by omega), t_ndvd Nat.prime_three (q := 2) rfl hj3]
      · refine ⟨3 * k, by omega, ?_⟩
        rw [t_ndvd Nat.prime_three (q := 2) rfl h3, t_dvd Nat.prime_two hk2]
    · refine ⟨k, by omega, ?_⟩
      rw [t_ndvd Nat.prime_two (q := 1) rfl hk2, one_mul]
  · refine ⟨2 * n, by omega, ?_⟩
    rw [t_ndvd Nat.prime_two (q := 1) rfl h2, one_mul]

end OMA.Carmichael1

theorem OMA.solution : OMA.R_CarmichaelTotient_charmichaelTotient_R1.H1 := by
  intro n hn h36
  exact OMA.Carmichael1.not_36 n hn h36
