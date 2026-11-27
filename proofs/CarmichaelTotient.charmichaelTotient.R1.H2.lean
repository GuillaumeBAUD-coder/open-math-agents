import OMAReductions.R_CarmichaelTotient_charmichaelTotient_R1

-- A multiple of 36 that is not divisible by 49 shares its totient with another integer.
-- Original Lean proof of the second step of Carmichael's 1922 argument: if 7 does not divide n take 7n/6
-- (phi(7) = 6 = phi-multiplier of the extra factors 2 and 3), and if 7 divides n exactly once take 6n/7.
-- A classical partial result, not progress on the conjecture.

namespace OMA.Carmichael2

lemma t_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) : (p * n).totient = p * n.totient :=
  Nat.totient_mul_of_prime_of_dvd hp h

lemma t_ndvd {p n q : ℕ} (hp : p.Prime) (hq : q + 1 = p) (h : ¬ p ∣ n) :
    (p * n).totient = q * n.totient := by
  rw [Nat.totient_mul_of_prime_of_not_dvd hp h]
  subst hq
  simp

theorem not_49 (n : ℕ) (h36 : 36 ∣ n) (h49 : ¬ 49 ∣ n) :
    CarmichaelTotient.CarmichaelTotientFor n := by
  unfold CarmichaelTotient.CarmichaelTotientFor
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact absurd (dvd_zero 49) h49
    · exact h
  have p7 : Nat.Prime 7 := by norm_num
  by_cases h7 : 7 ∣ n
  · obtain ⟨k, rfl⟩ := h7
    have hk7 : ¬ 7 ∣ k := by
      intro h
      apply h49
      omega
    have hk36 : 36 ∣ k := by omega
    refine ⟨2 * (3 * k), by omega, ?_⟩
    rw [t_dvd Nat.prime_two (show 2 ∣ 3 * k by omega), t_dvd Nat.prime_three (show 3 ∣ k by omega),
      t_ndvd p7 (q := 6) rfl hk7]
    ring
  · obtain ⟨c, hc⟩ := h36
    obtain ⟨w, rfl⟩ : ∃ w, n = 2 * (3 * w) := ⟨6 * c, by omega⟩
    have hw7 : ¬ 7 ∣ w := by
      intro h
      apply h7
      omega
    refine ⟨7 * w, by omega, ?_⟩
    rw [t_ndvd p7 (q := 6) rfl hw7, t_dvd Nat.prime_two (show 2 ∣ 3 * w by omega),
      t_dvd Nat.prime_three (show 3 ∣ w by omega)]
    ring

end OMA.Carmichael2

theorem OMA.solution : OMA.R_CarmichaelTotient_charmichaelTotient_R1.H2 := by
  intro n h36 h49
  exact OMA.Carmichael2.not_49 n h36 h49
