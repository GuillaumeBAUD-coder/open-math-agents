import OMAReductions.R_CarmichaelTotient_charmichaelTotient_R1

-- A multiple of 36 and 49 that is not divisible by 43^2 shares its totient with another integer.
-- Original Lean proof of the third step of Carmichael's 1922 argument: if 43 does not divide n take 43n/42
-- (phi(43) = 42 = 2 * 3 * 7), and if 43 divides n exactly once take 42n/43.
-- A classical partial result, not progress on the conjecture.

namespace OMA.Carmichael3

lemma t_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) : (p * n).totient = p * n.totient :=
  Nat.totient_mul_of_prime_of_dvd hp h

lemma t_ndvd {p n q : ℕ} (hp : p.Prime) (hq : q + 1 = p) (h : ¬ p ∣ n) :
    (p * n).totient = q * n.totient := by
  rw [Nat.totient_mul_of_prime_of_not_dvd hp h]
  subst hq
  simp

theorem not_1849 (n : ℕ) (h36 : 36 ∣ n) (h49 : 49 ∣ n) (h43 : ¬ 1849 ∣ n) :
    CarmichaelTotient.CarmichaelTotientFor n := by
  unfold CarmichaelTotient.CarmichaelTotientFor
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact absurd (dvd_zero 1849) h43
    · exact h
  have p7 : Nat.Prime 7 := by norm_num
  have p43 : Nat.Prime 43 := by norm_num
  by_cases c43 : 43 ∣ n
  · obtain ⟨k, rfl⟩ := c43
    have hk43 : ¬ 43 ∣ k := by
      intro h
      apply h43
      omega
    have hk36 : 36 ∣ k := by omega
    have hk49 : 49 ∣ k := by omega
    refine ⟨2 * (3 * (7 * k)), by omega, ?_⟩
    rw [t_dvd Nat.prime_two (show 2 ∣ 3 * (7 * k) by omega),
      t_dvd Nat.prime_three (show 3 ∣ 7 * k by omega), t_dvd p7 (show 7 ∣ k by omega),
      t_ndvd p43 (q := 42) rfl hk43]
    ring
  · have h1764 : 1764 ∣ n := by omega
    obtain ⟨c, hc⟩ := h1764
    obtain ⟨w, rfl⟩ : ∃ w, n = 2 * (3 * (7 * w)) := ⟨42 * c, by omega⟩
    have hw43 : ¬ 43 ∣ w := by
      intro h
      apply c43
      omega
    refine ⟨43 * w, by omega, ?_⟩
    rw [t_ndvd p43 (q := 42) rfl hw43, t_dvd Nat.prime_two (show 2 ∣ 3 * (7 * w) by omega),
      t_dvd Nat.prime_three (show 3 ∣ 7 * w by omega), t_dvd p7 (show 7 ∣ w by omega)]
    ring

end OMA.Carmichael3

theorem OMA.solution : OMA.R_CarmichaelTotient_charmichaelTotient_R1.H3 := by
  intro n h36 h49 h43
  exact OMA.Carmichael3.not_1849 n h36 h49 h43
