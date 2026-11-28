import OMAReductions.R_oeis_a338272_R1

/-! Classification of `n ≡ 1 (mod 4)` into sums of two squares or numbers whose
squarefree kernel has two distinct prime factors `≡ 3 (mod 4)`. -/

private lemma sq_mod_four (x : ℕ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  rw [sq, Nat.mul_mod]
  have := Nat.mod_lt x (by decide : 0 < 4)
  interval_cases x % 4 <;> decide

private lemma exists_prime_mod4_3 {m : ℕ} (h : ¬ ∃ u v, m = u ^ 2 + v ^ 2) :
    ∃ p, p.Prime ∧ p ∣ m ∧ p % 4 = 3 := by
  by_contra! hall
  exact h (Nat.eq_sq_add_sq_iff.2 fun p hp hp3 =>
    absurd hp3 (hall p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)))

theorem OMA.solution : OMA.R_oeis_a338272_R1.H1 := by
  intro n hn hn4
  obtain ⟨s, d, hs0, -, hds, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hs4 : s % 4 = 1 := by
    have hm : (d ^ 2 % 4 * (s % 4)) % 4 = 1 := by rw [← Nat.mul_mod, hds, hn4]
    rcases sq_mod_four d with h | h <;> rw [h] at hm <;> omega
  by_cases hsum : ∃ u v : ℕ, s = u ^ 2 + v ^ 2
  · obtain ⟨u, v, huv⟩ := hsum
    exact Or.inl ⟨d * u, d * v, by rw [← hds, huv]; ring⟩
  · obtain ⟨p, hp, ⟨t, rfl⟩, hp3⟩ := exists_prime_mod4_3 hsum
    have ht3 : t % 4 = 3 := by
      have hm : (p % 4 * (t % 4)) % 4 = 1 := by rw [← Nat.mul_mod, hs4]
      rw [hp3] at hm
      omega
    have htsum : ¬ ∃ u v : ℕ, t = u ^ 2 + v ^ 2 := by
      rintro ⟨u, v, rfl⟩
      rcases sq_mod_four u with hu | hu <;> rcases sq_mod_four v with hv | hv <;> omega
    obtain ⟨q, hq, hqt, hq3⟩ := exists_prime_mod4_3 htsum
    have hpq : p ≠ q := by
      rintro rfl
      obtain ⟨k, rfl⟩ := hqt
      exact hp.ne_one (Nat.isUnit_iff.1 (hsf p ⟨k, by ring⟩))
    exact Or.inr ⟨p * t, d, hs0, hs4, hsf, hds.symm, p, q, hp, hq, hpq, hp3, hq3,
      mul_dvd_mul_left p hqt⟩
