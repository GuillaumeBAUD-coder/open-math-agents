import OMAReductions.R_oeis_a338272_R1

/-! Classify the squarefree part of a number congruent to one modulo four. -/

namespace OMA.A338272

lemma square_mod_four (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt a (by decide : 0 < 4)
  interval_cases a % 4 <;> decide

/-- The two-squares criterion supplies a prime factor congruent to three modulo four. -/
lemma prime_factor_of_not_two_squares {s : ℕ} (h : ¬ ∃ x y : ℕ, s = x ^ 2 + y ^ 2) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ p ∣ s := by
  by_contra missing
  apply h
  apply Nat.eq_sq_add_sq_iff.mpr
  intro p hp hpmod
  exact (missing ⟨p, Nat.prime_of_mem_primeFactors hp, hpmod,
    Nat.dvd_of_mem_primeFactors hp⟩).elim

end OMA.A338272

open OMA.A338272

theorem OMA.solution : OMA.R_oeis_a338272_R1.H1 := by
  intro n hn hnmod
  obtain ⟨s, d, hs, _, hsplit, hfree⟩ := Nat.sq_mul_squarefree_of_pos hn
  by_cases hsum : ∃ x y : ℕ, s = x ^ 2 + y ^ 2
  · obtain ⟨x, y, hxy⟩ := hsum
    left
    refine ⟨d * x, d * y, ?_⟩
    rw [← hsplit, hxy]
    ring
  right
  have hsmod : s % 4 = 1 := by
    rw [← hsplit, Nat.mul_mod] at hnmod
    rcases square_mod_four d with hd | hd <;> simp [hd] at hnmod
    exact hnmod
  obtain ⟨p, hp, hpmod, t, ht⟩ := prime_factor_of_not_two_squares hsum
  have htmod : t % 4 = 3 := by
    have h := hsmod
    rw [ht, Nat.mul_mod, hpmod] at h
    omega
  have ht_not_sum : ¬ ∃ x y : ℕ, t = x ^ 2 + y ^ 2 := by
    rintro ⟨x, y, rfl⟩
    rw [Nat.add_mod] at htmod
    rcases square_mod_four x with hx | hx <;>
      rcases square_mod_four y with hy | hy <;> simp [hx, hy] at htmod
  obtain ⟨q, hq, hqmod, hqt⟩ := prime_factor_of_not_two_squares ht_not_sum
  have hpq : p * q ∣ s := ht ▸ Nat.mul_dvd_mul_left p hqt
  refine ⟨s, d, hs, hsmod, hfree, hsplit.symm, p, q, hp, hq, ?_, hpmod, hqmod, hpq⟩
  rintro rfl
  exact Nat.squarefree_iff_prime_squarefree.mp hfree p hp hpq
