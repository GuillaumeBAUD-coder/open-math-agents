import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1_H2_R1

open scoped ArithmeticFunction.sigma

namespace A63H1

theorem sigma_odd (d : ℕ) (hd : Odd d)
    (he : ∀ q : ℕ, q.Prime → q ∣ d → Even (d.factorization q)) : Odd (σ 1 d) := by
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hd0]
  apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hpo : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h | h
    · subst h; exact absurd (hd.of_dvd_nat hpd) (by decide)
    · exact h
  obtain ⟨j, hj⟩ := he p hpp hpd
  show Odd (σ 1 (p ^ d.factorization p))
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hpp, Nat.odd_iff, Finset.sum_nat_mod]
  have : ∀ i ∈ Finset.range (d.factorization p + 1), p ^ i % 2 = 1 := by
    intro i _; rw [Nat.pow_mod, hpo, one_pow]; rfl
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, hj]
  omega

end A63H1

theorem OMA.solution : OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1_H2_R1.H1 := by
  intro d hd _ he hA
  have ho := A63H1.sigma_odd d hd he
  rw [hA.2] at ho
  exact (Nat.not_odd_iff_even.mpr (even_two_mul _)) ho
