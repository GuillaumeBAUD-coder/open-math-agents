import OMAReductions.R_OeisA1599_eq_one_of_odd_of_a_R1

-- No prime power is a harmonic number (Ore 1948).
-- Original Lean proof of a classical fact: for n = p^k with k > 0 the divisor sum S = 1 + p + ... + p^k is
-- congruent to 1 modulo p, hence coprime to p^k, so S dividing p^k * (k + 1) forces S to divide k + 1; but S
-- is at least k + 2.
-- A classical first step, not progress on Ore's conjecture.

namespace OMA.Ore1

open ArithmeticFunction Finset

lemma sum_ge (p : ℕ) (hp : 2 ≤ p) : ∀ j : ℕ, j + 3 ≤ ∑ i ∈ range (j + 2), p ^ i := by
  intro j
  induction j with
  | zero =>
    simp [Finset.sum_range_succ]
    omega
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have h1 : 1 ≤ p ^ (j + 2) := Nat.one_le_pow _ _ (by omega)
    omega

theorem not_harmonic (n : ℕ) (hpp : IsPrimePow n) : ¬ OeisA1599.A n := by
  rintro ⟨-, hdvd⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [sigma_one_apply_prime_pow hp, sigma_zero_apply_prime_pow hp] at hdvd
  have hsplit : ∑ i ∈ range (j + 1 + 1), p ^ i = p * (∑ i ∈ range (j + 1), p ^ i) + 1 := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp [pow_succ']
  have hcop : Nat.Coprime p (∑ i ∈ range (j + 1 + 1), p ^ i) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp, hsplit]
    intro h
    have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_right p _)).mp h
    have h2 := Nat.le_of_dvd Nat.one_pos h1
    have h3 := hp.one_lt
    omega
  have hcop' : Nat.Coprime (∑ i ∈ range (j + 1 + 1), p ^ i) (p ^ (j + 1)) :=
    (hcop.pow_left (j + 1)).symm
  have hd : (∑ i ∈ range (j + 1 + 1), p ^ i) ∣ j + 1 + 1 :=
    hcop'.dvd_of_dvd_mul_left hdvd
  have h1 : ∑ i ∈ range (j + 1 + 1), p ^ i ≤ j + 1 + 1 := Nat.le_of_dvd (by omega) hd
  have h2 : j + 3 ≤ ∑ i ∈ range (j + 1 + 1), p ^ i := sum_ge p hp.two_le j
  have h3 : j + 3 ≤ j + 1 + 1 := le_trans h2 h1
  omega

end OMA.Ore1

theorem OMA.solution : OMA.R_OeisA1599_eq_one_of_odd_of_a_R1.H1 := by
  intro n hpp
  exact OMA.Ore1.not_harmonic n hpp
