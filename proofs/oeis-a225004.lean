import OMAStatements.S_oeis_a225004

namespace OMA.S_oeis_a225004.Pf
open OMA.S_oeis_a225004

lemma card_div_split (m p : ℕ) (hp : p.Prime) (hm : m ≠ 0) :
    m.divisors.card = (m.factorization p + 1) * (ordCompl[p] m).divisors.card := by
  have hc : (p ^ m.factorization p).Coprime (ordCompl[p] m) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hm)
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m p]
  rw [Nat.Coprime.card_divisors_mul hc, Nat.divisors_prime_pow hp, Finset.card_map,
    Finset.card_range]

lemma mem_S_dvd (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : m ∈ S n) : m ∣ n ^ 2 := by
  obtain ⟨hnm, hm0, hcard⟩ := hm
  have hm0' : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  rw [← Nat.factorization_le_iff_dvd hm0' (pow_ne_zero 2 hn0)]
  intro p
  rw [Nat.factorization_pow]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  by_cases hp : p.Prime
  · by_contra hlt
    push Not at hlt
    have h1 := card_div_split m p hp hm0'
    have h2 := card_div_split n p hp hn0
    have hd : (ordCompl[p] n).divisors.card ≤ (ordCompl[p] m).divisors.card := by
      apply Finset.card_le_card
      apply Nat.divisors_subset_of_dvd
      · exact (Nat.ordCompl_pos p hm0').ne'
      · exact Nat.ordCompl_dvd_ordCompl_of_dvd hnm p
    have : 2 * (n.factorization p + 1) ≤ m.factorization p + 1 := by omega
    have : 2 * n.divisors.card ≤ m.divisors.card := by
      rw [h1, h2]
      calc 2 * ((n.factorization p + 1) * (ordCompl[p] n).divisors.card)
          = (2 * (n.factorization p + 1)) * (ordCompl[p] n).divisors.card := by ring
        _ ≤ (m.factorization p + 1) * (ordCompl[p] m).divisors.card :=
          Nat.mul_le_mul this hd
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime m hp]

end OMA.S_oeis_a225004.Pf

open OMA.S_oeis_a225004 OMA.S_oeis_a225004.Pf in
theorem OMA.solution : type_of% @OMA.S_oeis_a225004.main := by
  intro n hn m hm
  exact mem_S_dvd n hn m hm.1
