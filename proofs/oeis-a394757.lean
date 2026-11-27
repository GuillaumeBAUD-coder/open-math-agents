import OMAStatements.S_oeis_a394757
import Mathlib.Tactic

-- A proof of both of Aied Sulaiman's conjectures by @anmolspace.
-- Pairing the terms in a geometric sum controls the prime divisors of sigma(k).

namespace TwinDivisorProof

open OMA.S_oeis_a394757 ArithmeticFunction Finset

private lemma paired_sum (p d j : ℕ) (hd : d ∣ 1+p) :
    d ∣ ∑ i ∈ range (2*j+2), p^i := by
  induction j with
  | zero => simpa [sum_range_succ, Nat.add_comm] using hd
  | succ j ih =>
    have pair : (∑ i ∈ range (2*(j+1)+2), p^i) =
        (∑ i ∈ range (2*j+2), p^i) + p^(2*j+2)*(1+p) := by
      rw [show 2*(j+1)+2=(2*j+2)+1+1 by omega, sum_range_succ, sum_range_succ, pow_succ p (2*j+2)]
      ring
    rw [pair]
    exact dvd_add ih (dvd_mul_of_dvd_right hd _)

/-- For an odd exponent of p in k, every divisor of 1+p divides sigma(k). -/
private lemma divisor_of_odd_exponent {k p d : ℕ} (hk : k ≠ 0) (hp : p.Prime)
    (he : k.factorization p % 2 = 1) (hd : d ∣ 1+p) : d ∣ sigma 1 k := by
  have localDiv : d ∣ sigma 1 (p ^ k.factorization p) := by
    rw [sigma_one_apply_prime_pow hp]
    obtain ⟨j,hj⟩ : ∃ j, k.factorization p + 1 = 2*j+2 := ⟨k.factorization p/2, by omega⟩
    rw [hj]
    exact paired_sum p d j hd
  have factor := Nat.ordProj_mul_ordCompl_eq_self k p
  have cop := (Nat.coprime_ordCompl (p := p) hp hk).pow_left (k.factorization p)
  calc
    d ∣ sigma 1 (p ^ k.factorization p) * sigma 1 (ordCompl[p] k) :=
      dvd_mul_of_dvd_left localDiv _
    _ = sigma 1 (p ^ k.factorization p * ordCompl[p] k) :=
      (isMultiplicative_sigma.map_mul_of_coprime cop).symm
    _ = sigma 1 k := congrArg (sigma 1) factor

private lemma midpoint_facts {k : ℕ} (large : 6 ≤ k) (left : (k-1).Prime)
    (right : (k+1).Prime) : 2 ∣ k ∧ 3 ∣ k ∧ ¬ IsSquare k := by
  have parity := left.eq_two_or_odd
  have leftThree : ¬ 3 ∣ k-1 := by
    intro h
    have := (Nat.dvd_prime left).mp h
    omega
  have rightThree : ¬ 3 ∣ k+1 := by
    intro h
    have := (Nat.dvd_prime right).mp h
    omega
  refine ⟨by omega, by omega, ?_⟩
  rintro ⟨r, hr⟩
  have rlarge : 3 ≤ r := by
    by_contra! small
    interval_cases r <;> omega
  have mul : k-1 = (r-1)*(r+1) := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s+1 := ⟨r-1, by omega⟩
    rw [show s+1-1=s by omega]
    have exactProduct : k = s*(s+1+1)+1 := by rw [hr]; ring
    omega
  rw [mul] at left
  exact Nat.not_prime_mul (by omega) (by omega) left

private lemma gcd_of_small_factor {k p : ℕ} (hg : (divisorGcd k).Prime)
    (hp : p.Prime) (hk : p ∣ k) (hs : p ∣ sigma 1 k) : divisorGcd k = p :=
  ((Nat.prime_dvd_prime_iff_eq hp hg).mp (Nat.dvd_gcd hk hs)).symm

private lemma nine_dvd {k : ℕ} (hk : k ≠ 0) (evenK : 2 ∣ k) (threeK : 3 ∣ k)
    (hg : (divisorGcd k).Prime) : 9 ∣ k := by
  by_contra absent
  have power3 : ¬ 3^2 ∣ k := by simpa using absent
  have v3 := Nat.prime_three.factorization_pos_of_dvd hk threeK
  have v3bound := mt (Nat.prime_three.pow_dvd_iff_le_factorization hk).mpr power3
  have fourSigma : 4 ∣ sigma 1 k :=
    divisor_of_odd_exponent hk Nat.prime_three (by omega) (by decide)
  have g2 := gcd_of_small_factor hg Nat.prime_two evenK ((by decide : 2 ∣ 4).trans fourSigma)
  have noFour : ¬ 2^2 ∣ k := by
    intro fourK
    have h : 4 ∣ divisorGcd k := Nat.dvd_gcd fourK fourSigma
    rw [g2] at h
    omega
  have v2 := Nat.prime_two.factorization_pos_of_dvd hk evenK
  have v2bound := mt (Nat.prime_two.pow_dvd_iff_le_factorization hk).mpr noFour
  have threeSigma : 3 ∣ sigma 1 k :=
    divisor_of_odd_exponent hk Nat.prime_two hv (by omega) (by decide)
  have g3 := gcd_of_small_factor hg Nat.prime_three threeK threeSigma
  omega

private lemma square_of_even_exponents {k : ℕ} (hk : k ≠ 0)
    (h : ∀ p : ℕ, p.Prime → k.factorization p % 2 = 0) : IsSquare k := by
  refine ⟨∏ p ∈ k.primeFactors, p ^ (k.factorization p / 2), ?_⟩
  calc
    k = ∏ p ∈ k.primeFactors, p ^ k.factorization p := Nat.prod_primeFactors_pow_factorization hk
    _ = _ := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_add]
      have hv := h p (Nat.prime_of_mem_primeFactors hp)
      congr 1
      omega

private lemma gcd_values {k : ℕ} (hk : k ≠ 0) (evenK : 2 ∣ k) (threeK : 3 ∣ k)
    (nonSquare : ¬ IsSquare k) (hg : (divisorGcd k).Prime) :
    divisorGcd k = 2 ∨ divisorGcd k = 3 := by
  by_contra none
  apply nonSquare (square_of_even_exponents hk ?_)
  intro p hp
  by_contra odd
  have hv : k.factorization p % 2 = 1 := by omega
  rcases hp.eq_two_or_odd with rfl | pOdd
  · have h3 : 3 ∣ sigma 1 k := divisor_of_odd_exponent hk Nat.prime_two hv (by decide)
    exact none (Or.inr (gcd_of_small_factor hg Nat.prime_three threeK h3))
  · have h2 : 2 ∣ sigma 1 k := divisor_of_odd_exponent hk hp hv (by omega)
    exact none (Or.inl (gcd_of_small_factor hg Nat.prime_two evenK h2))

end TwinDivisorProof

open TwinDivisorProof OMA.S_oeis_a394757 in
theorem OMA.solution : type_of% @OMA.S_oeis_a394757.main := by
  intro k ht
  by_cases large : 6 ≤ k
  · obtain ⟨hleft, hright, hg⟩ := ht
    obtain ⟨h2, h3, hn⟩ := midpoint_facts large hleft hright
    have hk : k ≠ 0 := by omega
    have h9 := nine_dvd hk h2 h3 hg
    exact ⟨by omega, gcd_values hk h2 h3 hn hg⟩
  · interval_cases k <;> revert ht <;> unfold IsTerm divisorGcd <;> decide +kernel
