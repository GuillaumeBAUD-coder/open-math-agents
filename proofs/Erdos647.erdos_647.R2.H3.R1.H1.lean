import OMAReductions.R_Erdos647_erdos_647_R2_H3_R1
import Mathlib

-- Step Erdos647.erdos_647.R2.H3.R1.H1: hypothesis H1 of reduction Erdos647.erdos_647.R2.H3.R1
-- Credit: @Raimo33

open ArithmeticFunction.sigma ArithmeticFunction

namespace RaimoDivB

def N : ℕ → ℕ
  | 2 => 2075942 | 3 => 192902 | 5 => 32768 | 7 => 14878 | 11 => 6025 | 13 => 4924
  | 17 => 3765 | 19 => 3369 | 23 => 2783 | 29 => 2207 | 31 => 2065 | 37 => 1730
  | 41 => 1561 | 43 => 1489 | 47 => 1362 | 53 => 1208 | 59 => 1085 | 61 => 1050
  | _ => 1000

def E : ℕ → ℕ
  | 2 => 8 | 3 => 4 | 5 => 3 | 7 => 2 | 11 => 2 | 13 => 1
  | 17 => 1 | 19 => 1 | 23 => 1 | 29 => 1 | 31 => 1 | 37 => 1
  | 41 => 1 | 43 => 1 | 47 => 1 | 53 => 1 | 59 => 1 | 61 => 1
  | _ => 0

lemma E_large (p : ℕ) (hp : 64 ≤ p) : E p = 0 := by
  unfold E; split <;> omega

lemma grow (D M p : ℕ) (hp : 2 ≤ p) (base : ∀ k ≤ 9, (k+1)^6*D ≤ M*p^k) :
    ∀ k, (k+1)^6*D ≤ M*p^k := by
  have step : ∀ j, (j+10)^6*D ≤ M*p^(j+9) := by
    intro j
    induction j with
    | zero => exact base 9 le_rfl
    | succ j ih =>
      have hpoly : (j+1+10)^6 ≤ 2*(j+10)^6 := by ring_nf; nlinarith [Nat.zero_le j, Nat.zero_le (j^2), Nat.zero_le (j^3), Nat.zero_le (j^4), Nat.zero_le (j^5), Nat.zero_le (j^6)]
      calc (j+1+10)^6*D ≤ 2*(j+10)^6*D := Nat.mul_le_mul_right _ hpoly
        _ = 2*((j+10)^6*D) := by ring
        _ ≤ 2*(M*p^(j+9)) := Nat.mul_le_mul_left _ ih
        _ ≤ p*(M*p^(j+9)) := Nat.mul_le_mul_right _ hp
        _ = M*p^(j+1+9) := by ring
  intro k
  by_cases hk : k ≤ 9
  · exact base k hk
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    have := step j
    have e : j + 9 + 1 = j + 10 := by ring
    rw [e]; exact this

lemma localE (p k : ℕ) (hp : p.Prime) : (k+1)^6 * p^(E p) ≤ (E p+1)^6 * p^k := by
  by_cases h64 : 64 ≤ p
  · rw [E_large p h64]
    simp only [pow_zero, mul_one, zero_add, one_pow, one_mul]
    have h1 : k + 1 ≤ 2^k := Nat.lt_two_pow_self
    calc (k+1)^6 ≤ (2^k)^6 := Nat.pow_le_pow_left h1 6
      _ = 64^k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ p^k := Nat.pow_le_pow_left h64 k
  · rw [not_le] at h64
    have h2 := hp.two_le
    interval_cases p <;> first
      | (exfalso; norm_num at hp; done)
      | exact grow _ _ _ (by norm_num) (by intro k hk; interval_cases k <;> norm_num [E]) k

lemma fm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (q : ℕ) :
    (a*b).factorization q = a.factorization q + b.factorization q := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]

lemma pp {p : ℕ} (e : ℕ) (hp : p.Prime) (q : ℕ) : (p^e).factorization q = if p = q then e else 0 := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, hp.factorization, Finsupp.single_apply]
  split_ifs <;> simp

lemma pp1 {p : ℕ} (hp : p.Prime) (q : ℕ) : p.factorization q = if p = q then 1 else 0 := by
  rw [hp.factorization, Finsupp.single_apply]

lemma facN0 (q : ℕ) : (780296143507862696557498656000 : ℕ).factorization q = E q := by
  have h : (780296143507862696557498656000 : ℕ) = 2^8*3^4*5^3*7^2*11^2*13*17*19*23*29*31*37*41*43*47*53*59*61 := by norm_num
  rw [h]
  simp (disch := norm_num) only [fm, pp, pp1]
  rcases lt_or_ge q 64 with hq | hq
  · interval_cases q <;> rfl
  · rw [E_large q hq]
    simp only [if_neg (show ¬ (2 = q) by omega), if_neg (show ¬ (3 = q) by omega), if_neg (show ¬ (5 = q) by omega), if_neg (show ¬ (7 = q) by omega), if_neg (show ¬ (11 = q) by omega), if_neg (show ¬ (13 = q) by omega), if_neg (show ¬ (17 = q) by omega), if_neg (show ¬ (19 = q) by omega), if_neg (show ¬ (23 = q) by omega), if_neg (show ¬ (29 = q) by omega), if_neg (show ¬ (31 = q) by omega), if_neg (show ¬ (37 = q) by omega), if_neg (show ¬ (41 = q) by omega), if_neg (show ¬ (43 = q) by omega), if_neg (show ¬ (47 = q) by omega), if_neg (show ¬ (53 = q) by omega), if_neg (show ¬ (59 = q) by omega), if_neg (show ¬ (61 = q) by omega)]

lemma prodS (n : ℕ) (hn : n ≠ 0) (S : Finset ℕ) (hS : n.primeFactors ⊆ S) :
    n.divisors.card = ∏ p ∈ S, (n.factorization p + 1) ∧ n = ∏ p ∈ S, p ^ (n.factorization p) := by
  have z : ∀ p ∈ S, p ∉ n.primeFactors → n.factorization p = 0 := by
    intro p _ hp
    exact Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
  constructor
  · rw [Nat.card_divisors hn]
    apply Finset.prod_subset hS
    intro p hpS hp; rw [z p hpS hp]; rfl
  · conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
    apply Finset.prod_subset hS
    intro p hpS hp; rw [z p hpS hp, pow_zero]

theorem H1 : ∀ A B m : ℕ, A*B = 780296143507862696557498656000 → A.Coprime B → A.Coprime m →
    (σ 0 m)^6 * B ≤ (σ 0 B)^6 * m := by
  intro A B m hAB hcop hAm
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hA : A ≠ 0 := by rintro rfl; simp at hAB
  have hB : B ≠ 0 := by rintro rfl; simp at hAB
  set S := m.primeFactors ∪ B.primeFactors
  obtain ⟨hm1, hm2⟩ := prodS m hm S Finset.subset_union_left
  obtain ⟨hB1, hB2⟩ := prodS B hB S Finset.subset_union_right
  rw [sigma_zero_apply, sigma_zero_apply, hm1, hB1]
  conv_lhs => rw [hB2]
  conv_rhs => rw [hm2]
  rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro p hp
  have hpp : p.Prime := by
    rcases Finset.mem_union.mp hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
  by_cases hpA : p ∣ A
  · have h1 : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hpp).mp (Nat.Coprime.coprime_dvd_left hpA hAm)
    have h2 : ¬ p ∣ B := (Nat.Prime.coprime_iff_not_dvd hpp).mp (Nat.Coprime.coprime_dvd_left hpA hcop)
    rw [Nat.factorization_eq_zero_of_not_dvd h1, Nat.factorization_eq_zero_of_not_dvd h2]
  · have hfac : B.factorization p = E p := by
      have := congrArg (fun n => n.factorization p) hAB
      rw [Nat.factorization_mul hA hB, Finsupp.add_apply, facN0,
        Nat.factorization_eq_zero_of_not_dvd hpA, zero_add] at this
      exact this
    rw [hfac]
    exact localE p _ hpp

end RaimoDivB

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R2_H3_R1.H1 := RaimoDivB.H1
