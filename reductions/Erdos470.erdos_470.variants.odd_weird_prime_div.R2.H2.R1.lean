import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2
import Mathlib

/-!
Reduction Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2.R1
of step Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2

Credit: @hoodbroskillson

For an odd primitive abundant multiple m of 9 with at most 5 distinct prime factors,
we settle:
  1. The entire case coprime to 35 (neither 5 nor 7 divides m): the prime set must be
     {3, 11, 13, 17, 19}, yielding exactly four primitive abundant numbers, each certified
     pseudoperfect via an explicit 4-to-7 divisor excess subset.
  2. All base and single-prime multiples of 315: {945, 1575, 2205} and 315 * p for all
     23 primes 11 ≤ p ≤ 103, plus the sharp bound 107 ≤ p ≤ 199 on the fourth prime for
     the remaining multiples of 315.
  3. Sharp third-prime bounds for the two remaining cases: 11 ≤ p ≤ 43 when 45 ∣ m, 7 ∤ m (H1),
     and p ∈ {11, 13, 17, 19} when 63 ∣ m, 5 ∤ m (H2).
-/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1

open Finset

/- Part 1: Abundancy Bound and Divisor-Sum Infrastructure -/

private lemma prime_power_sum_le {p : ℕ} (hp : 1 < p) (a : ℕ) {w : ℚ}
    (hw : (p : ℚ) ≤ w * (p - 1)) :
    (∑ j ∈ range (a + 1), (p : ℚ) ^ j) ≤ w * (p : ℚ) ^ a := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  apply (mul_le_mul_iff_left₀ (sub_pos.mpr hp')).mp
  rw [geom_sum_mul, pow_succ]
  have h := mul_le_mul_of_nonneg_right hw (show 0 ≤ (p : ℚ) ^ a by positivity)
  linarith only [h]

private lemma abundancy_bound {n : ℕ} (hn : 0 < n) (hc : n.primeFactors.card ≤ 5)
    (b : ℚ) (hb : 1 ≤ b) (E : Finset ℕ) (c : ℕ → ℚ)
    (hcorr : ∀ p ∈ E, 1 ≤ c p)
    (hlocal : ∀ p ∈ n.primeFactors, (∑ j ∈ range (n.factorization p + 1), (p : ℚ) ^ j) ≤
      b * (if p ∈ E then c p else 1) * (p : ℚ) ^ n.factorization p) :
    n.abundancyIndex ≤ b ^ 5 * ∏ p ∈ E, c p := by
  have hs : (∑ d ∈ n.divisors, (d : ℚ)) =
      ∏ p ∈ n.primeFactors, ∑ j ∈ range (n.factorization p + 1), (p : ℚ) ^ j := by
    simpa only [Nat.cast_sum, Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun k : ℕ => (k : ℚ)) (Nat.sum_divisors hn.ne')
  have hnprod : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn.ne'
  have hsub : n.primeFactors.filter (· ∈ E) ⊆ E :=
    fun _ hp => (mem_filter.mp hp).2
  have hexc : (∏ p ∈ n.primeFactors, if p ∈ E then c p else 1) ≤ ∏ p ∈ E, c p := by
    rw [← prod_filter]
    exact prod_le_prod_of_subset_of_one_le hsub
      (fun p hp => (hcorr p (hsub hp)).trans' zero_le_one) (fun p hp _ => hcorr p hp)
  rw [Nat.abundancyIndex, div_le_iff₀ (show 0 < (n : ℚ) by exact_mod_cast hn)]
  push_cast
  calc
    _ = _ := hs
    _ ≤ ∏ p ∈ n.primeFactors,
        (b * (if p ∈ E then c p else 1) * (p : ℚ) ^ n.factorization p) :=
      prod_le_prod (fun _ _ => sum_nonneg fun _ _ => by positivity) hlocal
    _ = (b ^ n.primeFactors.card *
          (∏ p ∈ n.primeFactors, if p ∈ E then c p else 1)) * n := by
      rw [prod_mul_distrib, prod_mul_distrib, prod_const, ← hnprod]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul (pow_le_pow_right₀ hb hc) hexc _ (by positivity)
      apply prod_nonneg
      intro p _
      split_ifs with h
      · exact (hcorr p h).trans' zero_le_one
      · norm_num

private lemma abundancy_of_primeFactors_eq {n : ℕ} (hn : 0 < n) (S : Finset ℕ)
    (hS : n.primeFactors = S) :
    n.abundancyIndex =
      ∏ p ∈ S, (∑ j ∈ range (n.factorization p + 1), (p : ℚ) ^ j) / (p : ℚ) ^ n.factorization p := by
  have hs : (∑ d ∈ n.divisors, (d : ℚ)) =
      ∏ p ∈ S, ∑ j ∈ range (n.factorization p + 1), (p : ℚ) ^ j := by
    rw [← hS]
    simpa only [Nat.cast_sum, Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun k : ℕ => (k : ℚ)) (Nat.sum_divisors hn.ne')
  have hnprod : (n : ℚ) = ∏ p ∈ S, (p : ℚ) ^ n.factorization p := by
    rw [← hS]
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn.ne'
  rw [Nat.abundancyIndex]
  push_cast
  rw [hs, hnprod, prod_div_distrib]

private lemma factor_le_geo {p : ℕ} (hp : 1 < p) (a : ℕ) :
    (∑ j ∈ range (a + 1), (p : ℚ) ^ j) / (p : ℚ) ^ a ≤ (p : ℚ) / (p - 1) := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  have hpos : (0 : ℚ) < (p : ℚ) ^ a := by positivity
  rw [div_le_iff₀ hpos]
  apply prime_power_sum_le hp a
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hp'.ne')]

private lemma factor_mono {p : ℕ} (hp : 1 < p) {a b : ℕ} (hab : a ≤ b) :
    (∑ j ∈ range (a + 1), (p : ℚ) ^ j) / (p : ℚ) ^ a ≤
    (∑ j ∈ range (b + 1), (p : ℚ) ^ j) / (p : ℚ) ^ b := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  have hposa : (0 : ℚ) < (p : ℚ) ^ a := by positivity
  have hposb : (0 : ℚ) < (p : ℚ) ^ b := by positivity
  have hsub : (0 : ℚ) < (p : ℚ) - 1 := sub_pos.mpr hp'
  rw [div_le_div_iff₀ hposa hposb]
  apply (mul_le_mul_iff_right₀ hsub).mp
  have ha : ((p : ℚ) - 1) * ((∑ j ∈ range (a + 1), (p : ℚ) ^ j) * (p : ℚ) ^ b) =
      ((p : ℚ) ^ (a + 1) - 1) * (p : ℚ) ^ b := by
    rw [← mul_assoc, mul_comm ((p : ℚ) - 1), geom_sum_mul]
  have hb : ((p : ℚ) - 1) * ((∑ j ∈ range (b + 1), (p : ℚ) ^ j) * (p : ℚ) ^ a) =
      ((p : ℚ) ^ (b + 1) - 1) * (p : ℚ) ^ a := by
    rw [← mul_assoc, mul_comm ((p : ℚ) - 1), geom_sum_mul]
  rw [ha, hb]
  have hpow : (p : ℚ) ^ a ≤ (p : ℚ) ^ b := pow_le_pow_right₀ hp'.le hab
  have heq : (p : ℚ) ^ (a + 1) * (p : ℚ) ^ b = (p : ℚ) ^ (b + 1) * (p : ℚ) ^ a := by
    rw [pow_succ, pow_succ]; ring
  linarith

private lemma sum_properDivisors_add_self {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.properDivisors, d) + n = ∑ d ∈ n.divisors, d := by
  have h := congrArg (fun s : Finset ℕ => ∑ d ∈ s, d) (Nat.cons_self_properDivisors hn.ne')
  simp only [sum_cons] at h
  omega

private lemma abundant_of_two_mul_lt_sum_divisors {n : ℕ} (hn : 0 < n)
    (h : 2 * n < ∑ d ∈ n.divisors, d) : n.Abundant := by
  have h1 := sum_properDivisors_add_self hn
  change n < ∑ d ∈ n.properDivisors, d
  omega

private lemma pseudoperfect_of_excess_subset {n : ℕ} (hn : 0 < n) {s : Finset ℕ}
    (hsub : s ⊆ n.properDivisors)
    (hsum : (∑ d ∈ s, d) + 2 * n = ∑ d ∈ n.divisors, d) : n.Pseudoperfect := by
  refine ⟨hn, n.properDivisors \ s, sdiff_subset, ?_⟩
  have hdiv := sum_properDivisors_add_self hn
  have hsdiff : (∑ d ∈ n.properDivisors \ s, d) + ∑ d ∈ s, d = ∑ d ∈ n.properDivisors, d :=
    sum_sdiff hsub
  omega

private lemma sum_divisors_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ d ∈ (p ^ k).divisors, d = (p ^ (k + 1) - 1) / (p - 1) := by
  rw [Nat.divisors_prime_pow hp, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have h1 : (∑ j ∈ range (k + 1), p ^ j) * (p - 1) = p ^ (k + 1) - 1 := by
    zify [Nat.one_le_pow (k + 1) p hp.pos, hp.one_lt.le]
    exact geom_sum_mul (p : ℤ) (k + 1)
  exact Nat.eq_div_of_mul_eq_left (Nat.sub_pos_of_lt hp.one_lt).ne' h1

private lemma prime_pow_factorization_eq {m p a : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hdvd : p ^ a ∣ m) (hndvd : ¬ p ^ (a + 1) ∣ m) : m.factorization p = a := by
  have h1 := (hp.pow_dvd_iff_le_factorization hm).mp hdvd
  have h2 : ¬ a + 1 ≤ m.factorization p := fun h =>
    hndvd ((hp.pow_dvd_iff_le_factorization hm).mpr h)
  omega

/- Part 2: Third-Prime Bounds for H1 (45 ∣ m, 7 ∤ m) and H2 (63 ∣ m, 5 ∤ m) -/

private lemma exists_prime_le_43_of_45_not_7 {m : ℕ} (ho : Odd m) (ha : m.Abundant)
    (hc : m.primeFactors.card ≤ 5) (h7 : ¬ 7 ∣ m) :
    ∃ p ∈ m.primeFactors, 11 ≤ p ∧ p ≤ 43 := by
  by_contra hno
  push Not at hno
  let E : Finset ℕ := {3, 5}
  let c : ℕ → ℚ := fun p => if p = 3 then 69 / 47 else 115 / 94
  have hsmall : ∀ p ∈ E, 1 ≤ c p := by intro p _; dsimp [c]; split_ifs <;> norm_num
  have h := abundancy_bound ho.pos hc (47 / 46) (by norm_num) E c hsmall (by
    intro p hp
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    apply prime_power_sum_le hprime.one_lt
    by_cases h3 : p = 3
    · subst p; norm_num [E, c]
    by_cases h5 : p = 5
    · subst p; norm_num [E, c]
    have h2 : p ≠ 2 := by rintro rfl; exact ho.not_two_dvd_nat hdvd
    have hn7 : p ≠ 7 := by rintro rfl; exact h7 hdvd
    have h11 : 11 ≤ p := by
      by_contra! hl
      interval_cases p <;> norm_num at *
    have h44 : 44 ≤ p := by have := hno p hp h11; omega
    have h47 : 47 ≤ p := by
      by_contra! hl
      interval_cases p <;> norm_num at *
    have h47' : (47 : ℚ) ≤ p := by exact_mod_cast h47
    simp [E, h3, h5]
    linarith)
  norm_num [E, c] at h
  linarith [Nat.abundant_iff_two_lt_abundancyIndex.mp ha]

private lemma exists_prime_11_19_of_63_not_5 {m : ℕ} (ho : Odd m) (ha : m.Abundant)
    (hc : m.primeFactors.card ≤ 5) (h5 : ¬ 5 ∣ m) :
    ∃ p ∈ m.primeFactors, p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 := by
  by_contra hno
  push Not at hno
  let E : Finset ℕ := {3, 7}
  let c : ℕ → ℚ := fun p => if p = 3 then 33 / 23 else 77 / 69
  have hsmall : ∀ p ∈ E, 1 ≤ c p := by intro p _; dsimp [c]; split_ifs <;> norm_num
  have h := abundancy_bound ho.pos hc (23 / 22) (by norm_num) E c hsmall (by
    intro p hp
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    apply prime_power_sum_le hprime.one_lt
    by_cases h3 : p = 3
    · subst p; norm_num [E, c]
    by_cases h7 : p = 7
    · subst p; norm_num [E, c]
    have h2 : p ≠ 2 := by rintro rfl; exact ho.not_two_dvd_nat hdvd
    have hn5 : p ≠ 5 := by rintro rfl; exact h5 hdvd
    obtain ⟨h11, h13, h17, h19⟩ := hno p hp
    have h23 : 23 ≤ p := by
      by_contra! hl
      interval_cases p <;> norm_num at *
    have h23' : (23 : ℚ) ≤ p := by exact_mod_cast h23
    simp [E, h3, h7]
    linarith)
  norm_num [E, c] at h
  linarith [Nat.abundant_iff_two_lt_abundancyIndex.mp ha]

/- Part 3: Case 1 — Coprime to 35 (Exact 4-Number Classification & Certificates) -/

private lemma primeFactors_coprime_35 {m : ℕ} (ho : Odd m) (ha : m.Abundant)
    (hc : m.primeFactors.card ≤ 5) (h9 : 9 ∣ m) (h5 : ¬ 5 ∣ m) (h7 : ¬ 7 ∣ m) :
    m.primeFactors = {3, 11, 13, 17, 19} := by
  have h3 : 3 ∈ m.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by decide, dvd_trans (by decide) h9, ho.pos.ne'⟩
  have h11 : 11 ∈ m.primeFactors := by
    by_contra hn11
    let E : Finset ℕ := {3, 13, 17, 19}
    let c : ℕ → ℚ := fun p =>
      if p = 3 then 33 / 23 else if p = 13 then 143 / 138 else if p = 17 then 187 / 184 else 209 / 207
    have h := abundancy_bound ho.pos hc (23 / 22) (by norm_num) E c
      (by intro p _; dsimp [c]; split_ifs <;> norm_num) (by
      intro p hp
      obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
      apply prime_power_sum_le hprime.one_lt
      by_cases hp3 : p = 3
      · subst p; norm_num [E, c]
      by_cases hp13 : p = 13
      · subst p; norm_num [E, c]
      by_cases hp17 : p = 17
      · subst p; norm_num [E, c]
      by_cases hp19 : p = 19
      · subst p; norm_num [E, c]
      have h2 : p ≠ 2 := by rintro rfl; exact ho.not_two_dvd_nat hdvd
      have hn5 : p ≠ 5 := by rintro rfl; exact h5 hdvd
      have hn7 : p ≠ 7 := by rintro rfl; exact h7 hdvd
      have hp11 : p ≠ 11 := by rintro rfl; exact hn11 hp
      have h23 : 23 ≤ p := by by_contra! hl; interval_cases p <;> norm_num at *
      have h23' : (23 : ℚ) ≤ p := by exact_mod_cast h23
      simp [E, hp3, hp13, hp17, hp19]; linarith)
    norm_num [E, c] at h
    linarith [Nat.abundant_iff_two_lt_abundancyIndex.mp ha]
  have h13 : 13 ∈ m.primeFactors := by
    by_contra hn13
    let E : Finset ℕ := {3, 11}
    let c : ℕ → ℚ := fun p => if p = 3 then 24 / 17 else 88 / 85
    have h := abundancy_bound ho.pos hc (17 / 16) (by norm_num) E c
      (by intro p _; dsimp [c]; split_ifs <;> norm_num) (by
      intro p hp
      obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
      apply prime_power_sum_le hprime.one_lt
      by_cases hp3 : p = 3
      · subst p; norm_num [E, c]
      by_cases hp11 : p = 11
      · subst p; norm_num [E, c]
      have h2 : p ≠ 2 := by rintro rfl; exact ho.not_two_dvd_nat hdvd
      have hn5 : p ≠ 5 := by rintro rfl; exact h5 hdvd
      have hn7 : p ≠ 7 := by rintro rfl; exact h7 hdvd
      have hp13 : p ≠ 13 := by rintro rfl; exact hn13 hp
      have h17 : 17 ≤ p := by by_contra! hl; interval_cases p <;> norm_num at *
      have h17' : (17 : ℚ) ≤ p := by exact_mod_cast h17
      simp [E, hp3, hp11]; linarith)
    norm_num [E, c] at h
    linarith [Nat.abundant_iff_two_lt_abundancyIndex.mp ha]
  have h17 : 17 ∈ m.primeFactors := by
    by_contra hn17
    let E : Finset ℕ := {3, 11, 13}
    let c : ℕ → ℚ := fun p => if p = 3 then 27 / 19 else if p = 11 then 99 / 95 else 39 / 38
    have h := abundancy_bound ho.pos hc (19 / 18) (by norm_num) E c
      (by intro p _; dsimp [c]; split_ifs <;> norm_num) (by
      intro p hp
      obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
      apply prime_power_sum_le hprime.one_lt
      by_cases hp3 : p = 3
      · subst p; norm_num [E, c]
      by_cases hp11 : p = 11
      · subst p; norm_num [E, c]
      by_cases hp13 : p = 13
      · subst p; norm_num [E, c]
      have h2 : p ≠ 2 := by rintro rfl; exact ho.not_two_dvd_nat hdvd
      have hn5 : p ≠ 5 := by rintro rfl; exact h5 hdvd
      have hn7 : p ≠ 7 := by rintro rfl; exact h7 hdvd
      have hp17 : p ≠ 17 := by rintro rfl; exact hn17 hp
      have h19 : 19 ≤ p := by by_contra! hl; interval_cases p <;> norm_num at *
      have h19' : (19 : ℚ) ≤ p := by exact_mod_cast h19
      simp [E, hp3, hp11, hp13]; linarith)
    norm_num [E, c] at h
    linarith [Nat.abundant_iff_two_lt_abundancyIndex.mp ha]
  have h19 : 19 ∈ m.primeFactors := by
    by_contra hn19
    let E : Finset ℕ := {3, 11, 13, 17}
    let c : ℕ → ℚ := fun p =>
      if p = 3 then 33 / 23 else if p = 11 then 121 / 115 else if p = 13 then 143 / 138 else 187 / 184
    have h := abundancy_bound ho.pos hc (23 / 22) (by norm_num) E c
      (by intro p _; dsimp [c]; split_ifs <;> norm_num) (by
      intro p hp
      obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
      apply prime_power_sum_le hprime.one_lt
      by_cases hp3 : p = 3
      · subst p; norm_num [E, c]
      by_cases hp11 : p = 11
      · subst p; norm_num [E, c]
      by_cases hp13 : p = 13
      · subst p; norm_num [E, c]
      by_cases hp17 : p = 17
      · subst p; norm_num [E, c]
      have h2 : p ≠ 2 := by rintro rfl; exact ho.not_two_dvd_nat hdvd
      have hn5 : p ≠ 5 := by rintro rfl; exact h5 hdvd
      have hn7 : p ≠ 7 := by rintro rfl; exact h7 hdvd
      have hp19 : p ≠ 19 := by rintro rfl; exact hn19 hp
      have h23 : 23 ≤ p := by by_contra! hl; interval_cases p <;> norm_num at *
      have h23' : (23 : ℚ) ≤ p := by exact_mod_cast h23
      simp [E, hp3, hp11, hp13, hp17]; linarith)
    norm_num [E, c] at h
    linarith [Nat.abundant_iff_two_lt_abundancyIndex.mp ha]
  have hsub : ({3, 11, 13, 17, 19} : Finset ℕ) ⊆ m.primeFactors := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> assumption
  exact (eq_of_subset_of_card_le hsub (by simpa using hc)).symm

private lemma sum_divisors_five_primes (a b c d e : ℕ) :
    ∑ x ∈ (3 ^ a * 11 ^ b * 13 ^ c * 17 ^ d * 19 ^ e).divisors, x =
      ((3 ^ (a + 1) - 1) / 2) * ((11 ^ (b + 1) - 1) / 10) *
      ((13 ^ (c + 1) - 1) / 12) * ((17 ^ (d + 1) - 1) / 16) * ((19 ^ (e + 1) - 1) / 18) := by
  have c1 : Nat.Coprime (3 ^ a * 11 ^ b * 13 ^ c * 17 ^ d) (19 ^ e) :=
    (((Nat.Coprime.pow a e (by decide)).mul_left (Nat.Coprime.pow b e (by decide))).mul_left
      (Nat.Coprime.pow c e (by decide))).mul_left (Nat.Coprime.pow d e (by decide))
  have c2 : Nat.Coprime (3 ^ a * 11 ^ b * 13 ^ c) (17 ^ d) :=
    ((Nat.Coprime.pow a d (by decide)).mul_left (Nat.Coprime.pow b d (by decide))).mul_left
      (Nat.Coprime.pow c d (by decide))
  have c3 : Nat.Coprime (3 ^ a * 11 ^ b) (13 ^ c) :=
    (Nat.Coprime.pow a c (by decide)).mul_left (Nat.Coprime.pow b c (by decide))
  have c4 : Nat.Coprime (3 ^ a) (11 ^ b) := Nat.Coprime.pow a b (by decide)
  rw [c1.sum_divisors_mul, c2.sum_divisors_mul, c3.sum_divisors_mul, c4.sum_divisors_mul,
    sum_divisors_prime_pow (by decide) a, sum_divisors_prime_pow (by decide) b,
    sum_divisors_prime_pow (by decide) c, sum_divisors_prime_pow (by decide) d,
    sum_divisors_prime_pow (by decide) e]

private lemma abundant_five_primes (a b c d e : ℕ)
    (hineq : 2 * (3 ^ a * 11 ^ b * 13 ^ c * 17 ^ d * 19 ^ e) <
      ((3 ^ (a + 1) - 1) / 2) * ((11 ^ (b + 1) - 1) / 10) *
      ((13 ^ (c + 1) - 1) / 12) * ((17 ^ (d + 1) - 1) / 16) * ((19 ^ (e + 1) - 1) / 18)) :
    (3 ^ a * 11 ^ b * 13 ^ c * 17 ^ d * 19 ^ e).Abundant := by
  apply abundant_of_two_mul_lt_sum_divisors (by positivity)
  rw [sum_divisors_five_primes]
  exact hineq

private lemma pseudoperfect_five_primes (a b c d e : ℕ) (s : Finset ℕ)
    (hsub : ∀ x ∈ s, x ∣ 3 ^ a * 11 ^ b * 13 ^ c * 17 ^ d * 19 ^ e ∧
      x < 3 ^ a * 11 ^ b * 13 ^ c * 17 ^ d * 19 ^ e)
    (hsum : (∑ x ∈ s, x) + 2 * (3 ^ a * 11 ^ b * 13 ^ c * 17 ^ d * 19 ^ e) =
      ((3 ^ (a + 1) - 1) / 2) * ((11 ^ (b + 1) - 1) / 10) *
      ((13 ^ (c + 1) - 1) / 12) * ((17 ^ (d + 1) - 1) / 16) * ((19 ^ (e + 1) - 1) / 18)) :
    (3 ^ a * 11 ^ b * 13 ^ c * 17 ^ d * 19 ^ e).Pseudoperfect := by
  apply pseudoperfect_of_excess_subset (by positivity)
    (fun x hx => Nat.mem_properDivisors.mpr (hsub x hx))
  rw [sum_divisors_five_primes]
  exact hsum

private lemma case_coprime_35 {m : ℕ} (ho : Odd m) (ha : m.Abundant)
    (hc : m.primeFactors.card ≤ 5) (hprim : ∀ d ∈ m.properDivisors, d.Deficient)
    (h9 : 9 ∣ m) (h5 : ¬ 5 ∣ m) (h7 : ¬ 7 ∣ m) : m.Pseudoperfect := by
  have hpf := primeFactors_coprime_35 ho ha hc h9 h5 h7
  set a := m.factorization 3
  set b := m.factorization 11
  set c := m.factorization 13
  set d := m.factorization 17
  set e := m.factorization 19
  have hm_eq : m = 3 ^ a * 11 ^ b * 13 ^ c * 17 ^ d * 19 ^ e := by
    have hp := Nat.prod_primeFactors_pow_factorization ho.pos.ne'
    rw [hpf] at hp
    simp only [prod_insert (by decide : (3 : ℕ) ∉ ({11, 13, 17, 19} : Finset ℕ)),
      prod_insert (by decide : (11 : ℕ) ∉ ({13, 17, 19} : Finset ℕ)),
      prod_insert (by decide : (13 : ℕ) ∉ ({17, 19} : Finset ℕ)),
      prod_insert (by decide : (17 : ℕ) ∉ ({19} : Finset ℕ)),
      prod_singleton] at hp
    linarith [hp, show 3 ^ a * (11 ^ b * (13 ^ c * (17 ^ d * 19 ^ e))) =
      3 ^ a * 11 ^ b * 13 ^ c * 17 ^ d * 19 ^ e by ring]
  have hab : (2 : ℚ) <
      ((∑ j ∈ range (a + 1), (3 : ℚ) ^ j) / (3 : ℚ) ^ a) *
      ((∑ j ∈ range (b + 1), (11 : ℚ) ^ j) / (11 : ℚ) ^ b) *
      ((∑ j ∈ range (c + 1), (13 : ℚ) ^ j) / (13 : ℚ) ^ c) *
      ((∑ j ∈ range (d + 1), (17 : ℚ) ^ j) / (17 : ℚ) ^ d) *
      ((∑ j ∈ range (e + 1), (19 : ℚ) ^ j) / (19 : ℚ) ^ e) := by
    have h2 := Nat.abundant_iff_two_lt_abundancyIndex.mp ha
    rw [abundancy_of_primeFactors_eq ho.pos {3, 11, 13, 17, 19} hpf] at h2
    simp only [prod_insert (by decide : (3 : ℕ) ∉ ({11, 13, 17, 19} : Finset ℕ)),
      prod_insert (by decide : (11 : ℕ) ∉ ({13, 17, 19} : Finset ℕ)),
      prod_insert (by decide : (13 : ℕ) ∉ ({17, 19} : Finset ℕ)),
      prod_insert (by decide : (17 : ℕ) ∉ ({19} : Finset ℕ)),
      prod_singleton] at h2
    linarith [h2, show
      ((∑ j ∈ range (a + 1), (3 : ℚ) ^ j) / (3 : ℚ) ^ a) *
      (((∑ j ∈ range (b + 1), (11 : ℚ) ^ j) / (11 : ℚ) ^ b) *
      (((∑ j ∈ range (c + 1), (13 : ℚ) ^ j) / (13 : ℚ) ^ c) *
      (((∑ j ∈ range (d + 1), (17 : ℚ) ^ j) / (17 : ℚ) ^ d) *
      ((∑ j ∈ range (e + 1), (19 : ℚ) ^ j) / (19 : ℚ) ^ e)))) =
      ((∑ j ∈ range (a + 1), (3 : ℚ) ^ j) / (3 : ℚ) ^ a) *
      ((∑ j ∈ range (b + 1), (11 : ℚ) ^ j) / (11 : ℚ) ^ b) *
      ((∑ j ∈ range (c + 1), (13 : ℚ) ^ j) / (13 : ℚ) ^ c) *
      ((∑ j ∈ range (d + 1), (17 : ℚ) ^ j) / (17 : ℚ) ^ d) *
      ((∑ j ∈ range (e + 1), (19 : ℚ) ^ j) / (19 : ℚ) ^ e) by ring]
  have hga := factor_le_geo (p := 3) (by decide) a
  have hgb := factor_le_geo (p := 11) (by decide) b
  have hgc := factor_le_geo (p := 13) (by decide) c
  have hgd := factor_le_geo (p := 17) (by decide) d
  have hge := factor_le_geo (p := 19) (by decide) e
  have hpos_f : ∀ (p k : ℕ), 0 ≤ (∑ j ∈ range (k + 1), (p : ℚ) ^ j) / (p : ℚ) ^ k :=
    fun p k => div_nonneg (sum_nonneg fun _ _ => by positivity) (by positivity)
  have hprod_le : ∀ {x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℚ},
      0 ≤ x1 → 0 ≤ x2 → 0 ≤ x3 → 0 ≤ x4 → 0 ≤ x5 →
      x1 ≤ y1 → x2 ≤ y2 → x3 ≤ y3 → x4 ≤ y4 → x5 ≤ y5 →
      x1 * x2 * x3 * x4 * x5 ≤ y1 * y2 * y3 * y4 * y5 := by
    intro x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 h1 h2 h3 h4 h5 l1 l2 l3 l4 l5
    exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul l1 l2 h2 (h1.trans l1)) l3 h3
      (mul_nonneg (h1.trans l1) (h2.trans l2))) l4 h4
      (mul_nonneg (mul_nonneg (h1.trans l1) (h2.trans l2)) (h3.trans l3))) l5 h5
      (mul_nonneg (mul_nonneg (mul_nonneg (h1.trans l1) (h2.trans l2)) (h3.trans l3)) (h4.trans l4))
  have ha5 : 5 ≤ a := by
    by_contra! hlt
    have hfa := factor_mono (p := 3) (by decide) (show a ≤ 4 by omega)
    have hle := lt_of_lt_of_le hab (hprod_le (hpos_f 3 a) (hpos_f 11 b) (hpos_f 13 c) (hpos_f 17 d) (hpos_f 19 e)
      hfa hgb hgc hgd hge)
    norm_num [sum_range_succ, sum_range_zero] at hle
  have hb2 : 2 ≤ b := by
    by_contra! hlt
    have hfb := factor_mono (p := 11) (by decide) (show b ≤ 1 by omega)
    have hle := lt_of_lt_of_le hab (hprod_le (hpos_f 3 a) (hpos_f 11 b) (hpos_f 13 c) (hpos_f 17 d) (hpos_f 19 e)
      hga hfb hgc hgd hge)
    norm_num [sum_range_succ, sum_range_zero] at hle
  have hc2 : 2 ≤ c := by
    by_contra! hlt
    have hfc := factor_mono (p := 13) (by decide) (show c ≤ 1 by omega)
    have hle := lt_of_lt_of_le hab (hprod_le (hpos_f 3 a) (hpos_f 11 b) (hpos_f 13 c) (hpos_f 17 d) (hpos_f 19 e)
      hga hgb hfc hgd hge)
    norm_num [sum_range_succ, sum_range_zero] at hle
  have hd2 : 2 ≤ d := by
    by_contra! hlt
    have hfd := factor_mono (p := 17) (by decide) (show d ≤ 1 by omega)
    have hle := lt_of_lt_of_le hab (hprod_le (hpos_f 3 a) (hpos_f 11 b) (hpos_f 13 c) (hpos_f 17 d) (hpos_f 19 e)
      hga hgb hgc hfd hge)
    norm_num [sum_range_succ, sum_range_zero] at hle
  have he2 : 2 ≤ e := by
    by_contra! hlt
    have hfe := factor_mono (p := 19) (by decide) (show e ≤ 1 by omega)
    have hle := lt_of_lt_of_le hab (hprod_le (hpos_f 3 a) (hpos_f 11 b) (hpos_f 13 c) (hpos_f 17 d) (hpos_f 19 e)
      hga hgb hgc hgd hfe)
    norm_num [sum_range_succ, sum_range_zero] at hle
  have prim_eq : ∀ a0 b0 c0 d0 e0 : ℕ, a0 ≤ a → b0 ≤ b → c0 ≤ c → d0 ≤ d → e0 ≤ e →
      (3 ^ a0 * 11 ^ b0 * 13 ^ c0 * 17 ^ d0 * 19 ^ e0).Abundant →
      m = 3 ^ a0 * 11 ^ b0 * 13 ^ c0 * 17 ^ d0 * 19 ^ e0 := by
    intro a0 b0 c0 d0 e0 la lb lc ld le hNab
    set N := 3 ^ a0 * 11 ^ b0 * 13 ^ c0 * 17 ^ d0 * 19 ^ e0
    have hdvd : N ∣ m := by
      rw [hm_eq]
      exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul
        (pow_dvd_pow 3 la) (pow_dvd_pow 11 lb)) (pow_dvd_pow 13 lc))
        (pow_dvd_pow 17 ld)) (pow_dvd_pow 19 le)
    by_contra hne
    have hlt : N < m := lt_of_le_of_ne (Nat.le_of_dvd ho.pos hdvd) (Ne.symm hne)
    have hdef := hprim N (Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩)
    exact (not_lt_of_gt hNab) hdef
  by_cases ha6 : 6 ≤ a
  · have hEq := prim_eq 6 2 2 2 2 ha6 hb2 hc2 hd2 he2
      (abundant_five_primes 6 2 2 2 2 (by norm_num))
    rw [hEq]
    exact pseudoperfect_five_primes 6 2 2 2 2
      {1022528529, 60148737, 3165723, 146523, 867, 11, 1}
      (by intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num)
      (by norm_num)
  have ha_eq : a = 5 := by omega
  by_cases hb3 : 3 ≤ b
  · have hEq := prim_eq 5 3 2 2 2 ha5 hb3 hc2 hd2 he2
      (abundant_five_primes 5 3 2 2 2 (by norm_num))
    rw [hEq]
    exact pseudoperfect_five_primes 5 3 2 2 2
      {1249757091, 84474819, 642447, 9801, 429, 3}
      (by intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num)
      (by norm_num)
  have hb_eq : b = 2 := by omega
  have hc3 : 3 ≤ c := by
    by_contra! hlt
    have hfc := factor_mono (p := 13) (by decide) (show c ≤ 2 by omega)
    have hle := lt_of_lt_of_le hab (hprod_le (hpos_f 3 a) (hpos_f 11 b) (hpos_f 13 c) (hpos_f 17 d) (hpos_f 19 e)
      (by rw [ha_eq]) (by rw [hb_eq]) hfc hgd hge)
    norm_num [sum_range_succ, sum_range_zero] at hle
  by_cases hd3 : 3 ≤ d
  · have hEq := prim_eq 5 2 3 3 2 ha5 hb2 hc3 hd3 he2
      (abundant_five_primes 5 2 3 3 2 (by norm_num))
    rw [hEq]
    exact pseudoperfect_five_primes 5 2 3 3 2
      {10165136553, 278871417, 1927341, 26163}
      (by intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl|rfl|rfl|rfl <;> norm_num)
      (by norm_num)
  have hd_eq : d = 2 := by omega
  have hc4 : 4 ≤ c := by
    by_contra! hlt
    have hfc := factor_mono (p := 13) (by decide) (show c ≤ 3 by omega)
    have hle := lt_of_lt_of_le hab (hprod_le (hpos_f 3 a) (hpos_f 11 b) (hpos_f 13 c) (hpos_f 17 d) (hpos_f 19 e)
      (by rw [ha_eq]) (by rw [hb_eq]) hfc (by rw [hd_eq]) hge)
    norm_num [sum_range_succ, sum_range_zero] at hle
  have he3 : 3 ≤ e := by
    by_contra! hlt
    have hfe := factor_mono (p := 19) (by decide) (show e ≤ 2 by omega)
    have hle := lt_of_lt_of_le hab (hprod_le (hpos_f 3 a) (hpos_f 11 b) (hpos_f 13 c) (hpos_f 17 d) (hpos_f 19 e)
      (by rw [ha_eq]) (by rw [hb_eq]) hgc (by rw [hd_eq]) hfe)
    norm_num [sum_range_succ, sum_range_zero] at hle
  have hEq := prim_eq 5 2 4 2 3 ha5 hb2 hc4 hd2 he3
    (abundant_five_primes 5 2 4 2 3 (by norm_num))
  rw [hEq]
  exact pseudoperfect_five_primes 5 2 4 2 3
    {80898718329, 497284359, 177957, 2223, 17, 9}
    (by intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num)
    (by norm_num)

/- Part 4: Case 4 — Multiples of 315 (Base Cases + All 23 Primes 315*p) -/

private lemma sum_divisors_three_primes (a b c : ℕ) :
    ∑ x ∈ (3 ^ a * 5 ^ b * 7 ^ c).divisors, x =
      ((3 ^ (a + 1) - 1) / 2) * ((5 ^ (b + 1) - 1) / 4) * ((7 ^ (c + 1) - 1) / 6) := by
  have c1 : Nat.Coprime (3 ^ a * 5 ^ b) (7 ^ c) :=
    (Nat.Coprime.pow a c (by decide)).mul_left (Nat.Coprime.pow b c (by decide))
  have c2 : Nat.Coprime (3 ^ a) (5 ^ b) := Nat.Coprime.pow a b (by decide)
  rw [c1.sum_divisors_mul, c2.sum_divisors_mul,
    sum_divisors_prime_pow (by decide) a, sum_divisors_prime_pow (by decide) b,
    sum_divisors_prime_pow (by decide) c]

private lemma sum_divisors_315 : ∑ d ∈ (315 : ℕ).divisors, d = 624 := by
  have h := sum_divisors_three_primes 2 1 1
  norm_num at h
  exact h

private lemma pseudo_945 : (945 : ℕ).Pseudoperfect := by
  apply pseudoperfect_of_excess_subset (by decide) (s := {27, 3})
  · intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Nat.mem_properDivisors.mpr (by norm_num)
  · have h := sum_divisors_three_primes 3 1 1; norm_num at h; rw [h]; norm_num

private lemma pseudo_1575 : (1575 : ℕ).Pseudoperfect := by
  apply pseudoperfect_of_excess_subset (by decide) (s := {63, 7, 3, 1})
  · intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact Nat.mem_properDivisors.mpr (by norm_num)
  · have h := sum_divisors_three_primes 2 2 1; norm_num at h; rw [h]; norm_num

private lemma pseudo_2205 : (2205 : ℕ).Pseudoperfect := by
  apply pseudoperfect_of_excess_subset (by decide) (s := {35, 1})
  · intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Nat.mem_properDivisors.mpr (by norm_num)
  · have h := sum_divisors_three_primes 2 1 2; norm_num at h; rw [h]; norm_num

private lemma abundant_945 : (945 : ℕ).Abundant := by
  apply abundant_of_two_mul_lt_sum_divisors (by decide)
  have h := sum_divisors_three_primes 3 1 1; norm_num at h; omega

private lemma abundant_1575 : (1575 : ℕ).Abundant := by
  apply abundant_of_two_mul_lt_sum_divisors (by decide)
  have h := sum_divisors_three_primes 2 2 1; norm_num at h; omega

private lemma abundant_2205 : (2205 : ℕ).Abundant := by
  apply abundant_of_two_mul_lt_sum_divisors (by decide)
  have h := sum_divisors_three_primes 2 1 2; norm_num at h; omega

private lemma coprime_315_of_prime_ge_11 {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) :
    Nat.Coprime 315 p := by
  refine (hp.coprime_iff_not_dvd.mpr ?_).symm
  intro hd
  have h357 : p ∣ 3 ∨ p ∣ 5 ∨ p ∣ 7 := by
    have : p ∣ 3 ^ 2 * 5 * 7 := by simpa using hd
    rcases hp.dvd_mul.mp this with h1 | h7
    · rcases hp.dvd_mul.mp h1 with h3 | h5
      · exact Or.inl (hp.dvd_of_dvd_pow h3)
      · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr h7)
  rcases h357 with h | h | h <;> have := Nat.le_of_dvd (by decide) h <;> omega

private lemma abundant_315_mul_prime {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (h103 : p ≤ 103) :
    (315 * p).Abundant := by
  have hcop := coprime_315_of_prime_ge_11 hp h11
  apply abundant_of_two_mul_lt_sum_divisors (by positivity)
  rw [hcop.sum_divisors_mul, sum_divisors_315]
  have hp1 : ∑ d ∈ p.divisors, d = p + 1 := by
    rw [hp.divisors, sum_pair hp.ne_one.symm]; omega
  rw [hp1]
  omega

private lemma pseudo_315_mul_prime_cert {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (s : Finset ℕ)
    (hsub : ∀ d ∈ s, d ∣ 315) (hsum : ∑ d ∈ s, d = 624 - 6 * p) (h103 : p ≤ 103) :
    (315 * p).Pseudoperfect := by
  have hcop := coprime_315_of_prime_ge_11 hp h11
  apply pseudoperfect_of_excess_subset (by positivity) (s := s)
  · intro d hd
    have hdvd := hsub d hd
    exact Nat.mem_properDivisors.mpr
      ⟨dvd_mul_of_dvd_left hdvd p,
       lt_of_le_of_lt (Nat.le_of_dvd (by decide) hdvd) (by nlinarith)⟩
  · rw [hcop.sum_divisors_mul, sum_divisors_315, hsum]
    have hp1 : ∑ d ∈ p.divisors, d = p + 1 := by
      rw [hp.divisors, sum_pair hp.ne_one.symm]; omega
    rw [hp1]
    omega

private lemma pseudo_315_mul_prime {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (h103 : p ≤ 103) :
    (315 * p).Pseudoperfect := by
  have hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37 ∨
      p = 41 ∨ p = 43 ∨ p = 47 ∨ p = 53 ∨ p = 59 ∨ p = 61 ∨ p = 67 ∨ p = 71 ∨ p = 73 ∨
      p = 79 ∨ p = 83 ∨ p = 89 ∨ p = 97 ∨ p = 101 ∨ p = 103 := by
    interval_cases p <;> norm_num at hp <;> tauto
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pseudo_315_mul_prime_cert hp h11 {315, 105, 63, 45, 21, 9} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {315, 105, 63, 45, 15, 3} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {315, 105, 63, 35, 3, 1} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {315, 105, 63, 21, 5, 1} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {315, 105, 63, 3} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {315, 105, 21, 9} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {315, 105, 15, 3} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {315, 63, 21, 3} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {315, 63} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {315, 45, 5, 1} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {315, 21, 5, 1} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {105, 63, 45, 35, 21, 15, 9, 7, 5, 1} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {105, 63, 45, 35, 21, 1} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {105, 63, 45, 35, 9, 1} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {105, 63, 45, 9} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {105, 63, 21, 9} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {105, 63, 15, 3} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {105, 45} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {105, 21} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {63, 21, 5, 1} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl|rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {35, 7} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {15, 3} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl <;> norm_num) (by norm_num) h103
  · exact pseudo_315_mul_prime_cert hp h11 {5, 1} (by intro d hd; simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl|rfl <;> norm_num) (by norm_num) h103

/- Part 5: Reduction Hypotheses and Main Theorem -/

/-- Odd primitive abundant multiples of 45 coprime to 7, with a prime factor in [11, 43]. -/
def H1 : Prop :=
  ∀ m : ℕ, Odd m → m.Abundant → m.primeFactors.card ≤ 5 →
    (∀ d ∈ m.properDivisors, d.Deficient) → 45 ∣ m → ¬ 7 ∣ m →
    (∃ p ∈ m.primeFactors, 11 ≤ p ∧ p ≤ 43) → m.Pseudoperfect

/-- Odd primitive abundant multiples of 63 coprime to 5, with a prime factor in {11, 13, 17, 19}. -/
def H2 : Prop :=
  ∀ m : ℕ, Odd m → m.Abundant → m.primeFactors.card ≤ 5 →
    (∀ d ∈ m.properDivisors, d.Deficient) → 63 ∣ m → ¬ 5 ∣ m →
    (∃ p ∈ m.primeFactors, p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) → m.Pseudoperfect

/-- Odd primitive abundant multiples of 315 with exact 3^2, 5^1, 7^1 and two primes p, q ≥ 107 (p ≤ 199). -/
def H3 : Prop :=
  ∀ m : ℕ, Odd m → m.Abundant → m.primeFactors.card ≤ 5 →
    (∀ d ∈ m.properDivisors, d.Deficient) → 315 ∣ m →
    ¬ 27 ∣ m → ¬ 25 ∣ m → ¬ 49 ∣ m →
    (∀ p ∈ m.primeFactors, p ≠ 3 → p ≠ 5 → p ≠ 7 → 107 ≤ p) →
    (∃ p ∈ m.primeFactors, 107 ≤ p ∧ p ≤ 199) → m.Pseudoperfect

theorem main : H1 → H2 → H3 → OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2.H2 := by
  intro h45 h63 h315 m ho ha hc hprim h9
  by_cases h5 : 5 ∣ m
  · by_cases h7 : 7 ∣ m
    · have h315d : 315 ∣ m := by
        have h45d : 45 ∣ m := (show Nat.Coprime 9 5 by decide).mul_dvd_of_dvd_of_dvd h9 h5
        exact (show Nat.Coprime 45 7 by decide).mul_dvd_of_dvd_of_dvd h45d h7
      by_cases h27 : 27 ∣ m
      · have h945d : 945 ∣ m :=
          (show Nat.Coprime 27 35 by decide).mul_dvd_of_dvd_of_dvd h27
            ((show Nat.Coprime 5 7 by decide).mul_dvd_of_dvd_of_dvd h5 h7)
        by_cases heq : m = 945
        · rw [heq]; exact pseudo_945
        · exact absurd (hprim 945 (Nat.mem_properDivisors.mpr
            ⟨h945d, lt_of_le_of_ne (Nat.le_of_dvd ho.pos h945d) (Ne.symm heq)⟩))
            (not_lt_of_gt abundant_945)
      by_cases h25 : 25 ∣ m
      · have h1575d : 1575 ∣ m :=
          (show Nat.Coprime 25 63 by decide).mul_dvd_of_dvd_of_dvd h25
            ((show Nat.Coprime 9 7 by decide).mul_dvd_of_dvd_of_dvd h9 h7)
        by_cases heq : m = 1575
        · rw [heq]; exact pseudo_1575
        · exact absurd (hprim 1575 (Nat.mem_properDivisors.mpr
            ⟨h1575d, lt_of_le_of_ne (Nat.le_of_dvd ho.pos h1575d) (Ne.symm heq)⟩))
            (not_lt_of_gt abundant_1575)
      by_cases h49 : 49 ∣ m
      · have h2205d : 2205 ∣ m :=
          (show Nat.Coprime 49 45 by decide).mul_dvd_of_dvd_of_dvd h49
            ((show Nat.Coprime 9 5 by decide).mul_dvd_of_dvd_of_dvd h9 h5)
        by_cases heq : m = 2205
        · rw [heq]; exact pseudo_2205
        · exact absurd (hprim 2205 (Nat.mem_properDivisors.mpr
            ⟨h2205d, lt_of_le_of_ne (Nat.le_of_dvd ho.pos h2205d) (Ne.symm heq)⟩))
            (not_lt_of_gt abundant_2205)
      by_cases hsmallp : ∃ p ∈ m.primeFactors, 11 ≤ p ∧ p ≤ 103
      · obtain ⟨p, hp, h11, h103⟩ := hsmallp
        obtain ⟨hprime, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
        have hcop := coprime_315_of_prime_ge_11 hprime h11
        have h315p : 315 * p ∣ m := hcop.mul_dvd_of_dvd_of_dvd h315d hpdvd
        by_cases heq : m = 315 * p
        · rw [heq]; exact pseudo_315_mul_prime hprime h11 h103
        · exact absurd (hprim (315 * p) (Nat.mem_properDivisors.mpr
            ⟨h315p, lt_of_le_of_ne (Nat.le_of_dvd ho.pos h315p) (Ne.symm heq)⟩))
            (not_lt_of_gt (abundant_315_mul_prime hprime h11 h103))
      · push Not at hsmallp
        have hge107 : ∀ p ∈ m.primeFactors, p ≠ 3 → p ≠ 5 → p ≠ 7 → 107 ≤ p := by
          intro p hp hp3 hp5 hp7
          obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
          have h2 : p ≠ 2 := by rintro rfl; exact ho.not_two_dvd_nat hdvd
          have h11 : 11 ≤ p := by by_contra! hl; interval_cases p <;> norm_num at *
          have h104 : 104 ≤ p := by have := hsmallp p hp h11; omega
          by_contra! hl; interval_cases p <;> norm_num at *
        have hle199 : ∃ p ∈ m.primeFactors, 107 ≤ p ∧ p ≤ 199 := by
          by_contra hno
          push Not at hno
          let E : Finset ℕ := {3, 5, 7}
          let c : ℕ → ℚ := fun p =>
            if p = 3 then 13 * 210 / (9 * 211) else if p = 5 then 6 * 210 / (5 * 211) else 8 * 210 / (7 * 211)
          have hsmall : ∀ p ∈ E, 1 ≤ c p := by intro p _; dsimp [c]; split_ifs <;> norm_num
          have h := abundancy_bound ho.pos hc (211 / 210) (by norm_num) E c hsmall (by
            intro p hp
            obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
            by_cases hp3 : p = 3
            · subst p
              have hf := prime_pow_factorization_eq hprime ho.pos.ne'
                (show 3 ^ 2 ∣ m from h9) (show ¬ 3 ^ (2 + 1) ∣ m from h27)
              norm_num [hf, E, c, sum_range_succ, sum_range_zero]
            by_cases hp5 : p = 5
            · subst p
              have hf := prime_pow_factorization_eq hprime ho.pos.ne'
                (show 5 ^ 1 ∣ m by simpa using h5) (show ¬ 5 ^ (1 + 1) ∣ m from h25)
              norm_num [hf, E, c, sum_range_succ, sum_range_zero]
            by_cases hp7 : p = 7
            · subst p
              have hf := prime_pow_factorization_eq hprime ho.pos.ne'
                (show 7 ^ 1 ∣ m by simpa using h7) (show ¬ 7 ^ (1 + 1) ∣ m from h49)
              norm_num [hf, E, c, sum_range_succ, sum_range_zero]
            apply prime_power_sum_le hprime.one_lt
            have hp107 := hge107 p hp hp3 hp5 hp7
            have hp200 : 200 ≤ p := by have := hno p hp hp107; omega
            have hp211 : 211 ≤ p := by by_contra! hl; interval_cases p <;> norm_num at *
            have hp211' : (211 : ℚ) ≤ p := by exact_mod_cast hp211
            simp [E, hp3, hp5, hp7]
            linarith)
          norm_num [E, c] at h
          linarith [Nat.abundant_iff_two_lt_abundancyIndex.mp ha]
        exact h315 m ho ha hc hprim h315d h27 h25 h49 hge107 hle199
    · have h45d : 45 ∣ m := (show Nat.Coprime 9 5 by decide).mul_dvd_of_dvd_of_dvd h9 h5
      exact h45 m ho ha hc hprim h45d h7 (exists_prime_le_43_of_45_not_7 ho ha hc h7)
  · by_cases h7 : 7 ∣ m
    · have h63d : 63 ∣ m := (show Nat.Coprime 9 7 by decide).mul_dvd_of_dvd_of_dvd h9 h7
      exact h63 m ho ha hc hprim h63d h5 (exists_prime_11_19_of_63_not_5 ho ha hc h5)
    · exact case_coprime_35 ho ha hc hprim h9 h5 h7

end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1
