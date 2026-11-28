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
  2. The entire case 315 ∣ m: the base multiples {945, 1575, 2205}, all 23 single-prime
     multiples 315 * p (11 ≤ p ≤ 103), and all infinitely many remaining multiples
     315 * p^a * q^b (107 ≤ p ≤ 199 < q) via a uniform (L = 3, g = 2) central-interval lift
     using the congruence 6 ∣ σ(m) - 2m.
  3. Sharp third-prime bounds for the two remaining cases: 11 ≤ p ≤ 43 when 45 ∣ m, 7 ∤ m (H1),
     and p ∈ {11, 13, 17, 19} when 63 ∣ m, 5 ∤ m (H2).
-/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1

open Finset ArithmeticFunction

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

/- Part 4b: Uniform Central-Interval Lift for 315 * p^a * q^b (107 ≤ p ≤ 199 < q) -/

/- Constructive [3, 306] coverage for 315.properDivisors -/

private lemma insert_step {A : Finset ℕ} {a b d : ℕ} (hd : d ∉ A)
    (hcov : ∀ y, a ≤ y → y ≤ b → ∃ s ⊆ A, ∑ x ∈ s, x = y)
    (hov : a + d ≤ b + 1) :
    ∀ y, a ≤ y → y ≤ b + d → ∃ s ⊆ insert d A, ∑ x ∈ s, x = y := by
  intro y hlo hhi
  by_cases hle : y ≤ b
  · obtain ⟨s, hs, hsum⟩ := hcov y hlo hle
    exact ⟨s, hs.trans (subset_insert d A), hsum⟩
  · obtain ⟨s, hs, hsum⟩ := hcov (y - d) (by omega) (by omega)
    have hdns : d ∉ s := fun h => hd (hs h)
    refine ⟨insert d s, insert_subset_insert d hs, ?_⟩
    rw [sum_insert hdns, hsum]
    omega

private lemma base_1_3_5_7_9 :
    ∀ y, 3 ≤ y → y ≤ 22 → ∃ s ⊆ ({1, 3, 5, 7, 9} : Finset ℕ), ∑ x ∈ s, x = y := by
  intro y hlo hhi
  interval_cases y
  · exact ⟨{3}, by decide, by norm_num⟩
  · exact ⟨{1, 3}, by decide, by norm_num⟩
  · exact ⟨{5}, by decide, by norm_num⟩
  · exact ⟨{1, 5}, by decide, by norm_num⟩
  · exact ⟨{7}, by decide, by norm_num⟩
  · exact ⟨{1, 7}, by decide, by norm_num⟩
  · exact ⟨{9}, by decide, by norm_num⟩
  · exact ⟨{1, 9}, by decide, by norm_num⟩
  · exact ⟨{1, 3, 7}, by decide, by norm_num⟩
  · exact ⟨{3, 9}, by decide, by norm_num⟩
  · exact ⟨{1, 3, 9}, by decide, by norm_num⟩
  · exact ⟨{5, 9}, by decide, by norm_num⟩
  · exact ⟨{1, 5, 9}, by decide, by norm_num⟩
  · exact ⟨{7, 9}, by decide, by norm_num⟩
  · exact ⟨{1, 7, 9}, by decide, by norm_num⟩
  · exact ⟨{1, 3, 5, 9}, by decide, by norm_num⟩
  · exact ⟨{3, 7, 9}, by decide, by norm_num⟩
  · exact ⟨{1, 3, 7, 9}, by decide, by norm_num⟩
  · exact ⟨{5, 7, 9}, by decide, by norm_num⟩
  · exact ⟨{1, 5, 7, 9}, by decide, by norm_num⟩

private lemma cover_315_proper :
    ∀ y, 3 ≤ y → y ≤ 306 → ∃ s ⊆ (315 : ℕ).properDivisors, ∑ x ∈ s, x = y := by
  have h1 := insert_step (d := 15) (by decide) base_1_3_5_7_9 (by omega)
  have h2 := insert_step (d := 21) (by decide) h1 (by omega)
  have h3 := insert_step (d := 35) (by decide) h2 (by omega)
  have h4 := insert_step (d := 45) (by decide) h3 (by omega)
  have h5 := insert_step (d := 63) (by decide) h4 (by omega)
  have h6 := insert_step (d := 105) (by decide) h5 (by omega)
  have hsub : ({105, 63, 45, 35, 21, 15, 1, 3, 5, 7, 9} : Finset ℕ) ⊆ (315 : ℕ).properDivisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact Nat.mem_properDivisors.mpr (by norm_num)
  intro y hlo hhi
  obtain ⟨s, hs, hsum⟩ := h6 y hlo hhi
  exact ⟨s, hs.trans hsub, hsum⟩

private lemma cover_315_all :
    ∀ y, (3 ≤ y ∧ y ≤ 306) ∨ (318 ≤ y ∧ y ≤ 621) →
      ∃ s ⊆ (315 : ℕ).divisors, ∑ x ∈ s, x = y := by
  rintro y (⟨hlo, hhi⟩ | ⟨hlo, hhi⟩)
  · obtain ⟨s, hs, hsum⟩ := cover_315_proper y hlo hhi
    exact ⟨s, hs.trans Nat.properDivisors_subset_divisors, hsum⟩
  · obtain ⟨s, hs, hsum⟩ := cover_315_proper (y - 315) (by omega) (by omega)
    have h315ns : 315 ∉ s := fun h => (Nat.mem_properDivisors.mp (hs h)).2.ne rfl
    refine ⟨insert 315 s, insert_subset (Nat.mem_divisors.mpr ⟨dvd_rfl, by decide⟩)
      (hs.trans Nat.properDivisors_subset_divisors), ?_⟩
    rw [sum_insert h315ns, hsum]; omega

/- Disjoint layer combination lemmas -/

private lemma layer_combine_coprime {b q : ℕ} (hb : 0 < b) (hq : 1 < q) (hcop : Nat.Coprime b q)
    {s1 s2 : Finset ℕ} (h1 : s1 ⊆ b.divisors) (h2 : s2 ⊆ b.properDivisors) :
    ∃ s ⊆ (b * q).properDivisors, ∑ x ∈ s, x = (∑ x ∈ s1, x) + q * ∑ x ∈ s2, x := by
  let emb : ℕ ↪ ℕ := ⟨(q * ·), fun _ _ h => Nat.eq_of_mul_eq_mul_left (by omega) h⟩
  have hdisj : Disjoint s1 (s2.map emb) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨y, _, rfl⟩ := mem_map.mp hx2
    have hxb : q * y ∣ b := (Nat.mem_divisors.mp (h1 hx1)).1
    have hqb : q ∣ b := dvd_trans (dvd_mul_right q y) hxb
    have := Nat.dvd_gcd hqb dvd_rfl
    rw [hcop.gcd_eq_one] at this
    exact absurd (Nat.le_of_dvd (by decide) this) (by omega)
  refine ⟨s1 ∪ s2.map emb, ?_, ?_⟩
  · intro x hx
    rcases mem_union.mp hx with hx1 | hx2
    · obtain ⟨hxb, _⟩ := Nat.mem_divisors.mp (h1 hx1)
      exact Nat.mem_properDivisors.mpr
        ⟨dvd_mul_of_dvd_left hxb q,
         lt_of_le_of_lt (Nat.le_of_dvd hb hxb) (by nlinarith)⟩
    · obtain ⟨y, hy, rfl⟩ := mem_map.mp hx2
      obtain ⟨hyb, hylt⟩ := Nat.mem_properDivisors.mp (h2 hy)
      exact Nat.mem_properDivisors.mpr
        ⟨by rw [mul_comm b q]; exact mul_dvd_mul_left q hyb,
         by rw [mul_comm b q]; exact Nat.mul_lt_mul_of_pos_left hylt (by omega)⟩
  · rw [sum_union hdisj, sum_map]
    change (∑ x ∈ s1, x) + ∑ x ∈ s2, q * x = (∑ x ∈ s1, x) + q * ∑ x ∈ s2, x
    rw [← mul_sum]

private lemma layer_combine_315_pow {b p : ℕ} (hb : 0 < b) (hp : p.Prime) (h11 : 11 ≤ p)
    (h315b : 315 ∣ b) {s1 s2 : Finset ℕ} (h1 : s1 ⊆ (315 : ℕ).divisors) (h2 : s2 ⊆ b.properDivisors) :
    ∃ s ⊆ (b * p).properDivisors, ∑ x ∈ s, x = (∑ x ∈ s1, x) + p * ∑ x ∈ s2, x := by
  let emb : ℕ ↪ ℕ := ⟨(p * ·), fun _ _ h => Nat.eq_of_mul_eq_mul_left hp.pos h⟩
  have hcop := coprime_315_of_prime_ge_11 hp h11
  have hdisj : Disjoint s1 (s2.map emb) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨y, _, rfl⟩ := mem_map.mp hx2
    have hx315 : p * y ∣ 315 := (Nat.mem_divisors.mp (h1 hx1)).1
    have hp315 : p ∣ 315 := dvd_trans (dvd_mul_right p y) hx315
    have := Nat.dvd_gcd hp315 dvd_rfl
    rw [hcop.gcd_eq_one] at this
    exact absurd (Nat.le_of_dvd (by decide) this) (by omega)
  refine ⟨s1 ∪ s2.map emb, ?_, ?_⟩
  · intro x hx
    rcases mem_union.mp hx with hx1 | hx2
    · obtain ⟨hx315, _⟩ := Nat.mem_divisors.mp (h1 hx1)
      have hxb : x ∣ b := dvd_trans hx315 h315b
      exact Nat.mem_properDivisors.mpr
        ⟨dvd_mul_of_dvd_left hxb p,
         lt_of_le_of_lt (Nat.le_of_dvd hb hxb) (by nlinarith [hp.one_lt])⟩
    · obtain ⟨y, hy, rfl⟩ := mem_map.mp hx2
      obtain ⟨hyb, hylt⟩ := Nat.mem_properDivisors.mp (h2 hy)
      exact Nat.mem_properDivisors.mpr
        ⟨by rw [mul_comm b p]; exact mul_dvd_mul_left p hyb,
         by rw [mul_comm b p]; exact Nat.mul_lt_mul_of_pos_left hylt hp.pos⟩
  · rw [sum_union hdisj, sum_map]
    change (∑ x ∈ s1, x) + ∑ x ∈ s2, p * x = (∑ x ∈ s1, x) + p * ∑ x ∈ s2, x
    rw [← mul_sum]

/- Uniform induction: for every k ≥ 0 and 107 ≤ p ≤ 199,
   (315 * p^k).properDivisors covers [3, P(315 * p^k) - 3] -/

private lemma cover_315_mul_p_pow {p : ℕ} (hp : p.Prime) (h107 : 107 ≤ p) (h199 : p ≤ 199) :
    ∀ k : ℕ,
      309 ≤ ∑ d ∈ (315 * p ^ k).properDivisors, d ∧
      ∀ y, 3 ≤ y → y ≤ (∑ d ∈ (315 * p ^ k).properDivisors, d) - 3 →
        ∃ s ⊆ (315 * p ^ k).properDivisors, ∑ x ∈ s, x = y := by
  intro k
  induction k with
  | zero =>
    have hP : ∑ d ∈ (315 * p ^ 0).properDivisors, d = 309 := by
      rw [pow_zero, mul_one]
      have h := sum_properDivisors_add_self (n := 315) (by decide)
      rw [sum_divisors_315] at h
      exact Nat.add_right_cancel (h.trans (by norm_num : 624 = 309 + 315))
    rw [hP]
    refine ⟨by omega, fun y hlo hhi => ?_⟩
    simpa only [pow_zero, mul_one] using cover_315_proper y hlo hhi
  | succ k ih =>
    obtain ⟨hPge, hcov⟩ := ih
    set b := 315 * p ^ k
    have hbpos : 0 < b := by positivity
    have h315b : 315 ∣ b := dvd_mul_right 315 (p ^ k)
    set Pb := ∑ d ∈ b.properDivisors, d
    have hPb_next : ∑ d ∈ (b * p).properDivisors, d = p * Pb + 624 := by
      have hcop : Nat.Coprime 315 (p ^ k) := (coprime_315_of_prime_ge_11 hp (by omega)).pow_right k
      have hcop1 : Nat.Coprime 315 (p ^ (k + 1)) := (coprime_315_of_prime_ge_11 hp (by omega)).pow_right (k + 1)
      have hs1 : ∑ d ∈ (b * p).divisors, d = 624 * ∑ j ∈ range (k + 2), p ^ j := by
        rw [show b * p = 315 * p ^ (k + 1) by simp [b, pow_succ, mul_assoc],
          hcop1.sum_divisors_mul, sum_divisors_315, Nat.divisors_prime_pow hp, sum_map]
        simp only [Function.Embedding.coeFn_mk]
      have hs0 : ∑ d ∈ b.divisors, d = 624 * ∑ j ∈ range (k + 1), p ^ j := by
        rw [show b = 315 * p ^ k from rfl,
          hcop.sum_divisors_mul, sum_divisors_315, Nat.divisors_prime_pow hp, sum_map]
        simp only [Function.Embedding.coeFn_mk]
      have hgeom : ∑ j ∈ range (k + 2), p ^ j = 1 + p * ∑ j ∈ range (k + 1), p ^ j := by
        rw [Finset.sum_range_succ', pow_zero, add_comm]
        congr 1
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [pow_succ']
      have hdiv0 := sum_properDivisors_add_self hbpos
      have hdiv1 := sum_properDivisors_add_self (n := b * p) (by positivity)
      rw [hgeom] at hs1
      have : ∑ d ∈ (b * p).divisors, d = 624 + p * ∑ d ∈ b.divisors, d := by
        rw [hs1, hs0]; ring
      change Pb + b = ∑ d ∈ b.divisors, d at hdiv0
      nlinarith
    have hmul : 315 * p ^ (k + 1) = b * p := by simp [b, pow_succ, mul_assoc]
    rw [hmul, hPb_next]
    refine ⟨by nlinarith, ?_⟩
    -- Helper to combine x ∈ [3,306] ∪ [318,621] with j ∈ {0,1} ∪ [3,Pb-3] ∪ {Pb-1,Pb}
    have mk : ∀ x j, ((3 ≤ x ∧ x ≤ 306) ∨ (318 ≤ x ∧ x ≤ 621)) →
        (j = 0 ∨ j = 1 ∨ (3 ≤ j ∧ j ≤ Pb - 3) ∨ j = Pb - 1 ∨ j = Pb) →
        ∃ s ⊆ (b * p).properDivisors, ∑ z ∈ s, z = x + p * j := by
      intro x j hx hj
      obtain ⟨s1, hs1, hsum1⟩ := cover_315_all x hx
      have hs2_ex : ∃ s2 ⊆ b.properDivisors, ∑ z ∈ s2, z = j := by
        rcases hj with rfl | rfl | ⟨jlo, jhi⟩ | rfl | rfl
        · exact ⟨∅, empty_subset _, by simp⟩
        · exact ⟨{1}, singleton_subset_iff.mpr (Nat.mem_properDivisors.mpr ⟨one_dvd _, by
            have : 1 < 315 := by decide
            exact lt_of_lt_of_le this (Nat.le_of_dvd hbpos h315b)⟩), by simp⟩
        · exact hcov j jlo jhi
        · refine ⟨b.properDivisors.erase 1, erase_subset _ _, ?_⟩
          have h1mem : 1 ∈ b.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd _, by
            have : 1 < 315 := by decide
            exact lt_of_lt_of_le this (Nat.le_of_dvd hbpos h315b)⟩
          have := Finset.add_sum_erase b.properDivisors id h1mem
          simp only [id_eq] at this; change 1 + ∑ x ∈ b.properDivisors.erase 1, x = Pb at this
          omega
        · exact ⟨b.properDivisors, Subset.rfl, rfl⟩
      obtain ⟨s2, hs2, hsum2⟩ := hs2_ex
      obtain ⟨s, hs, hsum⟩ := layer_combine_315_pow hbpos hp (by omega) h315b hs1 hs2
      exact ⟨s, hs, by rw [hsum, hsum1, hsum2]⟩
    have hP4 : p * (Pb - 3) = p * (Pb - 4) + p := by
      have : Pb - 3 = (Pb - 4) + 1 := by omega
      rw [this, mul_add, mul_one]
    have hP1 : p * (Pb - 1) = p * (Pb - 3) + 2 * p := by
      have : Pb - 1 = (Pb - 3) + 2 := by omega
      rw [this, mul_add, mul_comm p 2]
    have hP0 : p * Pb = p * (Pb - 1) + p := by
      calc p * Pb = p * ((Pb - 1) + 1) := by congr 1; omega
        _ = p * (Pb - 1) + p := by ring
    intro y hlo hhi
    by_cases h1 : y ≤ 306
    · simpa using mk y 0 (Or.inl ⟨hlo, h1⟩) (Or.inl rfl)
    by_cases h2 : y ≤ p + 306
    · obtain ⟨s, hs, hsum⟩ := mk (y - p) 1 (Or.inl ⟨by omega, by omega⟩) (Or.inr (Or.inl rfl))
      exact ⟨s, hs, by omega⟩
    by_cases h3 : y ≤ 621
    · simpa using mk y 0 (Or.inr ⟨by omega, h3⟩) (Or.inl rfl)
    by_cases h4 : y ≤ p * (Pb - 3) + 2
    · set j := (y - 3) / p
      have hj3 : 3 ≤ j := (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)
      have hjhi : j ≤ Pb - 3 := by
        have hlt : y - 3 < (Pb - 3) * p := by rw [mul_comm]; omega
        have := (Nat.div_lt_iff_lt_mul hp.pos).mpr hlt
        omega
      have hmul_le : p * j ≤ y - 3 := by
        rw [mul_comm]; exact Nat.div_mul_le_self (y - 3) p
      have hmul_gt : y - 3 < p * j + p := by
        have h := Nat.lt_div_mul_add (a := y - 3) hp.pos
        change y - 3 < j * p + p at h
        rw [mul_comm] at h; exact h
      obtain ⟨s, hs, hsum⟩ := mk (y - p * j) j (Or.inl ⟨by omega, by omega⟩)
        (Or.inr (Or.inr (Or.inl ⟨hj3, hjhi⟩)))
      exact ⟨s, hs, by omega⟩
    by_cases h5 : y ≤ p * (Pb - 3) + 306
    · obtain ⟨s, hs, hsum⟩ := mk (y - p * (Pb - 3)) (Pb - 3) (Or.inl ⟨by omega, by omega⟩)
        (Or.inr (Or.inr (Or.inl ⟨by omega, le_rfl⟩)))
      exact ⟨s, hs, by omega⟩
    by_cases h6 : y ≤ p * (Pb - 3) + 621
    · by_cases h6a : y ≤ p * (Pb - 3) + 317
      · obtain ⟨s, hs, hsum⟩ := mk (y - p * (Pb - 4)) (Pb - 4) (Or.inr ⟨by omega, by omega⟩)
          (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
        exact ⟨s, hs, by omega⟩
      · obtain ⟨s, hs, hsum⟩ := mk (y - p * (Pb - 3)) (Pb - 3) (Or.inr ⟨by omega, by omega⟩)
          (Or.inr (Or.inr (Or.inl ⟨by omega, le_rfl⟩)))
        exact ⟨s, hs, by omega⟩
    by_cases h7 : y ≤ p * (Pb - 1) + 306
    · obtain ⟨s, hs, hsum⟩ := mk (y - p * (Pb - 1)) (Pb - 1) (Or.inl ⟨by omega, by omega⟩)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      exact ⟨s, hs, by omega⟩
    by_cases h8 : y ≤ p * Pb + 306
    · obtain ⟨s, hs, hsum⟩ := mk (y - p * Pb) Pb (Or.inl ⟨by omega, by omega⟩)
        (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      exact ⟨s, hs, by omega⟩
    by_cases h9 : y ≤ p * Pb + 317
    · obtain ⟨s, hs, hsum⟩ := mk (y - p * (Pb - 1)) (Pb - 1) (Or.inr ⟨by omega, by omega⟩)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      exact ⟨s, hs, by omega⟩
    · obtain ⟨s, hs, hsum⟩ := mk (y - p * Pb) Pb (Or.inr ⟨by omega, by omega⟩)
        (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      exact ⟨s, hs, by omega⟩

/- Final prime-power lift with L = 3, g = 2 (adapted from OddWeirdFinalPrime / OddWeirdRepeatedFinal). -/

private lemma final_prime_alternatives {P D q L g E : ℤ}
    (hg : 1 ≤ g) (hL : 1 ≤ L) (hD : 2 ≤ D) (hq : 3 ≤ q)
    (big : (2 * g + 1) * (2 * L + 8 * g + 8) ≤ P)
    (excess : E = 2 * P - D * (q - 1)) (low : L ≤ E) :
    (g * q ≤ P - 2 * L + 1 ∧ D + 2 * L - 1 ≤ q * P) ∨
    (q ≤ P - 2 * L + 1 ∧ D + 2 * L - 1 ≤ q ∧ E ≤ 2 * P + D + q - L) ∨
    (L ≤ E ∧ E ≤ P - L) := by
  have gL : 0 ≤ g * L := mul_nonneg (by omega) (by omega)
  have gg : 0 ≤ g * g := mul_self_nonneg g
  have g1L : 0 ≤ (g - 1) * L := mul_nonneg (by omega) (by omega)
  have pbound : 5 * L ≤ P := by nlinarith only [big, hg, hL, gg, g1L]
  have dpos : 0 ≤ D := by omega
  have dlt : D < P := by nlinarith only [excess, low, hL, mul_nonneg (show 0 ≤ q - 3 by omega) dpos]
  by_cases small : g * q ≤ P - 2 * L + 1
  · left
    refine ⟨small, ?_⟩
    have t := mul_le_mul_of_nonneg_right hq (show 0 ≤ P by omega)
    nlinarith only [t, dlt, pbound, hL]
  · have dcap : D < 8 * g := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_left h (show 0 ≤ q - 1 by omega)
      have w := mul_nonneg (show 0 ≤ g by omega) (show 0 ≤ q - 2 by omega)
      nlinarith only [small, k, w, excess, low, pbound, hL]
    have bigq : 2 * L + 8 * g + 8 < q := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_left h (show 0 ≤ g by omega)
      nlinarith only [k, small, big, gg, gL, hg]
    by_cases overlap : q ≤ P - 2 * L + 1
    · right; left
      have h := mul_nonneg dpos (show 0 ≤ q - 1 by omega)
      exact ⟨overlap, by omega, by linarith only [excess, h, hD, bigq, hg, hL]⟩
    · right; right
      have k := mul_le_mul_of_nonneg_left hD (show 0 ≤ q - 1 by omega)
      exact ⟨low, by nlinarith only [k, excess, overlap, pbound]⟩

private lemma four_interval_join {P D q L A : ℤ} (w : q ≤ P - 2 * L + 1) (v : D + 2 * L - 1 ≤ q)
    (lo : L ≤ A) (hi : A ≤ 2 * P + D + q - L) :
    (L ≤ A ∧ A ≤ P - L) ∨ (L ≤ A - q ∧ A - q ≤ P - L) ∨
    (L ≤ A - (P + D) ∧ A - (P + D) ≤ P - L) ∨
    (L ≤ A - (P + D + q) ∧ A - (P + D + q) ≤ P - L) := by omega

private lemma repeated_bounds {P D q L : ℤ} (hD : 0 < D) (hq : 3 ≤ q)
    (large : 6 * L ≤ P) (low : D * (q - 2) < 2 * P) (high : 2 * P < D * (q - 1))
    (divone : ¬ D ∣ 2 * P) :
    3 ≤ D ∧ q ≤ P - 2 * L + 1 := by
  have three : 3 ≤ D := by
    by_contra! bad
    interval_cases D <;> simp at divone
  refine ⟨three, ?_⟩
  have a := mul_le_mul_of_nonneg_right three (show 0 ≤ q - 2 by omega)
  omega

private lemma nondivisor_between {P D q : ℤ} (hD : 0 < D)
    (low : D * (q - 2) < 2 * P) (high : 2 * P < D * (q - 1)) : ¬ D ∣ 2 * P := by
  rintro ⟨x, h⟩
  rw [h] at low high
  have a := (mul_lt_mul_iff_right₀ hD).mp low
  have b := (mul_lt_mul_iff_right₀ hD).mp high
  omega

private lemma repeated_alternatives {P D q L g E : ℤ} (hg : 1 ≤ g) (hL : 1 ≤ L)
    (hD : 0 < D) (hq : 3 ≤ q) (big : (2 * g + 1) * (2 * L + 8 * g + 8) ≤ P)
    (low : D * (q - 2) < 2 * P) (high : 2 * P < D * (q - 1)) (excess : E ≤ 2 * P + D - q) :
    (g * q ≤ P - 2 * L + 1 ∧ D + 2 * L - 1 ≤ q * P ∧ E ≤ 2 * P + D + q * P - L) ∨
    (q ≤ P - 2 * L + 1 ∧ D + 2 * L - 1 ≤ q ∧ E ≤ 2 * P + D + q - L) := by
  have gL := mul_nonneg (show 0 ≤ g - 1 by omega) (show 0 ≤ L by omega)
  have gg := mul_self_nonneg g
  have pl : 6 * L ≤ P := by nlinarith only [big, hg, gL, gg]
  have pd : D < 2 * P := by nlinarith only [low, mul_nonneg (show 0 ≤ D by omega) (show 0 ≤ q - 3 by omega)]
  obtain ⟨_, qw⟩ := repeated_bounds hD hq pl low high (nondivisor_between hD low high)
  by_cases small : g * q ≤ P - 2 * L + 1
  · left
    have covers := mul_le_mul_of_nonneg_right hq (show 0 ≤ P by omega)
    exact ⟨small, by omega, by omega⟩
  · right
    have largeQ : 2 * L + 8 * g + 8 < q := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_left h (show 0 ≤ g by omega)
      nlinarith only [k, small, big, gg, gL, hg, hL]
    have dcap : D < 8 * g := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_right h (show 0 ≤ q - 2 by omega)
      have w := mul_nonneg (show 0 ≤ g by omega) (show 0 ≤ q - 4 by omega)
      nlinarith only [k, low, small, pl, hL, w]
    exact ⟨qw, by omega, by omega⟩

private lemma repeat_from_excess {P D q : ℤ} (hq : 0 < q - 1) (hs : 0 < 2 * P + D)
    (E : ℕ → ℤ) (base : E 0 = -D)
    (next : ∀ j, E (j + 1) = q * E j + (2 * P + D))
    (j : ℕ) (firstDef : E 1 < 0) (previousDef : E j < 0) (abundant : 0 < E (j + 1)) :
    D * (q - 2) < 2 * P ∧ 2 * P < D * (q - 1) ∧ E (j + 1) ≤ 2 * P + D - q := by
  have closed (t : ℕ) : (q - 1) * E t = q ^ t * (2 * P - D * (q - 2)) - (2 * P + D) := by
    induction t with
    | zero => rw [base, pow_zero]; ring
    | succ t ih =>
      rw [next, pow_succ]
      calc _ = q * ((q - 1) * E t) + (q - 1) * (2 * P + D) := by ring
        _ = _ := by rw [ih]; ring
  have c := closed (j + 1)
  have prodPos := mul_pos hq abundant
  have pos : 0 < 2 * P - D * (q - 2) := by
    by_contra! h
    have x := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (show 0 ≤ q by omega) (j + 1)) h
    omega
  have one := next 0
  rw [base] at one
  have qNonneg : 0 ≤ q := by omega
  have neg := mul_le_mul_of_nonneg_left (show E j ≤ -1 by omega) qNonneg
  refine ⟨by omega, ?_, ?_⟩
  · nlinarith only [firstDef, one]
  · rw [next]; linarith only [neg]

private lemma index_for_translate {A : Set ℤ} {T L H g r x : ℤ}
    (hr : 0 < r) (wide : r * g ≤ H - L + 1) (last : T ∈ A)
    (gap : ∀ k : ℤ, 0 ≤ k → k < T → ∃ i ∈ A, k - g < i ∧ i ≤ k)
    (lo : L ≤ x) (hi : x ≤ H + r * T) :
    ∃ i ∈ A, L ≤ x - r * i ∧ x - r * i ≤ H := by
  by_cases finished : L + r * T ≤ x
  · exact ⟨T, last, by omega, by omega⟩
  let k := (x - L) / r
  have kp : k < T := Int.ediv_lt_of_lt_mul hr (by rw [mul_comm T r]; omega)
  obtain ⟨i, mem, lower, upper⟩ := gap k (Int.ediv_nonneg (by omega) (by omega)) kp
  have decomp := Int.emod_add_mul_ediv (x - L) r
  change (x - L) % r + r * k = x - L at decomp
  have remLo := Int.emod_nonneg (x - L) (by omega : r ≠ 0)
  have remHi := Int.emod_lt_of_pos (x - L) hr
  have left := mul_le_mul_of_nonneg_left upper (le_of_lt hr)
  have right := mul_le_mul_of_nonneg_left (show k - g + 1 ≤ i by omega) (le_of_lt hr)
  rw [mul_add, mul_sub, mul_one] at right
  exact ⟨i, mem, by omega, by omega⟩

private lemma middle_next {A B C : Set ℤ} {T P b L g r : ℤ}
    (hr : 0 < r) (wide : r * g ≤ P - 2 * L + 1) (overlap : b + 2 * L ≤ P + r * T + 1)
    (endA : T ∈ A) (gap : ∀ k : ℤ, 0 ≤ k → k < T → ∃ i ∈ A, k - g < i ∧ i ≤ k)
    (central : ∀ y : ℤ, L ≤ y → y ≤ P - L → y ∈ B)
    (layers : ∀ i ∈ A, ∀ y ∈ B, y + r * i ∈ C ∧ b + y + r * i ∈ C) :
    ∀ x : ℤ, L ≤ x → x ≤ b + P + r * T - L → x ∈ C := by
  intro x low high
  by_cases first : x ≤ P - L + r * T
  · obtain ⟨i, hi, h, k⟩ := index_for_translate hr (show r * g ≤ (P - L) - L + 1 by omega) endA gap low first
    have represented := (layers i hi _ (central _ h k)).1
    convert represented using 1
    ring
  · obtain ⟨i, hi, h, k⟩ := index_for_translate (x := x - b) hr (show r * g ≤ (P - L) - L + 1 by omega) endA gap
      (show L ≤ x - b by omega) (show x - b ≤ (P - L) + r * T by omega)
    have represented := (layers i hi _ (central _ h k)).2
    convert represented using 1
    ring

private lemma pseudoperfect_of_excess_int {m : ℕ} (pos : 0 < m) {s : Finset ℕ}
    (subset : s ⊆ m.properDivisors)
    (sum : (∑ d ∈ s, (d : ℤ)) = (sigma 1 m : ℤ) - 2 * (m : ℤ)) : m.Pseudoperfect := by
  classical
  have total : (sigma 1 m : ℤ) = (∑ d ∈ m.properDivisors, (d : ℤ)) + m := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    simp
  have rest := sum_sdiff subset (f := fun x : ℕ => (x : ℤ))
  refine ⟨pos, m.properDivisors \ s, sdiff_subset, Int.ofNat_inj.mp ?_⟩
  push_cast
  linarith only [sum, total, rest]

private lemma certified_prime_power_3_2 {b q j : ℕ} (bpos : 1 < b) (hq : q.Prime)
    (coprime : b.Coprime q) (q3 : 3 ≤ q)
    (primitive : ∀ d ∈ (b * q ^ (j + 1)).properDivisors, d.Deficient)
    (high : 3 ≤ (sigma 1 (b * q ^ (j + 1)) : ℤ) - 2 * (b * q ^ (j + 1) : ℕ)) :
    let P := ∑ d ∈ b.properDivisors, (d : ℤ)
    let R := fun x : ℤ => ∃ s ⊆ b.properDivisors, (∑ d ∈ s, (d : ℤ)) = x
    150 ≤ P → (j = 0 → 2 ≤ (b : ℤ) - P) →
    (∀ y : ℤ, 3 ≤ y → y ≤ P - 3 → R y) →
    (∀ k : ℤ, 0 ≤ k → k < P → ∃ i : ℤ, R i ∧ k - 2 < i ∧ i ≤ k) →
    (b * q ^ (j + 1)).Pseudoperfect := by
  classical
  let represented (n : ℕ) (x : ℤ) : Prop :=
    ∃ s : Finset ℕ, s ⊆ n.properDivisors ∧ (∑ d ∈ s, (d : ℤ)) = x
  let properTotal (n : ℕ) : ℤ := ∑ d ∈ n.properDivisors, (d : ℤ)
  let excess (n : ℕ) : ℤ := (sigma 1 n : ℕ) - 2 * (n : ℤ)
  have combine {b m q : ℕ} (hm : 0 < m) (bm : b ∣ m) (hn : ¬ q ∣ b)
      (hq : 1 < q) {s t : Finset ℕ} (hs : s ⊆ b.divisors) (ht : t ⊆ m.properDivisors) :
      represented (q * m) ((∑ d ∈ s, (d : ℤ)) + q * ∑ d ∈ t, (d : ℤ)) := by
    let f (x : ℕ) := q * x
    have positive : 0 < q := by omega
    have inj : Function.Injective f := fun x y eq => Nat.eq_of_mul_eq_mul_left positive eq
    have subset : s ⊆ (q * m).properDivisors := by
      intro x hx
      have d := Nat.dvd_of_mem_divisors (hs hx)
      have dm := d.trans bm
      refine Nat.mem_properDivisors.mpr ⟨dm.trans (dvd_mul_left _ _), ?_⟩
      exact lt_of_le_of_lt (Nat.le_of_dvd hm dm) (by simpa using Nat.mul_lt_mul_of_pos_right hq hm)
    have scaled : t.image f ⊆ (q * m).properDivisors := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      obtain ⟨div, lt⟩ := Nat.mem_properDivisors.mp (ht hz)
      exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_left q div, Nat.mul_lt_mul_of_pos_left lt positive⟩
    have separate : Disjoint s (t.image f) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx'
      exact hn ((dvd_mul_right q z).trans (Nat.dvd_of_mem_divisors (hs hx)))
    refine ⟨s ∪ t.image f, Finset.union_subset subset scaled, ?_⟩
    rw [sum_union separate, sum_image (fun x _ y _ eq => inj eq), Finset.mul_sum]
    simp [f]
  have layers {b m q : ℕ} (hm : 0 < m) (bm : b ∣ m) (hn : ¬ q ∣ b)
      (hq : 1 < q) {i y : ℤ} (hi : represented m i) (hy : represented b y) :
      represented (q * m) (y + q * i) ∧ represented (q * m) (b + y + q * i) := by
    obtain ⟨s, hs, rfl⟩ := hy
    obtain ⟨t, ht, rfl⟩ := hi
    have hb : b ≠ 0 := by
      intro z; subst b; exact hm.ne' (by simpa using bm)
    have full : insert b s ⊆ b.divisors := by
      rw [← Nat.insert_self_properDivisors hb]
      exact Finset.insert_subset_insert _ hs
    constructor
    · exact combine hm bm hn hq (hs.trans Nat.properDivisors_subset_divisors) ht
    · have nb : b ∉ s := fun h => Nat.self_notMem_properDivisors (hs h)
      simpa [sum_insert nb] using combine hm bm hn hq full ht
  have sigma_split (n : ℕ) : (sigma 1 n : ℤ) = properTotal n + n := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    simp [properTotal]
  have excess_step {b q : ℕ} (prime : q.Prime) (cop : b.Coprime q) (j : ℕ) :
      excess (b * q ^ (j + 1)) = q * excess (b * q ^ j) + (sigma 1 b : ℕ) := by
    have recurEq : sigma 1 (b * q ^ (j + 1)) = q * sigma 1 (b * q ^ j) + sigma 1 b := by
      rw [isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right (j + 1)),
          isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right j),
          sigma_one_apply_prime_pow prime, sigma_one_apply_prime_pow prime, geom_sum_succ]
      ring
    dsimp [excess]
    rw [recurEq]
    push_cast
    ring
  intro P R large simple middle gap
  change 150 ≤ properTotal b at large
  change 3 ≤ excess (b * q ^ (j + 1)) at high
  have total : represented b (properTotal b) := ⟨_, fun _ h => h, rfl⟩
  have zero : represented b 0 := ⟨∅, by simp, by simp⟩
  have unit : represented b 1 := ⟨{1}, by simpa using Nat.one_mem_properDivisors_iff_one_lt.mpr bpos, by simp⟩
  have bpos0 : 0 < b := by omega
  have qpos : 0 < q := hq.pos
  have hq3 : (3 : ℤ) ≤ q := by exact_mod_cast q3
  have can : represented (b * q ^ (j + 1)) (excess (b * q ^ (j + 1))) := by
    by_cases hzero : j = 0
    · subst j
      simp only [zero_add, pow_one] at high ⊢
      let P0 := properTotal b
      let D : ℤ := b - P0
      let E := excess (b * q)
      have formula : E = 2 * P0 - D * (q - 1) := by
        have first := excess_step hq coprime 0
        simp only [pow_zero, pow_one, mul_one, zero_add] at first
        dsimp only [E, P0, D]
        rw [first]; unfold excess; rw [sigma_split b]; ring
      have cases' := final_prime_alternatives (g := 2) (L := 3) (by decide) (by decide)
        (simple rfl) hq3 (by change 5 * 30 ≤ P0; omega) formula high
      have translate (i y : ℤ) (hi : represented b i) (hy : represented b y) :
          represented (b * q) (y + q * i) ∧ represented (b * q) (b + y + q * i) := by
        simpa only [mul_comm q b] using
          layers bpos0 (dvd_refl _) (hq.coprime_iff_not_dvd.mp coprime.symm) hq.one_lt hi hy
      rcases cases' with ⟨wide, join⟩ | ⟨wide, join, cap⟩ | basic
      · have qP := mul_le_mul_of_nonneg_right hq3 (show 0 ≤ P0 by omega)
        have hD2 : 2 ≤ D := simple rfl
        have prod := mul_nonneg (show 0 ≤ D by linarith)
          (show 0 ≤ (q : ℤ) - 1 by omega)
        have hjoin : (b : ℤ) + 2 * 3 ≤ P0 + (q : ℤ) * P0 + 1 := by
          have hDdef : D = (b : ℤ) - P0 := rfl
          linarith [join, hDdef]
        have hcap : E ≤ (b : ℤ) + P0 + (q : ℤ) * P0 - 3 := by
          have hb_ge : (0 : ℤ) ≤ (b : ℤ) := by omega
          linarith [formula, prod, qP, large, hb_ge]
        exact middle_next (A := fun i => represented b i) (B := fun y => represented b y)
          (C := fun z => represented (b * q) z) (P := P0) (T := P0) (b := (b : ℤ))
          (by omega : (0 : ℤ) < q) (by simpa only [mul_comm (q : ℤ) 2] using wide)
          hjoin total gap middle (fun i hi y hy => translate i y hi hy)
          _ high hcap
      · have eq : P0 + D = (b : ℤ) := by dsimp [D]; ring
        rcases four_interval_join wide join high cap with h | h | h | h
        · simpa using (translate 0 _ zero (middle _ h.1 h.2)).1
        · simpa using (translate 1 _ unit (middle _ h.1 h.2)).1
        · rw [eq] at h
          simpa using (translate 0 _ zero (middle _ h.1 h.2)).2
        · rw [eq] at h
          convert (translate 1 _ unit (middle _ h.1 h.2)).2 using 1
          ring
      · simpa using (translate 0 _ zero (middle _ basic.1 basic.2)).1
    · have earlier (k : ℕ) (hk : k < j + 1) : properTotal (b * q ^ k) < (b * q ^ k : ℕ) := by
        have mem : b * q ^ k ∈ (b * q ^ (j + 1)).properDivisors := Nat.mem_properDivisors.mpr
          ⟨Nat.mul_dvd_mul_left b (pow_dvd_pow q hk.le),
           Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hq.one_lt hk) (by omega)⟩
        have defic := primitive _ mem
        change ∑ d ∈ (b * q ^ k).properDivisors, d < b * q ^ k at defic
        dsimp only [properTotal]
        rw [← Nat.cast_sum]
        exact_mod_cast defic
      have exc_neg (k : ℕ) (hk : k < j + 1) : excess (b * q ^ k) < 0 := by
        have hlt := earlier k hk
        dsimp only [excess]
        rw [sigma_split]
        omega
      let P0 := properTotal b
      let D : ℤ := b - P0
      let E (t : ℕ) := excess (b * q ^ t)
      have sig : (sigma 1 b : ℤ) = 2 * P0 + D := by rw [sigma_split]; dsimp [P0, D]; ring
      have sPos : 0 < 2 * P0 + D := by rw [← sig]; exact_mod_cast (sigma_pos_iff.mpr bpos0 : 0 < sigma 1 b)
      have dPos : 0 < D := by have := earlier 0 (by omega); simp only [pow_zero, mul_one] at this; dsimp [D, P0]; omega
      have recurEq (t : ℕ) : E (t + 1) = (q : ℤ) * E t + (2 * P0 + D) := by rw [← sig]; exact excess_step hq coprime t
      have e0 : E 0 = -D := by simp only [E, pow_zero, mul_one, excess, sig]; dsimp [D]; ring
      have one : E 1 < 0 := by simpa [E] using exc_neg 1 (by omega)
      have prevDef : E j < 0 := by simpa [E] using exc_neg j (by omega)
      obtain ⟨l, h, e⟩ := repeat_from_excess (q := (q : ℤ)) (by omega) sPos
        E e0 recurEq j one prevDef (lt_of_lt_of_le (by omega : (0 : ℤ) < 3) high)
      have alt := repeated_alternatives (P := P0) (D := D) (E := E (j + 1)) (g := 2) (L := 3)
        (by decide) (by decide) dPos hq3 (by change 5 * 30 ≤ P0; omega) l h e
      have translate (i y : ℤ) (hi : represented b i) (hy : represented b y) :
          represented (b * q ^ (j + 1)) (y + q * i) ∧ represented (b * q ^ (j + 1)) (b + y + q * i) := by
        have divis : b ∣ b * q ^ j := dvd_mul_right _ _
        have pos : 0 < b * q ^ j := by positivity
        obtain ⟨t, sub, ht⟩ := hi
        have inclusion : represented (b * q ^ j) i := by
          refine ⟨t, fun d hd => ?_, ht⟩
          obtain ⟨dvd, lt⟩ := Nat.mem_properDivisors.mp (sub hd)
          exact Nat.mem_properDivisors.mpr ⟨dvd.trans divis, lt_of_lt_of_le lt (Nat.le_of_dvd pos divis)⟩
        have holds := layers pos divis (hq.coprime_iff_not_dvd.mp coprime.symm) hq.one_lt inclusion hy
        convert holds using 2 <;> ring
      rcases alt with ⟨wide, join, cap⟩ | ⟨wide, join, cap⟩
      · exact middle_next (A := fun i => represented b i) (B := fun y => represented b y)
          (C := fun z => represented (b * q ^ (j + 1)) z) (P := P0) (T := P0) (b := (b : ℤ))
          (by omega : (0 : ℤ) < q) (by simpa only [mul_comm (q : ℤ) 2] using wide)
          (by change (b : ℤ) - P0 + 2 * 3 - 1 ≤ q * P0 at join; omega)
          total gap middle (fun i hi y hy => translate i y hi hy)
          _ high (by dsimp only [E, P0, D] at cap ⊢; omega)
      · have bEq : P0 + D = (b : ℤ) := by dsimp [D]; ring
        rcases four_interval_join wide join high cap with h | h | h | h
        · simpa using (translate 0 _ zero (middle _ h.1 h.2)).1
        · simpa using (translate 1 _ unit (middle _ h.1 h.2)).1
        · rw [bEq] at h
          simpa using (translate 0 _ zero (middle _ h.1 h.2)).2
        · rw [bEq] at h
          convert (translate 1 _ unit (middle _ h.1 h.2)).2 using 1
          ring
  obtain ⟨s, hs, hsum⟩ := can
  exact pseudoperfect_of_excess_int (by positivity) hs hsum

private lemma deficient_315_mul_p_pow {p a : ℕ} (hp : p.Prime) (h107 : 107 ≤ p) :
    sigma 1 (315 * p ^ a) < 2 * (315 * p ^ a) := by
  have hcop : Nat.Coprime 315 (p ^ a) := (coprime_315_of_prime_ge_11 hp (by omega)).pow_right a
  have hsig : sigma 1 (315 * p ^ a) = 624 * ∑ j ∈ range (a + 1), p ^ j := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, ArithmeticFunction.sigma_one_apply,
      sum_divisors_315, sigma_one_apply_prime_pow hp]
  have hgeom : (p - 1) * ∑ j ∈ range (a + 1), p ^ j = p ^ (a + 1) - 1 := by
    have hz : ((p : ℤ) - 1) * ∑ j ∈ range (a + 1), (p : ℤ) ^ j = (p : ℤ) ^ (a + 1) - 1 := by
      rw [mul_comm]; exact geom_sum_mul (p : ℤ) (a + 1)
    have h1 : 1 ≤ p := hp.one_lt.le
    have h2 : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ hp.pos
    zify [h1, h2]
    exact hz
  have hlt1 : (p - 1) * ∑ j ∈ range (a + 1), p ^ j < p * p ^ a := by
    rw [hgeom, pow_succ']
    have : 0 < p * p ^ a := by positivity
    omega
  have hmul : (p - 1) * sigma 1 (315 * p ^ a) < (p - 1) * (2 * (315 * p ^ a)) := by
    rw [hsig]
    have h1 : (p - 1) * (624 * ∑ j ∈ range (a + 1), p ^ j) < 624 * (p * p ^ a) := by
      have : (p - 1) * (624 * ∑ j ∈ range (a + 1), p ^ j) = 624 * ((p - 1) * ∑ j ∈ range (a + 1), p ^ j) := by ring
      rw [this]
      exact Nat.mul_lt_mul_of_pos_left hlt1 (by decide)
    have h2 : 624 * (p * p ^ a) ≤ (p - 1) * (2 * (315 * p ^ a)) := by
      have : 624 * p ≤ (p - 1) * 630 := by omega
      calc 624 * (p * p ^ a) = (624 * p) * p ^ a := by ring
        _ ≤ ((p - 1) * 630) * p ^ a := Nat.mul_le_mul_right _ this
        _ = (p - 1) * (2 * (315 * p ^ a)) := by ring
    exact lt_of_lt_of_le h1 h2
  exact Nat.lt_of_mul_lt_mul_left hmul

/- Complete uniform proof of Branch H3:
   every odd primitive abundant multiple of 315 with 3^2 || m, 5 || m, 7 || m,
   all other primes ≥ 107, and some prime in [107, 199], is pseudoperfect. -/

private lemma case_315_two_large_primes {m : ℕ} (ho : Odd m) (ha : m.Abundant)
    (hc : m.primeFactors.card ≤ 5)
    (hprim : ∀ d ∈ m.properDivisors, d.Deficient)
    (h315 : 315 ∣ m) (h27 : ¬ 27 ∣ m) (h25 : ¬ 25 ∣ m) (h49 : ¬ 49 ∣ m)
    (hge107 : ∀ r ∈ m.primeFactors, r ≠ 3 → r ≠ 5 → r ≠ 7 → 107 ≤ r)
    (hle199 : ∃ p ∈ m.primeFactors, 107 ≤ p ∧ p ≤ 199) :
    m.Pseudoperfect := by
  have hmpos : 0 < m := ho.pos
  have hmne : m ≠ 0 := hmpos.ne'
  obtain ⟨p, hp_mem, hp107, hp199⟩ := hle199
  obtain ⟨hp_prime, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp_mem
  have h3mem : 3 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, dvd_trans (by decide : 3 ∣ 315) h315, hmne⟩
  have h5mem : 5 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, dvd_trans (by decide : 5 ∣ 315) h315, hmne⟩
  have h7mem : 7 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, dvd_trans (by decide : 7 ∣ 315) h315, hmne⟩
  have hf3 : m.factorization 3 = 2 :=
    prime_pow_factorization_eq (by decide) hmne (dvd_trans (by decide : 3 ^ 2 ∣ 315) h315) h27
  have hf5 : m.factorization 5 = 1 :=
    prime_pow_factorization_eq (by decide) hmne (dvd_trans (by decide : 5 ^ 1 ∣ 315) h315) h25
  have hf7 : m.factorization 7 = 1 :=
    prime_pow_factorization_eq (by decide) hmne (dvd_trans (by decide : 7 ^ 1 ∣ 315) h315) h49
  have hexq : ∃ q ∈ m.primeFactors, q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ p := by
    by_contra hno
    push Not at hno
    have hpf_eq : m.primeFactors = {3, 5, 7, p} := by
      ext r
      simp only [mem_insert, mem_singleton]
      constructor
      · intro hr
        by_contra hnot
        push Not at hnot
        exact hnot.2.2.2 (hno r hr hnot.1 hnot.2.1 hnot.2.2.1)
      · rintro (rfl | rfl | rfl | rfl) <;> assumption
    have hm_eq : m = 315 * p ^ (m.factorization p) := by
      have hprod := Nat.prod_factorization_pow_eq_self hmne
      rw [Finsupp.prod, Nat.support_factorization, hpf_eq] at hprod
      rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
          Finset.prod_insert (by simp; omega), Finset.prod_singleton] at hprod
      rw [hf3, hf5, hf7] at hprod
      linarith
    have hdef := deficient_315_mul_p_pow (a := m.factorization p) hp_prime hp107
    rw [← hm_eq, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self] at hdef
    have hab : m < ∑ d ∈ m.properDivisors, d := ha
    omega
  obtain ⟨q, hq_mem, hq3, hq5, hq7, hqp⟩ := hexq
  obtain ⟨hq_prime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq_mem
  have hq107 : 107 ≤ q := hge107 q hq_mem hq3 hq5 hq7
  have hsub5 : ({3, 5, 7, p, q} : Finset ℕ) ⊆ m.primeFactors := by
    intro r hr
    simp only [mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hcard5 : ({3, 5, 7, p, q} : Finset ℕ).card = 5 := by
    rw [card_insert_of_notMem (by simp; omega), card_insert_of_notMem (by simp; omega),
        card_insert_of_notMem (by simp; omega), card_insert_of_notMem (by simp; omega),
        card_singleton]
  have hpf_eq : m.primeFactors = {3, 5, 7, p, q} :=
    (Finset.eq_of_subset_of_card_le hsub5 (by omega)).symm
  set a := m.factorization p
  set c := m.factorization q
  have hcpos : 1 ≤ c := by
    have : q ^ 1 ∣ m := by simpa using hqdvd
    exact (hq_prime.pow_dvd_iff_le_factorization hmne).mp this
  set j := c - 1
  have hcj : c = j + 1 := by omega
  set b := 315 * p ^ a
  have hm_eq : m = b * q ^ (j + 1) := by
    have hprod := Nat.prod_factorization_pow_eq_self hmne
    rw [Finsupp.prod, Nat.support_factorization, hpf_eq] at hprod
    rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
        Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
        Finset.prod_singleton] at hprod
    rw [hf3, hf5, hf7] at hprod
    change 3 ^ 2 * (5 ^ 1 * (7 ^ 1 * (p ^ a * q ^ c))) = m at hprod
    rw [hcj] at hprod
    dsimp [b]
    linarith
  have hcop_bq : b.Coprime q := by
    have h1 : Nat.Coprime 315 q := coprime_315_of_prime_ge_11 hq_prime (by omega)
    have h2 : Nat.Coprime (p ^ a) q :=
      ((Nat.coprime_primes hp_prime hq_prime).mpr (Ne.symm hqp)).pow_left a
    exact h1.mul_left h2
  have hbpos : 1 < b := by
    have : 1 ≤ p ^ a := Nat.one_le_pow _ _ hp_prime.pos
    dsimp [b]; omega
  -- 6 divides the excess of m, so excess m ≥ 6 ≥ 3
  have hhigh : 3 ≤ (sigma 1 (b * q ^ (j + 1)) : ℤ) - 2 * (b * q ^ (j + 1) : ℕ) := by
    have hcop315 : Nat.Coprime 315 (p ^ a * q ^ (j + 1)) :=
      ((coprime_315_of_prime_ge_11 hp_prime (by omega)).pow_right a).mul_right
        ((coprime_315_of_prime_ge_11 hq_prime (by omega)).pow_right (j + 1))
    have hsig_dvd : 6 ∣ sigma 1 m := by
      have : m = 315 * (p ^ a * q ^ (j + 1)) := by rw [hm_eq]; dsimp [b]; ring
      rw [this, isMultiplicative_sigma.map_mul_of_coprime hcop315,
          ArithmeticFunction.sigma_one_apply, sum_divisors_315]
      exact dvd_mul_of_dvd_left (by decide : 6 ∣ 624) _
    have h2m_dvd : 6 ∣ 2 * m := by
      have h3m : 3 ∣ m := dvd_trans (by decide : 3 ∣ 315) h315
      obtain ⟨t, ht⟩ := h3m
      exact ⟨t, by omega⟩
    have hab_sig : 2 * m < sigma 1 m := by
      rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
      have hab : m < ∑ d ∈ m.properDivisors, d := ha
      omega
    have h6_diff : 6 ∣ sigma 1 m - 2 * m := Nat.dvd_sub hsig_dvd h2m_dvd
    have hge6 : 6 ≤ sigma 1 m - 2 * m := Nat.le_of_dvd (by omega) h6_diff
    rw [← hm_eq]
    omega
  -- 6 divides the deficiency of b, so b - P(b) ≥ 6 ≥ 2
  have hsimple : j = 0 → 2 ≤ (b : ℤ) - ∑ d ∈ b.properDivisors, (d : ℤ) := by
    intro _
    have hdef : sigma 1 b < 2 * b := deficient_315_mul_p_pow hp_prime hp107
    have hcop315 : Nat.Coprime 315 (p ^ a) := (coprime_315_of_prime_ge_11 hp_prime (by omega)).pow_right a
    have hsig_dvd : 6 ∣ sigma 1 b := by
      dsimp [b]
      rw [isMultiplicative_sigma.map_mul_of_coprime hcop315,
          ArithmeticFunction.sigma_one_apply, sum_divisors_315]
      exact dvd_mul_of_dvd_left (by decide : 6 ∣ 624) _
    have h2b_dvd : 6 ∣ 2 * b := ⟨105 * p ^ a, by dsimp [b]; ring⟩
    have h6_diff : 6 ∣ 2 * b - sigma 1 b := Nat.dvd_sub h2b_dvd hsig_dvd
    have hge6 : 6 ≤ 2 * b - sigma 1 b := Nat.le_of_dvd (by omega) h6_diff
    have hsplit : sigma 1 b = (∑ d ∈ b.properDivisors, d) + b := by
      rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    have hcast : (∑ d ∈ b.properDivisors, (d : ℤ)) = ((∑ d ∈ b.properDivisors, d : ℕ) : ℤ) := by
      push_cast; rfl
    rw [hcast]
    omega
  obtain ⟨hP309, hcov⟩ := cover_315_mul_p_pow hp_prime hp107 hp199 a
  change 309 ≤ ∑ d ∈ b.properDivisors, d at hP309
  change ∀ y, 3 ≤ y → y ≤ (∑ d ∈ b.properDivisors, d) - 3 →
      ∃ s ⊆ b.properDivisors, ∑ x ∈ s, x = y at hcov
  have hcastP : (∑ d ∈ b.properDivisors, (d : ℤ)) = ((∑ d ∈ b.properDivisors, d : ℕ) : ℤ) := by
    push_cast; rfl
  have hmiddle : ∀ y : ℤ, 3 ≤ y → y ≤ (∑ d ∈ b.properDivisors, (d : ℤ)) - 3 →
      ∃ s ⊆ b.properDivisors, (∑ d ∈ s, (d : ℤ)) = y := by
    intro y hlo hhi
    rw [hcastP] at hhi
    obtain ⟨s, hs, hsum⟩ := hcov y.toNat (by omega) (by omega)
    refine ⟨s, hs, ?_⟩
    have : (∑ d ∈ s, (d : ℤ)) = ((∑ d ∈ s, d : ℕ) : ℤ) := by push_cast; rfl
    rw [this, hsum]; omega
  have hgap : ∀ k : ℤ, 0 ≤ k → k < ∑ d ∈ b.properDivisors, (d : ℤ) →
      ∃ i : ℤ, (∃ s ⊆ b.properDivisors, (∑ d ∈ s, (d : ℤ)) = i) ∧ k - 2 < i ∧ i ≤ k := by
    intro k hklo hkhi
    set Pz := ∑ d ∈ b.properDivisors, (d : ℤ)
    by_cases hk0 : k = 0
    · exact ⟨0, ⟨∅, empty_subset _, by simp⟩, by omega, by omega⟩
    by_cases hk2 : k ≤ 2
    · refine ⟨1, ⟨{1}, singleton_subset_iff.mpr (Nat.one_mem_properDivisors_iff_one_lt.mpr hbpos), by simp⟩,
        by omega, by omega⟩
    by_cases hkm : k ≤ Pz - 3
    · exact ⟨k, hmiddle k (by omega) hkm, by omega, le_rfl⟩
    by_cases hkP2 : k = Pz - 2
    · exact ⟨Pz - 3, hmiddle (Pz - 3) (by rw [hcastP]; omega) (by omega), by omega, by omega⟩
    · -- k = Pz - 1
      have h1mem : 1 ∈ b.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr hbpos
      refine ⟨Pz - 1, ⟨b.properDivisors.erase 1, erase_subset _ _, ?_⟩, by omega, by omega⟩
      have := Finset.add_sum_erase b.properDivisors (fun x : ℕ => (x : ℤ)) h1mem
      change (1 : ℤ) + ∑ x ∈ b.properDivisors.erase 1, (x : ℤ) = Pz at this
      omega
  rw [hm_eq]
  exact certified_prime_power_3_2 hbpos hq_prime hcop_bq (by omega)
    (by rw [← hm_eq]; exact hprim) hhigh
    (by rw [hcastP]; omega) hsimple hmiddle hgap

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

theorem main : H1 → H2 → OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2.H2 := by
  intro h45 h63 m ho ha hc hprim h9
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
        exact case_315_two_large_primes ho ha hc hprim h315d h27 h25 h49 hge107 hle199
    · have h45d : 45 ∣ m := (show Nat.Coprime 9 5 by decide).mul_dvd_of_dvd_of_dvd h9 h5
      exact h45 m ho ha hc hprim h45d h7 (exists_prime_le_43_of_45_not_7 ho ha hc h7)
  · by_cases h7 : 7 ∣ m
    · have h63d : 63 ∣ m := (show Nat.Coprime 9 7 by decide).mul_dvd_of_dvd_of_dvd h9 h7
      exact h63 m ho ha hc hprim h63d h5 (exists_prime_11_19_of_63_not_5 ho ha hc h5)
    · exact case_coprime_35 ho ha hc hprim h9 h5 h7

end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1
