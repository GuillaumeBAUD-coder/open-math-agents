import OMAStatements.S_oeis_a367175
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto

/-!
The signed divisor sum is sigma(n) minus twice the sum of the distinct prime divisors.
For a positive integer with at least three prime factors counted with multiplicity,
sigma(n) is greater than four times that prime sum. Divisibility is then impossible.
The remaining prime and semiprime cases give exactly the seven stated integers.
Source: Peter Luschny's conjecture in https://oeis.org/A367175.
-/

namespace A367175Proof

def divisorSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

def primeSum (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, p

end A367175Proof

namespace A367175Proof

lemma divisorSum_prime {p : ℕ} (hp : Nat.Prime p) : divisorSum p = p + 1 := by
  simpa [divisorSum, Finset.sum_range_succ, Nat.add_comm] using
    (Nat.sum_divisors_prime_pow (k := 1) (f := fun x : ℕ => x) hp)

lemma divisorSum_pow {p : ℕ} (hp : Nat.Prime p) (k : ℕ) :
    divisorSum (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
  exact Nat.sum_divisors_prime_pow hp

lemma divisorSum_mul {m n : ℕ} (h : Nat.Coprime m n) :
    divisorSum (m * n) = divisorSum m * divisorSum n := h.sum_divisors_mul

lemma primeSum_prime {p : ℕ} (hp : Nat.Prime p) : primeSum p = p := by
  simp [primeSum, hp.primeFactors]

lemma primeSum_pow {p : ℕ} (hp : Nat.Prime p) {k : ℕ} (hk : k ≠ 0) :
    primeSum (p ^ k) = p := by
  simp [primeSum, Nat.primeFactors_prime_pow hk hp]

lemma primeSum_mul {m n : ℕ} (h : Nat.Coprime m n) :
    primeSum (m * n) = primeSum m + primeSum n := by
  simp only [primeSum, h.primeFactors_mul, Finset.sum_union h.disjoint_primeFactors]

lemma primeSum_pos {n : ℕ} (hn : 1 < n) : 0 < primeSum n := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn
  apply Finset.sum_pos'
  · intro q hq
    exact Nat.zero_le _
  · exact ⟨p, hp, Nat.pos_of_mem_primeFactors hp⟩

lemma divisorSum_mono {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) :
    divisorSum m ≤ divisorSum n :=
  Finset.sum_le_sum_of_subset (Nat.divisors_subset_of_dvd hn h)

lemma large_mul_prime {n p : ℕ} (hn : 1 < n) (hp : Nat.Prime p)
    (hbig : 4 * primeSum n < divisorSum n) :
    4 * primeSum (p * n) < divisorSum (p * n) := by
  have hn0 : n ≠ 0 := by omega
  by_cases hpn : p ∣ n
  · have hP : primeSum (p * n) = primeSum n := by
      simp only [primeSum, Nat.primeFactors_mul hp.ne_zero hn0, hp.primeFactors]
      rw [Finset.singleton_union, Finset.insert_eq_of_mem (hp.mem_primeFactors hpn hn0)]
    rw [hP]
    exact hbig.trans_le (divisorSum_mono (mul_ne_zero hp.ne_zero hn0) (dvd_mul_left n p))
  · have hcop : Nat.Coprime p n := hp.coprime_iff_not_dvd.mpr hpn
    have hmem : p ∉ n.primeFactors := fun h => hpn (Nat.dvd_of_mem_primeFactors h)
    have hP : primeSum (p * n) = p + primeSum n := by
      simp [primeSum, Nat.primeFactors_mul hp.ne_zero hn0, hp.primeFactors,
        Finset.sum_insert, hmem]
    rw [hP, divisorSum_mul hcop, divisorSum_prime hp]
    have hpos := primeSum_pos hn
    have h1 : 4 * p ≤ p * (4 * primeSum n) := by
      nlinarith [Nat.mul_le_mul_left p (show 4 ≤ 4 * primeSum n by omega)]
    nlinarith [Nat.mul_le_mul_left (p + 1) (Nat.succ_le_of_lt hbig)]

lemma triple_product_bound {p q r : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r) :
    4 * (p + q + r) < (p + 1) * (q + 1) * (r + 1) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hq
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hr
  nlinarith [Nat.zero_le (a * b), Nat.zero_le (a * c), Nat.zero_le (b * c),
    Nat.zero_le (a * b * c)]

lemma square_product_bound {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    4 * (p + q) < (1 + p + p ^ 2) * (q + 1) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hq
  nlinarith [Nat.zero_le (a * b), Nat.zero_le (a ^ 2 * b)]

lemma large_cube {p : ℕ} (hp : Nat.Prime p) :
    4 * primeSum (p * p * p) < divisorSum (p * p * p) := by
  have heq : p * p * p = p ^ 3 := by ring
  rw [heq, primeSum_pow hp (by decide : 3 ≠ 0), divisorSum_pow hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.pow_zero, pow_one]
  have h2 : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
  have h3 : 4 * p ≤ p ^ 3 := by nlinarith [Nat.mul_le_mul_left p h2]
  omega

lemma large_square_mul {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    4 * primeSum (p * p * q) < divisorSum (p * p * q) := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hP : primeSum (p * p * q) = p + q := by
    rw [← pow_two, primeSum_mul (hc.pow_left 2), primeSum_pow hp (by decide : 2 ≠ 0),
      primeSum_prime hq]
  rw [hP, ← pow_two, divisorSum_mul (hc.pow_left 2), divisorSum_pow hp,
    divisorSum_prime hq]
  simpa [Finset.sum_range_succ, Nat.add_assoc] using square_product_bound hp.two_le hq.two_le

lemma large_three {p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) :
    4 * primeSum (p * q * r) < divisorSum (p * q * r) := by
  by_cases hpq : p = q
  · subst q
    by_cases hpr : p = r
    · subst r
      exact large_cube hp
    · exact large_square_mul hp hr hpr
  by_cases hpr : p = r
  · subst r
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using large_square_mul hp hq hpq
  by_cases hqr : q = r
  · subst r
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      large_square_mul hq hp (Ne.symm hpq)
  have hpqc : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hprc : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpr
  have hqrc : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
  have hP : primeSum (p * q * r) = p + q + r := by
    rw [primeSum_mul (hprc.mul_left hqrc), primeSum_mul hpqc,
      primeSum_prime hp, primeSum_prime hq, primeSum_prime hr]
  rw [hP, divisorSum_mul (hprc.mul_left hqrc), divisorSum_mul hpqc,
    divisorSum_prime hp, divisorSum_prime hq, divisorSum_prime hr]
  exact triple_product_bound hp.two_le hq.two_le hr.two_le

lemma large_mul_list (l : List ℕ) (hl : ∀ p ∈ l, Nat.Prime p) (n : ℕ)
    (hn : 1 < n) (hbig : 4 * primeSum n < divisorSum n) :
    4 * primeSum (n * l.prod) < divisorSum (n * l.prod) := by
  induction l generalizing n with
  | nil => simpa using hbig
  | cons p l ih =>
    have hp := hl p (by simp)
    have hln : ∀ q ∈ l, Nat.Prime q := fun q hq => hl q (by simp [hq])
    have hpn : 1 < p * n := by
      have := Nat.mul_le_mul hp.two_le (Nat.succ_le_of_lt hn)
      omega
    have hb := large_mul_prime hn hp hbig
    simpa [List.prod_cons, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      ih hln (p * n) hpn hb

lemma large_list (l : List ℕ) (hl : ∀ p ∈ l, Nat.Prime p) (hlen : 3 ≤ l.length) :
    4 * primeSum l.prod < divisorSum l.prod := by
  cases l with
  | nil => simp at hlen
  | cons p l =>
    cases l with
    | nil => simp at hlen
    | cons q l =>
      cases l with
      | nil => simp at hlen
      | cons r l =>
        have hp := hl p (by simp)
        have hq := hl q (by simp)
        have hr := hl r (by simp)
        have hrest : ∀ t ∈ l, Nat.Prime t := fun t ht => hl t (by simp [ht])
        have hpos : 1 < p * q * r := by
          have := Nat.mul_le_mul (Nat.mul_le_mul hp.two_le hq.two_le) hr.two_le
          omega
        simpa [List.prod_cons, Nat.mul_assoc] using
          large_mul_list l hrest (p * q * r) hpos (large_three hp hq hr)

theorem large_omega (n : ℕ) (hn : 0 < n) (hΩ : 3 ≤ n.primeFactorsList.length) :
    4 * primeSum n < divisorSum n := by
  have h := large_list n.primeFactorsList
    (fun p hp => Nat.prime_of_mem_primeFactorsList hp) hΩ
  simpa [Nat.prod_primeFactorsList hn.ne'] using h

lemma small_list (l : List ℕ) (hl : ∀ p ∈ l, Nat.Prime p) (hlen : l.length ≤ 2) :
    l.prod = 1 ∨ Nat.Prime l.prod ∨
      ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ l.prod = p * q := by
  cases l with
  | nil => simp
  | cons p l =>
    have hp := hl p (by simp)
    cases l with
    | nil => exact Or.inr (Or.inl (by simpa using hp))
    | cons q l =>
      have hq := hl q (by simp)
      cases l with
      | nil => exact Or.inr (Or.inr ⟨p, q, hp, hq, by simp⟩)
      | cons r l => simp at hlen

theorem small_omega (n : ℕ) (hn : 0 < n) (hΩ : n.primeFactorsList.length ≤ 2) :
    n = 1 ∨ Nat.Prime n ∨ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p * q := by
  have h := small_list n.primeFactorsList
    (fun p hp => Nat.prime_of_mem_primeFactorsList hp) hΩ
  simpa [Nat.prod_primeFactorsList hn.ne'] using h

end A367175Proof

namespace A367175Proof

theorem dvd_sub_twice_iff (s t : ℤ) :
    s - 2 * t ∣ s ↔ s - 2 * t ∣ 2 * t := by
  constructor
  · intro h
    have hh := dvd_sub h (dvd_refl (s - 2 * t))
    rwa [show s - (s - 2 * t) = 2 * t by ring] at hh
  · intro h
    have hh := dvd_add (dvd_refl (s - 2 * t)) h
    rwa [show s - 2 * t + 2 * t = s by ring] at hh

theorem no_large_divisibility (s t : ℕ) (ht : 0 < t) (hs : 4 * t < s) :
    ¬ ((s : ℤ) - 2 * t ∣ (s : ℤ)) := by
  intro h
  have hd := (dvd_sub_twice_iff (s : ℤ) (t : ℤ)).mp h
  obtain ⟨k, hk⟩ := hd
  have htZ : (0 : ℤ) < t := by exact_mod_cast ht
  have hsZ : 4 * (t : ℤ) < s := by exact_mod_cast hs
  have ha : (0 : ℤ) < (s : ℤ) - 2 * t := by omega
  have hkpos : 0 < k := by
    by_contra hn
    have hmul := mul_nonpos_of_nonneg_of_nonpos ha.le (show k ≤ 0 by omega)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ k by omega) ha.le
  nlinarith

theorem prime_divisibility {p : ℕ} (hp : Nat.Prime p)
    (h : (p : ℤ) + 1 - 2 * p ∣ (p : ℤ) + 1) : p = 2 ∨ p = 3 := by
  have hd : (p : ℤ) + 1 - 2 * p ∣ 2 := by
    have hh := dvd_add h (dvd_refl ((p : ℤ) + 1 - 2 * p))
    rwa [show (p : ℤ) + 1 + ((p : ℤ) + 1 - 2 * p) = 2 by ring] at hh
  have he : (p : ℤ) + 1 - 2 * p = -((p : ℤ) - 1) := by ring
  rw [he, neg_dvd] at hd
  have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  rw [← hcast] at hd
  have hdN : p - 1 ∣ 2 := by exact_mod_cast hd
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdN
  have hp2 := hp.two_le
  omega

theorem square_divisibility_false {p : ℕ} (hp : Nat.Prime p) :
    ¬ ((p : ℤ) ^ 2 + p + 1 - 2 * p ∣ (p : ℤ) ^ 2 + p + 1) := by
  intro h
  by_cases he : p = 2
  · subst p
    norm_num at h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hs : 4 * p < p ^ 2 + p + 1 := by
    have hm := Nat.mul_le_mul_right p hp3
    nlinarith
  have hh := no_large_divisibility (p ^ 2 + p + 1) p hp.pos hs
  apply hh
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h

theorem semiprime_cases {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p < q) (h : (p - 1) * (q - 1) ∣ 2 * (p + q)) :
    (p = 2 ∧ (q = 3 ∨ q = 7)) ∨ (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 7) := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hep : p - 1 + 1 = p := by omega
  have heq : q - 1 + 1 = q := by omega
  have hb := Nat.le_of_dvd (show 0 < 2 * (p + q) by omega) h
  have hp6 : p ≤ 6 := by
    by_contra hh
    have hm := Nat.mul_le_mul_right (q - 1) (show 6 ≤ p - 1 by omega)
    nlinarith
  have hpc : p = 2 ∨ p = 3 ∨ p = 5 := by
    interval_cases p <;> norm_num at hp <;> norm_num
  rcases hpc with rfl | rfl | rfl
  · simp only [Nat.reduceSub, one_mul] at h
    have hd0 : q - 1 ∣ 2 * (q - 1) := ⟨2, by omega⟩
    have hd := Nat.dvd_sub h hd0
    have he : 2 * (2 + q) - 2 * (q - 1) = 6 := by omega
    rw [he] at hd
    have hq7 : q ≤ 7 := by have := Nat.le_of_dvd (by decide : 0 < 6) hd; omega
    interval_cases q <;> norm_num at hq <;> norm_num at hd <;> norm_num
  · simp only [Nat.reduceSub] at h
    have hd0 : q - 1 ∣ q + 3 := by
      obtain ⟨k, hk⟩ := h
      refine ⟨k, ?_⟩
      nlinarith
    have hd := Nat.dvd_sub hd0 (dvd_refl (q - 1))
    have he : q + 3 - (q - 1) = 4 := by omega
    rw [he] at hd
    have hq5 : q ≤ 5 := by have := Nat.le_of_dvd (by decide : 0 < 4) hd; omega
    interval_cases q <;> norm_num at hq <;> norm_num
  · have hq7 : q ≤ 7 := by norm_num at hb; omega
    interval_cases q <;> norm_num at hq <;> norm_num

end A367175Proof

namespace A367175Proof

theorem a_eq (n : ℕ) : OMA.S_oeis_a367175.a n =
    (divisorSum n : ℤ) - 2 * primeSum n := by
  classical
  have hf : n.divisors.filter Nat.Prime = n.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primeFactors]
    tauto
  unfold OMA.S_oeis_a367175.a divisorSum primeSum
  simp only [Nat.cast_sum]
  calc
    (∑ d ∈ n.divisors, if Nat.Prime d then -(d : ℤ) else (d : ℤ)) =
        ∑ d ∈ n.divisors, ((d : ℤ) - 2 * (if Nat.Prime d then (d : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hp : Nat.Prime d <;> simp [hp] <;> ring
    _ = (∑ d ∈ n.divisors, (d : ℤ)) -
        2 * ∑ d ∈ n.divisors, if Nat.Prime d then (d : ℤ) else 0 := by
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by rw [← Finset.sum_filter, hf]

theorem semiprime_divisibility_int {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p < q)
    (h : ((p : ℤ) + 1) * ((q : ℤ) + 1) - 2 * ((p : ℤ) + q) ∣
      ((p : ℤ) + 1) * ((q : ℤ) + 1)) :
    p * q = 6 ∨ p * q = 14 ∨ p * q = 15 ∨ p * q = 35 := by
  have hd := (dvd_sub_twice_iff (((p : ℤ) + 1) * ((q : ℤ) + 1)) ((p : ℤ) + q)).mp h
  have he : ((p : ℤ) + 1) * ((q : ℤ) + 1) - 2 * ((p : ℤ) + q) =
      (((p - 1) * (q - 1) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_sub hq.one_lt.le]
    norm_num
    ring
  rw [he] at hd
  have hdN : (p - 1) * (q - 1) ∣ 2 * (p + q) := by exact_mod_cast hd
  rcases semiprime_cases hp hq hpq hdN with ⟨rfl, hq⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hq with rfl | rfl <;> norm_num
  · norm_num
  · norm_num

theorem excluded_large (n : ℕ) (hn : 1 < n)
    (hlarge : 4 * primeSum n < divisorSum n) :
    ¬ (OMA.S_oeis_a367175.a n ∣ (divisorSum n : ℤ)) := by
  rw [a_eq]
  exact no_large_divisibility _ _ (primeSum_pos hn) hlarge

end A367175Proof

namespace A367175Proof

lemma divisorSum_square {p : ℕ} (hp : Nat.Prime p) :
    divisorSum (p * p) = p ^ 2 + p + 1 := by
  rw [← pow_two, divisorSum_pow hp]
  simp [Finset.sum_range_succ]
  ring

lemma prime_product_result {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p < q)
    (h : OMA.S_oeis_a367175.a (p * q) ∣ (divisorSum (p * q) : ℤ)) :
    p * q = 6 ∨ p * q = 14 ∨ p * q = 15 ∨ p * q = 35 := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (Nat.ne_of_lt hpq)
  apply semiprime_divisibility_int hp hq hpq
  simpa only [a_eq, divisorSum_mul hc, primeSum_mul hc, divisorSum_prime hp,
    divisorSum_prime hq, primeSum_prime hp, primeSum_prime hq,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h

theorem classification (n : ℕ) (hn : 0 < n)
    (h : OMA.S_oeis_a367175.a n ∣ (divisorSum n : ℤ)) :
    n ∈ ({1, 2, 3, 6, 14, 15, 35} : Finset ℕ) := by
  by_cases h1 : n = 1
  · subst n
    decide
  have hn1 : 1 < n := by omega
  have hsmall : n.primeFactorsList.length ≤ 2 := by
    by_contra hh
    exact excluded_large n hn1 (large_omega n hn (by omega)) h
  rcases small_omega n hn hsmall with hnEq | hp | ⟨p, q, hp, hq, rfl⟩
  · exact False.elim (h1 hnEq)
  · have hd : (n : ℤ) + 1 - 2 * n ∣ (n : ℤ) + 1 := by
      simpa only [a_eq, divisorSum_prime hp, primeSum_prime hp,
        Nat.cast_add, Nat.cast_one] using h
    rcases prime_divisibility hp hd with rfl | rfl <;> decide
  · by_cases hpq : p = q
    · subst q
      have hh : (p : ℤ) ^ 2 + p + 1 - 2 * p ∣ (p : ℤ) ^ 2 + p + 1 := by
        have hP : primeSum (p * p) = p := by
          rw [← pow_two, primeSum_pow hp (by decide : 2 ≠ 0)]
        simpa only [a_eq, divisorSum_square hp, hP, Nat.cast_add,
          Nat.cast_pow, Nat.cast_one] using h
      exact False.elim (square_divisibility_false hp hh)
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · rcases prime_product_result hp hq hlt h with h6 | h14 | h15 | h35 <;>
        simp_all
    · have hh : OMA.S_oeis_a367175.a (q * p) ∣ (divisorSum (q * p) : ℤ) := by
        simpa only [Nat.mul_comm] using h
      have hc := prime_product_result hq hp hgt hh
      rw [Nat.mul_comm q p] at hc
      rcases hc with h6 | h14 | h15 | h35 <;> simp_all

theorem listed_values (n : ℕ) (h : n ∈ ({1, 2, 3, 6, 14, 15, 35} : Finset ℕ)) :
    OMA.S_oeis_a367175.a n ∣ (divisorSum n : ℤ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem solution (n : ℕ) (hn : 0 < n) :
    OMA.S_oeis_a367175.a n ∣ (divisorSum n : ℤ) ↔
      n ∈ ({1, 2, 3, 6, 14, 15, 35} : Finset ℕ) :=
  ⟨classification n hn, listed_values n⟩

end A367175Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a367175.main := by
  intro n hn
  exact A367175Proof.solution n hn
