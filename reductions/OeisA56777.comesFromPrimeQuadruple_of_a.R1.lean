import FormalConjectures.OEIS.«56777»
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
# Reduction of OEIS A056777 to two constrained factorization cases

The target is the converse of the prime-quadruple construction in Conjecture 1.1 of
[Choudhury and Wei](https://arxiv.org/abs/2606.10331). Their Theorem 2.2 handles the
case where both endpoints are squarefree semiprimes. The small-excess
classification also appears in [previous Lean work](https://github.com/Kuberwastaken/c5-k4).

The reduction proves the converse whenever both endpoints are squarefree.
For every remaining counterexample, each endpoint has at least three prime factors
counted with multiplicity and at least one odd prime of odd exponent. Each such odd prime
contributes a factor of two to the divisor sum, so at least one endpoint has at most two.
The two obligations distinguish which endpoint has the small number of odd exponents.
-/

namespace OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R1

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777Closure

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  simpa using sigma_one_apply_prime_pow (i := 1) hp

private theorem le_sigma (n : ℕ) (hn : 1 < n) : n + 1 ≤ σ 1 n := by
  rw [sigma_one_apply]
  calc
    n + 1 = ∑ d ∈ ({n, 1} : Finset ℕ), d := by simp [show n ≠ 1 by omega]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> exact Nat.mem_divisors.mpr ⟨by simp, by omega⟩) (by omega)

private theorem lt_sigma_of_not_prime (n : ℕ) (hn : 1 < n) (hp : ¬n.Prime) :
    n + 2 < σ 1 n := by
  obtain ⟨p, hprime, hdiv⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hne : p ≠ n := fun h => hp (h ▸ hprime)
  have hp1 := hprime.one_lt
  have : n + p + 1 ≤ σ 1 n := by
    rw [sigma_one_apply]
    calc
      n + p + 1 = ∑ d ∈ ({n, p, 1} : Finset ℕ), d := by
        simp [show n ≠ 1 by omega, show n ≠ p by omega, hprime.ne_one, add_assoc]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;>
              exact Nat.mem_divisors.mpr ⟨by first | exact hdiv | simp, by omega⟩) (by omega)
  omega

/-- The excess of the sum of the divisor sum and the totient for a prime power. -/
private theorem prime_pow_excess (p k : ℕ) (hp : p.Prime) :
    σ 1 (p ^ (k + 2)) + (p ^ (k + 2)).totient =
      2 * p ^ (k + 2) + ∑ j ∈ Finset.range (k + 1), p ^ j := by
  rw [sigma_one_apply_prime_pow hp, totient_prime_pow_succ hp,
    Finset.sum_range_succ, Finset.sum_range_succ, pow_succ p (k + 1)]
  have h : p - 1 + 1 = p := by have := hp.one_lt; omega
  have hh := congrArg (fun x : ℕ => p ^ (k + 1) * x) h
  simp only [Nat.mul_add, mul_one] at hh
  omega

/-- The divisor sum and totient together are at least twice the argument. -/
private theorem le_sigma_add_totient (n : ℕ) : 2 * n ≤ σ 1 n + n.totient := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p k hp hk =>
    rcases k with _ | _ | k
    · omega
    · rw [show 0 + 1 = 1 by rfl, pow_one]
      rw [sigma_prime hp, totient_prime hp]
      have := hp.one_lt
      omega
    · change 2 * p ^ (k + 2) ≤ σ 1 (p ^ (k + 2)) + (p ^ (k + 2)).totient
      rw [prime_pow_excess p k hp]
      omega
  | coprime a b ha hb hc iha ihb =>
    have hsa := le_sigma a ha
    have hsb := le_sigma b hb
    have hta := Nat.totient_lt a ha
    have htb := Nat.totient_lt b hb
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc]
    have hprod := Nat.mul_le_mul iha ihb
    have hdiff := mul_nonneg
      (show 0 ≤ (σ 1 a : ℤ) - a.totient by omega)
      (show 0 ≤ (σ 1 b : ℤ) - b.totient by omega)
    zify at hprod ⊢
    nlinarith

/-- A positive integer has excess two precisely when it is a product of distinct primes. -/
theorem excess_two_iff (n : ℕ) :
    σ 1 n + n.totient = 2 * n + 2 ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q := by
  constructor
  · intro h
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp at h
    | one => simp at h
    | prime_pow p k hp hk =>
      rcases k with _ | _ | _ | k
      · omega
      · rw [show 0 + 1 = 1 by rfl, pow_one] at h
        rw [sigma_prime hp, totient_prime hp] at h
        have := hp.one_lt
        omega
      · rw [prime_pow_excess p 0 hp] at h
        simp at h
      · change σ 1 (p ^ ((k + 1) + 2)) + (p ^ ((k + 1) + 2)).totient =
          2 * p ^ ((k + 1) + 2) + 2 at h
        rw [prime_pow_excess p (k + 1) hp] at h
        have hs : 1 + p ≤ ∑ j ∈ Finset.range (k + 1 + 1), p ^ j := by
          calc
            1 + p = ∑ j ∈ Finset.range 2, p ^ j := by simp [Finset.sum_range_succ]
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr (by omega)) (by omega)
        have := hp.one_lt
        omega
    | coprime a b ha hb hc _ _ =>
      have hsa := le_sigma a ha
      have hsb := le_sigma b hb
      have hta := Nat.totient_lt a ha
      have htb := Nat.totient_lt b hb
      rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc] at h
      have hprod := Nat.mul_le_mul (le_sigma_add_totient a) (le_sigma_add_totient b)
      zify at h hprod
      have hforce (x y : ℕ) (hx : ¬x.Prime) (hx1 : 1 < x) (hy1 : 1 < y) :
          8 ≤ ((σ 1 x : ℤ) - x.totient) * ((σ 1 y : ℤ) - y.totient) := by
        have hsx := lt_sigma_of_not_prime x hx1 hx
        have hsy := le_sigma y hy1
        have htx := Nat.totient_lt x hx1
        have hty := Nat.totient_lt y hy1
        exact mul_le_mul (show (4 : ℤ) ≤ σ 1 x - (x.totient : ℤ) by omega)
          (show (2 : ℤ) ≤ σ 1 y - (y.totient : ℤ) by omega) (by decide) (by omega)
      have hpa : a.Prime := by
        by_contra hn
        linarith only [h, hprod, hforce a b hn ha hb]
      have hpb : b.Prime := by
        by_contra hn
        have he := hforce b a hn hb ha
        rw [mul_comm] at he
        linarith only [h, hprod, he]
      exact ⟨a, b, hpa, hpb, ((Nat.coprime_primes hpa hpb).mp hc), rfl⟩
  · rintro ⟨p, q, hp, hq, hne, rfl⟩
    have hc := (Nat.coprime_primes hp hq).mpr hne
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc,
      sigma_prime hp, sigma_prime hq, Nat.totient_prime hp, Nat.totient_prime hq]
    zify [hp.pos, hq.pos]
    ring


/-- Excess one classifies squares of primes. -/
theorem excess_one_iff (n : ℕ) :
    σ 1 n + n.totient = 2 * n + 1 ↔ ∃ p : ℕ, p.Prime ∧ n = p ^ 2 := by
  constructor
  · intro h
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp at h
    | one => simp at h
    | prime_pow p k hp hk =>
      rcases k with _ | _ | _ | k
      · omega
      · rw [show 0 + 1 = 1 by rfl, pow_one, sigma_prime hp, totient_prime hp] at h
        have := hp.one_lt
        omega
      · exact ⟨p, hp, rfl⟩
      · change σ 1 (p ^ ((k + 1) + 2)) + (p ^ ((k + 1) + 2)).totient =
          2 * p ^ ((k + 1) + 2) + 1 at h
        rw [prime_pow_excess p (k + 1) hp] at h
        have hs : 1 + p ≤ ∑ j ∈ Finset.range (k + 1 + 1), p ^ j := by
          calc
            1 + p = ∑ j ∈ Finset.range 2, p ^ j := by simp [Finset.sum_range_succ]
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr (by omega)) (by omega)
        have := hp.one_lt
        omega
    | coprime a b ha hb hc _ _ =>
      rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc] at h
      have hprod := Nat.mul_le_mul (le_sigma_add_totient a) (le_sigma_add_totient b)
      zify at h hprod
      have hsa := le_sigma a ha
      have hsb := le_sigma b hb
      have hta := Nat.totient_lt a ha
      have htb := Nat.totient_lt b hb
      have hdiff : 4 ≤ ((σ 1 a : ℤ) - a.totient) * ((σ 1 b : ℤ) - b.totient) :=
        mul_le_mul (show (2 : ℤ) ≤ σ 1 a - (a.totient : ℤ) by omega)
          (show (2 : ℤ) ≤ σ 1 b - (b.totient : ℤ) by omega) (by decide) (by omega)
      linarith only [h, hprod, hdiff]
  · rintro ⟨p, hp, rfl⟩
    simpa using prime_pow_excess p 0 hp

private theorem no_prime_squares_at_distance_twelve {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ^ 2 + 12 = q ^ 2) : False := by
  have hp2 := hp.two_le
  have hpq : p < q := by
    by_contra! hle
    have := Nat.mul_le_mul hle hle
    rw [pow_two, pow_two] at h
    omega
  by_cases heq : q = p + 1
  · rw [heq] at h
    have hh : 2 * p + 1 = 12 := by nlinarith
    omega
  · have hle : p + 2 ≤ q := by omega
    have hsq := Nat.mul_le_mul hle hle
    have hp_le : p ≤ 2 := by nlinarith
    have hq_le : q ≤ 4 := by
      have hp_eq : p = 2 := by omega
      rw [hp_eq] at h
      by_contra! H
      have hh := Nat.mul_le_mul H H
      norm_num at h
      nlinarith
    have hq_eq : q = 4 := by omega
    exact (by decide : ¬Nat.Prime 4) (hq_eq ▸ hq)

private theorem ordered_factors {n : ℕ}
    (h : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q := by
  obtain ⟨p, q, hp, hq, hne, hn⟩ := h
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨p, q, hp, hq, h, hn⟩
  · exact ⟨q, p, hq, hp, h, by simpa [mul_comm] using hn⟩

private theorem sum_eq_of_totient {n p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hrs : r < s) (hn : n = p * q) (hm : n + 12 = r * s)
    (ht : (n + 12).totient = n.totient + 12) :
    p + q = r + s := by
  rw [hm, hn, Nat.totient_mul ((Nat.coprime_primes hr hs).mpr hrs.ne),
    Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hpq.ne),
    Nat.totient_prime hp, Nat.totient_prime hq, Nat.totient_prime hr, Nat.totient_prime hs] at ht
  zify [hp.pos, hq.pos, hr.pos, hs.pos] at hn hm ht ⊢
  linarith

/-- If either argument has excess two, the simultaneous totient and divisor-sum
increments by twelve force the pair to come from a prime quadruple. -/
theorem prime_quadruple_of_one_excess_two {n : ℕ}
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12)
    (he : σ 1 n + n.totient = 2 * n + 2 ∨
      σ 1 (n + 12) + (n + 12).totient = 2 * (n + 12) + 2) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  have he₁ : σ 1 n + n.totient = 2 * n + 2 := by omega
  have he₂ : σ 1 (n + 12) + (n + 12).totient = 2 * (n + 12) + 2 := by omega
  obtain ⟨p, q, hp, hq, hpq, hn⟩ := ordered_factors ((excess_two_iff n).mp he₁)
  obtain ⟨r, s, hr, hs', hrs, hm⟩ := ordered_factors ((excess_two_iff (n + 12)).mp he₂)
  have hsum := sum_eq_of_totient hp hq hr hs' hpq hrs hn hm ht
  have hpr : p < r := by
    by_contra! h
    have hsr : (r : ℤ) ≤ s := by exact_mod_cast hrs.le
    have hrp : (r : ℤ) ≤ p := by exact_mod_cast h
    zify at hn hm hsum
    have H := mul_nonneg (show 0 ≤ (p : ℤ) - r by omega)
      (show 0 ≤ (q : ℤ) - r by omega)
    linarith only [hn, hm, hsum, H, show
      (p : ℤ) * q - r * s = ((p : ℤ) - r) * (q - r) from by
        linear_combination (r : ℤ) * hsum]
  have hq2 : q % 2 = 1 := hq.eq_two_or_odd.resolve_left (by
    have := hp.two_le
    omega)
  have hr2 : r % 2 = 1 := hr.eq_two_or_odd.resolve_left (by
    have := hp.two_le
    omega)
  have hs2 : s % 2 = 1 := hs'.eq_two_or_odd.resolve_left (by
    have := hr.two_le
    omega)
  have hp2 : p % 2 = 1 := by omega
  let d := r - p
  let e := q - r
  have hd : 0 < d := by dsimp [d]; omega
  have hde : d ≤ e := by dsimp [d, e]; omega
  have hdp : d % 2 = 0 := by dsimp [d]; omega
  have hprod : d * e = 12 := by
    have hd' : d + p = r := by dsimp [d]; omega
    have he' : e + r = q := by dsimp [e]; omega
    have hs'' : s = p + e := by omega
    rw [← hd'] at he'
    rw [← hd', hs''] at hm
    rw [← he'] at hn
    nlinarith only [hn, hm]
  have hd4 : d < 4 := by
    by_contra! hd4
    have hm16 : 4 * 4 ≤ d * e := Nat.mul_le_mul hd4 (hd4.trans hde)
    omega
  have hd2 : d = 2 := by omega
  have he6 : e = 6 := by rw [hd2] at hprod; omega
  have hrp : r = p + 2 := by dsimp [d] at hd2; omega
  have hsp : s = p + 6 := by dsimp [e] at he6; omega
  have hqp : q = p + 8 := by dsimp [e] at he6; omega
  refine ⟨p, hp, hrp ▸ hr, hsp ▸ hs', hqp ▸ hq, ?_⟩
  simpa [hqp] using hn

/-- The prime-quadruple conjecture holds whenever either member of the pair
is semiprime, including the case of a square of a prime. -/
theorem prime_quadruple_of_one_semiprime {n : ℕ}
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12)
    (hp : (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n + 12 = p * q) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  rcases hp with ⟨p, q, hp, hq, hn⟩ | ⟨p, q, hp, hq, hn⟩
  · by_cases h : p = q
    · subst q
      have he := (excess_one_iff n).mpr ⟨p, hp, by simpa [pow_two] using hn⟩
      obtain ⟨q, hq, hm⟩ := (excess_one_iff (n + 12)).mp (by omega)
      exact (no_prime_squares_at_distance_twelve hp hq (by simp_all [pow_two])).elim
    · exact prime_quadruple_of_one_excess_two ht hs
        (Or.inl ((excess_two_iff n).mpr ⟨p, q, hp, hq, h, hn⟩))
  · by_cases h : p = q
    · subst q
      have he := (excess_one_iff (n + 12)).mpr ⟨p, hp, by simpa [pow_two] using hn⟩
      obtain ⟨q, hq, hm⟩ := (excess_one_iff n).mp (by omega)
      exact (no_prime_squares_at_distance_twelve hq hp (by simp_all [pow_two])).elim
    · exact prime_quadruple_of_one_excess_two ht hs
        (Or.inr ((excess_two_iff (n + 12)).mpr ⟨p, q, hp, hq, h, hn⟩))

theorem factor_count_of_nonsemiprime {n : ℕ} (hn : 1 < n) (hp : ¬n.Prime)
    (hs : ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) :
    3 ≤ n.primeFactorsList.length := by
  have hprod := Nat.prod_primeFactorsList (n := n) (by omega)
  have hprime {p : ℕ} (hm : p ∈ n.primeFactorsList) := Nat.prime_of_mem_primeFactorsList hm
  cases h : n.primeFactorsList with
  | nil => simp [h] at hprod; omega
  | cons p tail =>
    cases tail with
    | nil =>
      have hp' := hprime (p := p) (by simp [h])
      simp [h] at hprod
      exact (hp (hprod ▸ hp')).elim
    | cons q tail =>
      cases tail with
      | nil =>
        exact (hs ⟨p, q, hprime (by simp [h]), hprime (by simp [h]),
          by simpa [h] using hprod.symm⟩).elim
      | cons r tail => simp

/-- A counterexample to the converse for A056777 must have at least three
prime factors, counted with multiplicity, in both positions. -/
theorem factor_count_of_counterexample {n : ℕ} (hn : 1 < n) (hp : ¬n.Prime)
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12)
    (hc : ¬∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧
      (p + 8).Prime ∧ n = p * (p + 8)) :
    3 ≤ n.primeFactorsList.length ∧ 3 ≤ (n + 12).primeFactorsList.length := by
  have hm : ¬(n + 12).Prime := by
    intro hm
    rw [sigma_prime hm] at hs
    have := lt_sigma_of_not_prime n hn hp
    omega
  exact ⟨factor_count_of_nonsemiprime hn hp
      (fun h => hc (prime_quadruple_of_one_semiprime ht hs (Or.inl h))),
    factor_count_of_nonsemiprime (by omega) hm
      (fun h => hc (prime_quadruple_of_one_semiprime ht hs (Or.inr h)))⟩

/-- The low values of the excess for an odd squarefree number are zero and two. -/
theorem low_excess_of_odd_squarefree (n : ℕ) (ho : Odd n) (hs : Squarefree n) :
    σ 1 n + n.totient = 2 * n ∨ σ 1 n + n.totient = 2 * n + 2 ∨
      2 * n + 10 ≤ σ 1 n + n.totient := by
  suffices h : n = 1 ∨ n.Prime ∨ σ 1 n + n.totient = 2 * n + 2 ∨
      2 * n + 10 ≤ σ 1 n + n.totient by
    rcases h with rfl | hp | h | h
    · left; simp
    · left
      rw [sigma_prime hp, Nat.totient_prime hp]
      have := hp.one_lt
      omega
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp at ho
  | one => exact Or.inl rfl
  | prime_pow p k hp hk =>
    have h := hs.natFactorization_le_one p
    rw [hp.factorization_pow, Finsupp.single_eq_same] at h
    have h1 : k = 1 := by omega
    subst k
    exact Or.inr (Or.inl (by simpa using hp))
  | coprime a b ha hb hc iha ihb =>
    obtain ⟨hoa, hob⟩ := Nat.odd_mul.mp ho
    have hsa := hs.squarefree_of_dvd (dvd_mul_right a b)
    have hsb := hs.squarefree_of_dvd (dvd_mul_left b a)
    by_cases hab : a.Prime ∧ b.Prime
    · exact Or.inr (Or.inr (Or.inl ((excess_two_iff _).mpr
        ⟨a, b, hab.1, hab.2, (Nat.coprime_primes hab.1 hab.2).mp hc, rfl⟩)))
    · have hhelper (x y : ℕ) (hx : 1 < x) (hy : 1 < y) (hyod : Odd y)
          (hcop : x.Coprime y) (hnp : ¬x.Prime)
          (hi : x = 1 ∨ x.Prime ∨ σ 1 x + x.totient = 2 * x + 2 ∨
            2 * x + 10 ≤ σ 1 x + x.totient) :
          2 * (x * y) + 10 ≤ σ 1 (x * y) + (x * y).totient := by
        have hDx : 2 * x + 2 ≤ σ 1 x + x.totient := by
          rcases hi with h | h | h | h
          · omega
          · exact (hnp h).elim
          · omega
          · omega
        have hDy := le_sigma_add_totient y
        have hy3 : 3 ≤ y := by have := Nat.odd_iff.mp hyod; omega
        have hprod := Nat.mul_le_mul hDx hDy
        have hσx := lt_sigma_of_not_prime x hx hnp
        have hσy := le_sigma y hy
        have htx := Nat.totient_lt x hx
        have hty := Nat.totient_lt y hy
        have hdiff : 8 ≤ ((σ 1 x : ℤ) - x.totient) * ((σ 1 y : ℤ) - y.totient) :=
          mul_le_mul (show (4 : ℤ) ≤ σ 1 x - (x.totient : ℤ) by omega)
            (show (2 : ℤ) ≤ σ 1 y - (y.totient : ℤ) by omega) (by decide) (by omega)
        rw [isMultiplicative_sigma.map_mul_of_coprime hcop, Nat.totient_mul hcop]
        zify at hprod hy3 ⊢
        linarith only [hprod, hy3, hdiff]
      refine Or.inr (Or.inr (Or.inr ?_))
      by_cases hap : a.Prime
      · have hbp : ¬b.Prime := fun hp => hab ⟨hap, hp⟩
        simpa [mul_comm] using hhelper b a hb ha hoa hc.symm hbp (ihb hob hsb)
      · exact hhelper a b ha hb hob hc hap (iha hoa hsa)

end A056777Closure

namespace A056777Parity

theorem geom_odd_mod_two {p : ℕ} (hp : p % 2 = 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp]
    simp [Nat.add_mod]

private theorem prime_pow_square_shape {p k : ℕ} (hp : p.Prime)
    (h : Odd (σ 1 (p ^ k))) :
    (∃ a : ℕ, p ^ k = a ^ 2) ∨ ∃ a : ℕ, p ^ k = 2 * a ^ 2 := by
  rcases hp.eq_two_or_odd with rfl | hpodd
  · by_cases hk : k % 2 = 0
    · left
      exact ⟨2 ^ (k / 2), by rw [← pow_mul, show k / 2 * 2 = k by omega]⟩
    · right
      exact ⟨2 ^ (k / 2), by rw [← pow_mul, ← pow_succ', show (k / 2 * 2).succ = k by omega]⟩
  · have ho := Nat.odd_iff.mp h
    rw [sigma_one_apply_prime_pow hp, geom_odd_mod_two hpodd] at ho
    left
    exact ⟨p ^ (k / 2), by rw [← pow_mul, show k / 2 * 2 = k by omega]⟩

/-- Odd divisor sums occur only for squares and twice squares. -/
theorem square_or_twice_square {n : ℕ} (h : Odd (σ 1 n)) :
    (∃ a : ℕ, n = a ^ 2) ∨ ∃ a : ℕ, n = 2 * a ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => left; exact ⟨0, by decide⟩
  | one => left; exact ⟨1, by decide⟩
  | prime_pow p k hp hk => exact prime_pow_square_shape hp h
  | coprime a b ha hb hc iha ihb =>
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.odd_mul] at h
    rcases iha h.1 with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
      rcases ihb h.2 with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨x * y, by ring⟩
    · exact Or.inr ⟨x * y, by ring⟩
    · exact Or.inr ⟨x * y, by ring⟩
    · have := Nat.dvd_gcd (dvd_mul_right 2 (x ^ 2)) (dvd_mul_right 2 (y ^ 2))
      rw [hc.gcd_eq_one] at this
      omega

private theorem geom_two_mod_two (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (2 : ℕ) ^ i) % 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, pow_succ', Nat.mul_mod]
    simp

private theorem odd_sigma_of_even_odd_prime_exponents (n : ℕ) (hn : n ≠ 0)
    (hf : ∀ p, p.Prime → p ≠ 2 → Even (n.factorization p)) :
    Odd (σ 1 n) := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [Nat.mul_one]
  suffices h : ∀ s : Finset ℕ, s ⊆ n.primeFactors →
      Odd (∏ p ∈ s, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) by
    exact h _ Subset.rfl
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    intro hsub
    have hprime := Nat.prime_of_mem_primeFactors (hsub (Finset.mem_insert_self p s))
    rw [Finset.prod_insert hp, Nat.odd_mul]
    refine ⟨?_, ih (fun q hq => hsub (Finset.mem_insert_of_mem hq))⟩
    rw [Nat.odd_iff]
    rcases hprime.eq_two_or_odd with hp' | hp'
    · rw [hp', geom_two_mod_two]
    · have hne : p ≠ 2 := by omega
      obtain ⟨k, hk⟩ := hf p hprime hne
      rw [geom_odd_mod_two hp', hk]
      omega

/-- A positive number has odd divisor sum precisely when it is a square or twice a square. -/
theorem odd_sigma_iff_square_or_twice_square {n : ℕ} (hn : n ≠ 0) :
    Odd (σ 1 n) ↔ (∃ a : ℕ, n = a ^ 2) ∨ ∃ a : ℕ, n = 2 * a ^ 2 := by
  refine ⟨square_or_twice_square, ?_⟩
  intro h
  apply odd_sigma_of_even_odd_prime_exponents _ hn
  intro p _ hp
  rcases h with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact ⟨a.factorization p, by omega⟩
  · have ha : a ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul (by decide) (pow_ne_zero _ ha),
      Nat.prime_two.factorization, Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.single_eq_of_ne hp, Finsupp.smul_apply, smul_eq_mul, zero_add]
    exact ⟨a.factorization p, by omega⟩

private theorem sq_mod_four (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt a (by decide : 0 < 4)
  interval_cases (a % 4) <;> decide

private theorem sq_mod_eight (a : ℕ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt a (by decide : 0 < 8)
  interval_cases (a % 8) <;> decide

private theorem not_sq_add_twelve_eq_twice_sq (a b : ℕ) : a ^ 2 + 12 ≠ 2 * b ^ 2 := by
  intro h
  have ha : a % 2 = 0 := by
    have hh := congrArg (· % 4) h
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod a, Nat.pow_mod b] at hh
    have ha4 := Nat.mod_lt a (by decide : 0 < 4)
    have hb4 := Nat.mod_lt b (by decide : 0 < 4)
    have ha' : a % 2 = a % 4 % 2 := by omega
    rw [ha']
    interval_cases (a % 4) <;> interval_cases (b % 4) <;> (norm_num at hh) <;> decide
  have hb : b % 2 = 0 := by
    have hh := congrArg (· % 4) h
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod a, Nat.pow_mod b] at hh
    have ha4 := Nat.mod_lt a (by decide : 0 < 4)
    have hb4 := Nat.mod_lt b (by decide : 0 < 4)
    have hb' : b % 2 = b % 4 % 2 := by omega
    rw [hb']
    interval_cases (a % 4) <;> interval_cases (b % 4) <;> (norm_num at hh) <;> decide
  have ha' : a = 2 * (a / 2) := by omega
  have hb' : b = 2 * (b / 2) := by omega
  have H : (a / 2) ^ 2 + 3 = 2 * (b / 2) ^ 2 := by
    nlinarith only [h, congrArg (· ^ 2) ha', congrArg (· ^ 2) hb']
  have hh := congrArg (· % 8) H
  rw [Nat.add_mod, Nat.mul_mod] at hh
  rcases sq_mod_eight (a / 2) with A | A | A <;>
    rcases sq_mod_eight (b / 2) with B | B | B <;> norm_num [A, B] at hh

private theorem not_twice_sq_add_twelve_eq_sq (a b : ℕ) : 2 * a ^ 2 + 12 ≠ b ^ 2 := by
  intro h
  have ha : a % 2 = 0 := by
    have hh := congrArg (· % 4) h
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod a, Nat.pow_mod b] at hh
    have ha4 := Nat.mod_lt a (by decide : 0 < 4)
    have hb4 := Nat.mod_lt b (by decide : 0 < 4)
    have ha' : a % 2 = a % 4 % 2 := by omega
    rw [ha']
    interval_cases (a % 4) <;> interval_cases (b % 4) <;> (norm_num at hh) <;> decide
  have hb : b % 2 = 0 := by
    have hh := congrArg (· % 4) h
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod a, Nat.pow_mod b] at hh
    have ha4 := Nat.mod_lt a (by decide : 0 < 4)
    have hb4 := Nat.mod_lt b (by decide : 0 < 4)
    have hb' : b % 2 = b % 4 % 2 := by omega
    rw [hb']
    interval_cases (a % 4) <;> interval_cases (b % 4) <;> (norm_num at hh) <;> decide
  have ha' : a = 2 * (a / 2) := by omega
  have hb' : b = 2 * (b / 2) := by omega
  have H : 2 * (a / 2) ^ 2 + 3 = (b / 2) ^ 2 := by
    nlinarith only [h, congrArg (· ^ 2) ha', congrArg (· ^ 2) hb']
  have hh := congrArg (· % 8) H
  rw [Nat.add_mod, Nat.mul_mod] at hh
  rcases sq_mod_eight (a / 2) with A | A | A <;>
    rcases sq_mod_eight (b / 2) with B | B | B <;> norm_num [A, B] at hh

private theorem eq_two_of_sq_add_twelve_eq_sq (a b : ℕ) (h : a ^ 2 + 12 = b ^ 2) : a = 2 := by
  have hab : a < b := by
    by_contra! hab
    have hh := Nat.mul_le_mul hab hab
    rw [pow_two, pow_two] at h
    omega
  by_cases heq : b = a + 1
  · subst b
    have hh : 2 * a + 1 = 12 := by nlinarith
    omega
  · have hle : a + 2 ≤ b := by omega
    have hsq := Nat.mul_le_mul hle hle
    have ha2 : a ≤ 2 := by nlinarith
    interval_cases a
    · have hb : 3 < b := by
        by_contra! hh
        have := Nat.mul_le_mul hh hh
        nlinarith
      have := Nat.mul_le_mul (show 4 ≤ b by omega) (show 4 ≤ b by omega)
      nlinarith
    · have hb : 3 < b := by
        by_contra! hh
        have := Nat.mul_le_mul hh hh
        nlinarith
      have := Nat.mul_le_mul (show 4 ≤ b by omega) (show 4 ≤ b by omega)
      nlinarith
    · rfl

/-- Any pair satisfying the divisor-sum condition of A056777 has even divisor sums.
This excludes all square and twice-square endpoints with odd divisor sum. -/
theorem even_sigma_of_sigma_step {n : ℕ} (h : σ 1 (n + 12) = σ 1 n + 12) :
    Even (σ 1 n) ∧ Even (σ 1 (n + 12)) := by
  have he : Even (σ 1 n) := by
    by_contra hnot
    have h₁ : Odd (σ 1 n) := Nat.not_even_iff_odd.mp hnot
    have h₂ : Odd (σ 1 (n + 12)) := by rw [Nat.odd_iff, h]; have := Nat.odd_iff.mp h₁; omega
    rcases square_or_twice_square h₁ with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
      rcases square_or_twice_square h₂ with ⟨b, hb⟩ | ⟨b, hb⟩
    · have : a = 2 := eq_two_of_sq_add_twelve_eq_sq a b (ha ▸ hb)
      subst a
      subst n
      revert h
      decide
    · exact not_sq_add_twelve_eq_twice_sq a b (ha ▸ hb)
    · exact not_twice_sq_add_twelve_eq_sq a b (ha ▸ hb)
    · have h' : a ^ 2 + 6 = b ^ 2 := by omega
      have hh := congrArg (· % 4) h'
      rw [Nat.add_mod] at hh
      rcases sq_mod_four a with A | A <;> rcases sq_mod_four b with B | B <;>
        norm_num [A, B] at hh
  exact ⟨he, by rw [h]; exact he.add (by decide)⟩

/-- The divisor-sum condition alone excludes squares and twice squares at both endpoints. -/
theorem no_square_shapes_of_sigma_step {n : ℕ} (hn : n ≠ 0)
    (h : σ 1 (n + 12) = σ 1 n + 12) :
    (¬ ((∃ a : ℕ, n = a ^ 2) ∨ ∃ a : ℕ, n = 2 * a ^ 2)) ∧
    (¬ ((∃ a : ℕ, n + 12 = a ^ 2) ∨ ∃ a : ℕ, n + 12 = 2 * a ^ 2)) := by
  rw [← odd_sigma_iff_square_or_twice_square hn,
      ← odd_sigma_iff_square_or_twice_square (show n + 12 ≠ 0 by omega)]
  obtain ⟨he₁, he₂⟩ := even_sigma_of_sigma_step h
  exact ⟨fun ho => (Nat.not_even_iff_odd.mpr ho) he₁,
    fun ho => (Nat.not_even_iff_odd.mpr ho) he₂⟩

/-- Both arguments have some odd prime occurring to an odd exponent. -/
theorem odd_prime_exponents_of_sigma_step {n : ℕ} (hn : n ≠ 0)
    (h : σ 1 (n + 12) = σ 1 n + 12) :
    (∃ p, p.Prime ∧ p ≠ 2 ∧ Odd (n.factorization p)) ∧
    (∃ p, p.Prime ∧ p ≠ 2 ∧ Odd ((n + 12).factorization p)) := by
  have hexists {m : ℕ} (hm : m ≠ 0) (he : Even (σ 1 m)) :
      ∃ p, p.Prime ∧ p ≠ 2 ∧ Odd (m.factorization p) := by
    by_contra! hall
    apply (Nat.not_even_iff_odd.mpr (odd_sigma_of_even_odd_prime_exponents m hm ?_)) he
    intro p hp hp2
    by_contra hn
    exact hall p hp hp2 (Nat.not_even_iff_odd.mp hn)
  obtain ⟨he₁, he₂⟩ := even_sigma_of_sigma_step h
  exact ⟨hexists hn he₁, hexists (by omega) he₂⟩

end A056777Parity

namespace A056777Squarefree

/-- Each odd prime with odd exponent contributes at least one factor of two
to the divisor sum. -/
theorem two_pow_card_odd_exponents_dvd_sigma {n : ℕ} (hn : n ≠ 0) :
    2 ^ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ∣ σ 1 n := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [Nat.mul_one]
  let s := n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)
  let f (p : ℕ) := ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i
  change 2 ^ s.card ∣ ∏ p ∈ n.primeFactors, f p
  have hsub : s ⊆ n.primeFactors := Finset.filter_subset _ _
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset s n.primeFactors f hsub)
  rw [← Finset.prod_const]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  have ⟨hmem, hp2, hexp⟩ := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hmem
  have hodd := hprime.eq_two_or_odd.resolve_left hp2
  apply Nat.dvd_of_mod_eq_zero
  dsimp [f]
  rw [A056777Parity.geom_odd_mod_two hodd]
  have := Nat.odd_iff.mp hexp
  omega

/-- The divisor-sum step by twelve forces at least one endpoint to have
at most two odd primes occurring to odd exponents. -/
theorem at_most_two_odd_exponents_of_sigma_step {n : ℕ} (hn : n ≠ 0)
    (hs : σ 1 (n + 12) = σ 1 n + 12) :
    (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ≤ 2 ∨
    ((n + 12).primeFactors.filter fun p => p ≠ 2 ∧ Odd ((n + 12).factorization p)).card ≤ 2 := by
  by_contra! h
  have h₁ := dvd_trans (pow_dvd_pow 2 (show 3 ≤ _ from h.1))
    (two_pow_card_odd_exponents_dvd_sigma hn)
  have h₂ := dvd_trans (pow_dvd_pow 2 (show 3 ≤ _ from h.2))
    (two_pow_card_odd_exponents_dvd_sigma (show n + 12 ≠ 0 by omega))
  change 8 ∣ σ 1 n at h₁
  change 8 ∣ σ 1 (n + 12) at h₂
  omega

private theorem filter_eq_primeFactors {n : ℕ} (hs : Squarefree n) (ho : Odd n) :
    (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)) = n.primeFactors := by
  apply Finset.filter_eq_self.mpr
  intro p hp
  have ⟨hprime, hdiv, hn⟩ := Nat.mem_primeFactors.mp hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := Nat.odd_iff.mp ho
    omega
  have hpos := hprime.factorization_pos_of_dvd hn hdiv
  have hle := hs.natFactorization_le_one p
  have he : n.factorization p = 1 := by omega
  exact ⟨hp2, he ▸ (by decide : Odd 1)⟩

private theorem factor_count_eq_of_squarefree {n : ℕ} (hs : Squarefree n) :
    n.primeFactors.card = n.primeFactorsList.length := by
  rw [← Nat.toFinset_factors, List.toFinset_card_of_nodup hs.nodup_primeFactorsList]

/-- The A056777 pair comes from a prime quadruple if both endpoints are odd and squarefree. -/
theorem prime_quadruple_of_odd_squarefree_pair {n : ℕ}
    (hn : 1 < n) (hnp : ¬n.Prime) (ho : Odd n)
    (h₁ : Squarefree n) (h₂ : Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  by_contra h
  obtain ⟨hc₁, hc₂⟩ := A056777Closure.factor_count_of_counterexample hn hnp ht hs h
  have ho' : Odd (n + 12) := by
    rw [Nat.odd_iff]
    have := Nat.odd_iff.mp ho
    omega
  have hcount := at_most_two_odd_exponents_of_sigma_step (show n ≠ 0 by omega) hs
  rw [filter_eq_primeFactors h₁ ho, filter_eq_primeFactors h₂ ho',
    factor_count_eq_of_squarefree h₁, factor_count_eq_of_squarefree h₂] at hcount
  omega

private theorem dvd_eight_sigma_of_card_ge_three {n : ℕ} (hn : Squarefree n) (ho : Odd n)
    (hc : 3 ≤ n.primeFactors.card) : 8 ∣ σ 1 n := by
  have h := two_pow_card_odd_exponents_dvd_sigma (n := n) hn.ne_zero
  rw [filter_eq_primeFactors hn ho] at h
  exact (pow_dvd_pow 2 hc).trans h

private theorem low_excess_of_card_le_two {n : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card ≤ 2) :
    σ 1 n + n.totient = 2 * n ∨ σ 1 n + n.totient = 2 * n + 2 := by
  by_cases hn1 : n = 1
  · subst n
    simp
  by_cases hp : n.Prime
  · left
    have hσ : σ 1 n = n + 1 := by simpa using sigma_one_apply_prime_pow (i := 1) hp
    rw [hσ, Nat.totient_prime hp]
    have := hp.one_lt
    omega
  · right
    have hnn : 1 < n := by have := hn.ne_zero; omega
    have hh (h : ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) : False := by
      have hlen := A056777Closure.factor_count_of_nonsemiprime hnn hp h
      rw [← factor_count_eq_of_squarefree hn] at hlen
      omega
    obtain ⟨p, q, hpp, hq, rfl⟩ := not_not.mp (fun h => hh h)
    have hne : p ≠ q := by
      rintro rfl
      exact (Nat.squarefree_iff_prime_squarefree.mp hn p hpp) (dvd_refl _)
    exact (A056777Closure.excess_two_iff _).mpr ⟨p, q, hpp, hq, hne, rfl⟩

/-- The A056777 conditions are incompatible with both endpoints being even and squarefree. -/
theorem no_even_squarefree_pair {n : ℕ}
    (he : Even n) (h₁ : Squarefree n) (h₂ : Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) : False := by
  obtain ⟨m, hm⟩ := he
  have hn : n = 2 * m := by omega
  have hn' : n + 12 = 2 * (m + 6) := by omega
  rw [hn] at h₁
  rw [hn'] at h₂
  have hcop₁ := Nat.coprime_of_squarefree_mul h₁
  have hcop₂ := Nat.coprime_of_squarefree_mul h₂
  have ho₁ := hcop₁.odd_of_left
  have ho₂ := hcop₂.odd_of_left
  have hsq₁ := h₁.squarefree_of_dvd (dvd_mul_left m 2)
  have hsq₂ := h₂.squarefree_of_dvd (dvd_mul_left (m + 6) 2)
  rw [hn', hn, Nat.totient_mul hcop₁, Nat.totient_mul hcop₂] at ht
  norm_num at ht
  rw [hn', hn, isMultiplicative_sigma.map_mul_of_coprime hcop₁,
    isMultiplicative_sigma.map_mul_of_coprime hcop₂, show σ 1 2 = 3 by decide] at hs
  have hadd : σ 1 (m + 6) = σ 1 m + 4 := by omega
  have hsmall : m.primeFactors.card ≤ 2 ∨ (m + 6).primeFactors.card ≤ 2 := by
    by_contra! h
    have hd₁ := dvd_eight_sigma_of_card_ge_three hsq₁ ho₁ (by omega)
    have hd₂ := dvd_eight_sigma_of_card_ge_three hsq₂ ho₂ (by omega)
    omega
  rcases hsmall with hc | hc
  · rcases low_excess_of_card_le_two hsq₁ hc with h | h <;>
      rcases A056777Closure.low_excess_of_odd_squarefree (m + 6) ho₂ hsq₂ with h' | h' | h' <;>
      omega
  · rcases low_excess_of_card_le_two hsq₂ hc with h | h <;>
      rcases A056777Closure.low_excess_of_odd_squarefree m ho₁ hsq₁ with h' | h' | h' <;>
      omega

/-- The A056777 converse holds whenever both endpoints are squarefree. -/
theorem prime_quadruple_of_squarefree_pair {n : ℕ}
    (hn : 1 < n) (hnp : ¬n.Prime) (h₁ : Squarefree n) (h₂ : Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  by_cases he : Even n
  · exact (no_even_squarefree_pair he h₁ h₂ ht hs).elim
  · exact prime_quadruple_of_odd_squarefree_pair hn hnp
      (Nat.not_even_iff_odd.mp he) h₁ h₂ ht hs

end A056777Squarefree

open OeisA56777

private theorem positive_odd_exponent_count {n : ℕ} (hn : n ≠ 0)
    (h : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Odd (n.factorization p)) :
    1 ≤ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card := by
  obtain ⟨p, hp, hp2, hodd⟩ := h
  have hpos : 0 < n.factorization p := by
    have := Nat.odd_iff.mp hodd
    omega
  have hmem := Nat.mem_primeFactors.mpr ⟨hp, Nat.dvd_of_factorization_pos hpos.ne', hn⟩
  exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hmem, hp2, hodd⟩⟩

/-- Exclude a remaining pair whose first endpoint has only one or two odd primes
occurring to odd exponents. -/
def H1 : Prop :=
  ∀ n : ℕ, A n →
    3 ≤ n.primeFactorsList.length →
    3 ≤ (n + 12).primeFactorsList.length →
    (¬ Squarefree n ∨ ¬ Squarefree (n + 12)) →
    1 ≤ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card →
    (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ≤ 2 →
    1 ≤ ((n + 12).primeFactors.filter fun p =>
      p ≠ 2 ∧ Odd ((n + 12).factorization p)).card →
    False

/-- Exclude a remaining pair whose first endpoint has at least three such primes
and whose second endpoint has only one or two. -/
def H2 : Prop :=
  ∀ n : ℕ, A n →
    3 ≤ n.primeFactorsList.length →
    3 ≤ (n + 12).primeFactorsList.length →
    (¬ Squarefree n ∨ ¬ Squarefree (n + 12)) →
    3 ≤ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card →
    1 ≤ ((n + 12).primeFactors.filter fun p =>
      p ≠ 2 ∧ Odd ((n + 12).factorization p)).card →
    ((n + 12).primeFactors.filter fun p => p ≠ 2 ∧ Odd ((n + 12).factorization p)).card ≤ 2 →
    False

theorem main : H1 → H2 → type_of% @OeisA56777.comesFromPrimeQuadruple_of_a := by
  intro h1 h2 n ha
  have ⟨hnp, hn, ht, hs⟩ := ha
  by_contra hc
  have hrepeat : ¬ Squarefree n ∨ ¬ Squarefree (n + 12) := by
    by_contra! hall
    exact hc (A056777Squarefree.prime_quadruple_of_squarefree_pair hn hnp hall.1 hall.2 ht hs)
  obtain ⟨hf₁, hf₂⟩ := A056777Closure.factor_count_of_counterexample hn hnp ht hs hc
  have hne : n ≠ 0 := by omega
  obtain ⟨hex₁, hex₂⟩ := A056777Parity.odd_prime_exponents_of_sigma_step hne hs
  have hc₁ := positive_odd_exponent_count hne hex₁
  have hc₂ := positive_odd_exponent_count (by omega) hex₂
  rcases A056777Squarefree.at_most_two_odd_exponents_of_sigma_step hne hs with hl | hr
  · exact h1 n ha hf₁ hf₂ hrepeat hc₁ hl hc₂
  · by_cases hl : (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ≤ 2
    · exact h1 n ha hf₁ hf₂ hrepeat hc₁ hl hc₂
    · exact h2 n ha hf₁ hf₂ hrepeat (by omega) hc₂ hr

end OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R1
