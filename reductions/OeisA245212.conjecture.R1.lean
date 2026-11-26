import FormalConjectures.OEIS.«245212»

-- Reduction OeisA245212.conjecture.R1 of Difference between $n \tau(n)$ and $\sum_{d \mid n, d < n} d \tau(d)$
-- Credit: @BetAdmin237
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Target: for n > 0, a(n) = sigma(n) iff n is a power of 2, where
-- a(n) = n tau(n) - sum over proper divisors d of n of d tau(d).
--
-- Proved outright in this file:
--  * for every prime p and k, a(p^k) = (k+1) p^k - sum_{j<k} (j+1) p^j (a_prime_pow);
--  * the backward direction: a(2^k) = 2^(k+1) - 1 = sigma(2^k) for every k (two_pow_holds);
--  * every odd prime power p^k (k >= 1) fails: a(p^k) = sigma(p^k) would force
--    sum_{j<k} (j+2) p^j = k p^k, but 2 sum_{j<k} (j+2) p^j + 2 <= (k+1) p^k for p >= 3
--    (odd_prime_pow_fails).
-- The remaining open core of the forward direction is split by the shape of n:
--  H1: odd n > 1 with at least two distinct prime factors;
--  H2: n = 2^k m with k >= 1 and m odd, m > 1.

namespace OMA.R_OeisA245212_conjecture_R1

open Finset
open scoped ArithmeticFunction.sigma

def H1 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → ¬ IsPrimePow n → OeisA245212.a n ≠ (σ 1 n : ℤ)

def H2 : Prop :=
  ∀ k m : ℕ, 1 ≤ k → Odd m → 1 < m →
    OeisA245212.a (2 ^ k * m) ≠ (σ 1 (2 ^ k * m) : ℤ)

lemma a_prime_pow (p : ℕ) (hp : p.Prime) (k : ℕ) :
    OeisA245212.a (p ^ k) =
      (p : ℤ) ^ k * (k + 1) - ∑ j ∈ range k, (p : ℤ) ^ j * (j + 1) := by
  unfold OeisA245212.a
  rw [Nat.divisors_prime_pow hp, card_map, card_range, Nat.properDivisors_prime_pow hp,
    sum_map]
  simp only [Function.Embedding.coeFn_mk, Nat.divisors_prime_pow hp, card_map, card_range]
  push_cast
  ring

lemma sigma_prime_pow (p : ℕ) (hp : p.Prime) (k : ℕ) :
    (σ 1 (p ^ k) : ℤ) = ∑ j ∈ range (k + 1), (p : ℤ) ^ j := by
  rw [ArithmeticFunction.sigma_apply_prime_pow hp]
  push_cast
  apply sum_congr rfl
  intro j _
  rw [mul_one]

lemma two_pow_sum (k : ℕ) :
    ∑ j ∈ range k, (2 : ℤ) ^ j * (j + 1) + 2 ^ (k + 1) = (k + 1) * 2 ^ k + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    push_cast
    have e : (2 : ℤ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    rw [e]
    have e2 : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [e2] at ih ⊢
    nlinarith [ih]

lemma geom_two (k : ℕ) : ∑ j ∈ range (k + 1), (2 : ℤ) ^ j = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    ring

lemma two_pow_holds (k : ℕ) : OeisA245212.a (2 ^ k) = (σ 1 (2 ^ k) : ℤ) := by
  rw [a_prime_pow 2 Nat.prime_two k, sigma_prime_pow 2 Nat.prime_two k]
  push_cast
  rw [geom_two]
  have := two_pow_sum k
  linarith

lemma odd_bound (p : ℕ) (hp3 : 3 ≤ p) (m : ℕ) :
    2 * (∑ j ∈ range (m + 1), (p : ℤ) ^ j * (j + 2)) + 2 ≤ (m + 2) * (p : ℤ) ^ (m + 1) := by
  have hpR : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  induction m with
  | zero => simp; linarith
  | succ m ih =>
    rw [sum_range_succ]
    push_cast at ih ⊢
    have hpos : (0 : ℤ) < (p : ℤ) ^ (m + 1) := by positivity
    have e : (p : ℤ) ^ (m + 1 + 1) = p * p ^ (m + 1) := by ring
    rw [e]
    have hm : (0 : ℤ) ≤ m := by exact_mod_cast Nat.zero_le m
    nlinarith [mul_le_mul_of_nonneg_right hpR hpos.le, mul_nonneg hm hpos.le,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpR hpos.le) hm]

lemma odd_prime_pow_fails (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) (hk : 1 ≤ k) :
    OeisA245212.a (p ^ k) ≠ (σ 1 (p ^ k) : ℤ) := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le; omega
  rw [a_prime_pow p hp k, sigma_prime_pow p hp k]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  intro h
  have hb := odd_bound p hp3 m
  have hsplit : ∑ j ∈ range (m + 1), (p : ℤ) ^ j * (j + 2) =
      ∑ j ∈ range (m + 1), (p : ℤ) ^ j * (j + 1) + ∑ j ∈ range (m + 1), (p : ℤ) ^ j := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [sum_range_succ (fun j => (p : ℤ) ^ j) (m + 1)] at h
  have hpos : (0 : ℤ) < (p : ℤ) ^ (m + 1) := by positivity
  have hm : (0 : ℤ) ≤ m := by exact_mod_cast Nat.zero_le m
  push_cast at h hb
  nlinarith [mul_nonneg hm hpos.le]

theorem main : H1 → H2 → type_of% @OeisA245212.conjecture := by
  intro h1 h2 n hn
  constructor
  · intro heq
    by_contra hnot
    obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hnot ⟨k, by simpa using hnm⟩
    have hm0 : 0 < m := hm.pos
    by_cases hk : k = 0
    · subst hk
      simp only [pow_zero, one_mul] at hnm
      subst hnm
      by_cases hpp : IsPrimePow n
      · obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
        have hp2 : p ≠ 2 := by
          rintro rfl
          have : Even (2 ^ j) := (Nat.even_pow' (by omega)).mpr even_two
          exact (Nat.not_even_iff_odd.mpr hm) this
        exact odd_prime_pow_fails p hp hp2 j hj heq
      · exact h1 n (by omega) hm hpp heq
    · subst hnm
      exact h2 k m (by omega) hm (by omega) heq
  · rintro ⟨k, rfl⟩
    exact two_pow_holds k

end OMA.R_OeisA245212_conjecture_R1
