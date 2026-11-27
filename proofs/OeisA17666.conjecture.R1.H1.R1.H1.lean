import OMAReductions.R_OeisA17666_conjecture_R1_H1_R1

-- An odd perfect number has at least three distinct prime factors.
-- Original proof of a classical fact. The divisor sum of n satisfies sigma(n) * prod (p - 1) <= n * prod p,
-- the products over the primes dividing n (prime powers by the geometric sum, then multiplicativity), so a
-- perfect n needs 2 * prod (p - 1) <= prod p, which fails for one odd prime and for two distinct odd primes.
-- This is a small classical case of the odd perfect number problem, not progress on it.

namespace OMA.A17666

open ArithmeticFunction Finset

lemma geom' (c : ℕ) : ∀ i : ℕ, (∑ k ∈ range (i + 1), (c + 1) ^ k) * c + 1 = (c + 1) ^ (i + 1) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have e : (c + 1) ^ (i + 1 + 1) = (c + 1) ^ (i + 1) * (c + 1) := pow_succ _ _
    rw [Finset.sum_range_succ, e]
    nlinarith [ih]

lemma geom (p : ℕ) (hp : 1 ≤ p) (i : ℕ) : (∑ k ∈ range (i + 1), p ^ k) * (p - 1) + 1 = p ^ (i + 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by omega⟩
  simpa using geom' c i

/-- The abundancy bound: `σ(n) * ∏ (p - 1) ≤ n * ∏ p` over the primes dividing `n`. -/
lemma sigma_bound (n : ℕ) :
    sigma 1 n * ∏ p ∈ n.primeFactors, (p - 1) ≤ n * ∏ p ∈ n.primeFactors, p := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton, Finset.prod_singleton,
      sigma_one_apply_prime_pow hp]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h := geom p hp.one_lt.le (j + 1)
    have h2 : p ^ (j + 1 + 1) = p ^ (j + 1) * p := pow_succ p (j + 1)
    omega
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [isMultiplicative_sigma.map_mul_of_coprime hab, hab.primeFactors_mul,
      Finset.prod_union hab.disjoint_primeFactors, Finset.prod_union hab.disjoint_primeFactors]
    calc sigma 1 a * sigma 1 b * ((∏ p ∈ a.primeFactors, (p - 1)) * ∏ p ∈ b.primeFactors, (p - 1))
        = (sigma 1 a * ∏ p ∈ a.primeFactors, (p - 1)) *
            (sigma 1 b * ∏ p ∈ b.primeFactors, (p - 1)) := by ring
      _ ≤ (a * ∏ p ∈ a.primeFactors, p) * (b * ∏ p ∈ b.primeFactors, p) :=
          Nat.mul_le_mul iha ihb
      _ = a * b * ((∏ p ∈ a.primeFactors, p) * ∏ p ∈ b.primeFactors, p) := by ring

theorem few_primes (b : ℕ) (hb : 1 < b) (hodd : Odd b) (hc : b.primeFactors.card ≤ 2) :
    sigma 1 b ≠ 2 * b := by
  intro hs
  have hbound := sigma_bound b
  rw [hs] at hbound
  have hkey : 2 * ∏ p ∈ b.primeFactors, (p - 1) ≤ ∏ p ∈ b.primeFactors, p := by
    have h2 : b * (2 * ∏ p ∈ b.primeFactors, (p - 1)) ≤ b * ∏ p ∈ b.primeFactors, p := by
      calc b * (2 * ∏ p ∈ b.primeFactors, (p - 1)) = 2 * b * ∏ p ∈ b.primeFactors, (p - 1) := by ring
        _ ≤ _ := hbound
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  have hge : ∀ p ∈ b.primeFactors, 3 ≤ p ∧ p % 2 = 1 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpo : p % 2 = 1 := by
      obtain ⟨c, hcb⟩ := hodd
      obtain ⟨d, hd⟩ := hpd
      by_contra hne
      have hpe : p % 2 = 0 := by omega
      have : (p * d) % 2 = 0 := by rw [Nat.mul_mod, hpe]; simp
      omega
    have h2 := hpp.two_le
    exact ⟨by omega, hpo⟩
  have hcard : b.primeFactors.card = 0 ∨ b.primeFactors.card = 1 ∨ b.primeFactors.card = 2 := by
    omega
  rcases hcard with h0 | h1 | h2
  · rw [Finset.card_eq_zero, Nat.primeFactors_eq_empty] at h0
    omega
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
    have hp3 := hge p (by rw [hp]; exact Finset.mem_singleton_self p)
    rw [hp, Finset.prod_singleton, Finset.prod_singleton] at hkey
    omega
  · obtain ⟨p, q, hpq, hp⟩ := Finset.card_eq_two.mp h2
    have hp3 := hge p (by rw [hp]; simp)
    have hq3 := hge q (by rw [hp]; simp)
    rw [hp, Finset.prod_pair hpq, Finset.prod_pair hpq] at hkey
    obtain ⟨x, rfl⟩ : ∃ x, p = x + 3 := ⟨p - 3, by omega⟩
    obtain ⟨y, rfl⟩ : ∃ y, q = y + 3 := ⟨q - 3, by omega⟩
    simp only [show x + 3 - 1 = x + 2 by omega, show y + 3 - 1 = y + 2 by omega] at hkey
    have hxy2 : 2 ≤ x ∨ 2 ≤ y := by omega
    rcases hxy2 with h | h <;> nlinarith [Nat.zero_le (x * y)]

end OMA.A17666

theorem OMA.solution : OMA.R_OeisA17666_conjecture_R1_H1_R1.H1 := by
  intro b hb hodd hc
  exact OMA.A17666.few_primes b hb hodd hc
