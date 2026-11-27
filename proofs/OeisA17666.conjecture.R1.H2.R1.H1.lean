import OMAReductions.R_OeisA17666_conjecture_R1_H2_R1

-- An odd number b > 1 with sigma(b) = k * b and k >= 3 has at least seven distinct prime factors.
-- Original proof of an elementary fact. The divisor sum satisfies sigma(n) * prod (p - 1) <= n * prod p over
-- the primes dividing n (prime powers by the geometric sum, then multiplicativity). For r distinct odd numbers
-- >= 3 the product of p / (p - 1) is at most (3/2)(5/4)...((2r+1)/(2r)), by induction adding the largest element,
-- which is at least 2r + 1. For r <= 6 that is 135135 / 46080 < 3.
-- This is an elementary case of the open question on odd multiply perfect numbers, not progress on it.

namespace OMA.A17666m

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

/-- For distinct odd numbers `≥ 3`: `∏ p / (p - 1) ≤ ∏_{j < r} (2j + 3) / (2j + 2)`. -/
lemma odd_prod_bound (s : Finset ℕ) :
    (∀ p ∈ s, 3 ≤ p ∧ p % 2 = 1) →
    (∏ j ∈ range s.card, (2 * j + 2)) * ∏ p ∈ s, p ≤
      (∏ j ∈ range s.card, (2 * j + 3)) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    have hans : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hs' : ∀ p ∈ s, 3 ≤ p ∧ p % 2 = 1 := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have ha3 := hs a (Finset.mem_insert_self a s)
    have ih' := ih hs'
    have hmap : ∀ x ∈ s, (x - 3) / 2 ∈ range ((a - 3) / 2) := by
      intro x hx
      have h1 := hs' x hx
      have h2 := ha x hx
      rw [Finset.mem_range]
      omega
    have hinj : Set.InjOn (fun x : ℕ => (x - 3) / 2) (s : Set ℕ) := by
      intro x hx y hy hxy
      have h1 := hs' x hx
      have h2 := hs' y hy
      simp only at hxy
      omega
    have hcard : s.card ≤ (a - 3) / 2 := by
      have h := Finset.card_le_card_of_injOn (fun x : ℕ => (x - 3) / 2) hmap hinj
      rwa [Finset.card_range] at h
    have hstep : (2 * s.card + 2) * a ≤ (2 * s.card + 3) * (a - 1) := by
      obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have h3 : 2 * s.card + 2 ≤ c := by omega
      nlinarith
    rw [Finset.card_insert_of_notMem hans, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_insert hans, Finset.prod_insert hans]
    calc (∏ j ∈ range s.card, (2 * j + 2)) * (2 * s.card + 2) * (a * ∏ p ∈ s, p)
        = ((∏ j ∈ range s.card, (2 * j + 2)) * ∏ p ∈ s, p) * ((2 * s.card + 2) * a) := by ring
      _ ≤ ((∏ j ∈ range s.card, (2 * j + 3)) * ∏ p ∈ s, (p - 1)) * ((2 * s.card + 3) * (a - 1)) :=
          Nat.mul_le_mul ih' hstep
      _ = (∏ j ∈ range s.card, (2 * j + 3)) * (2 * s.card + 3) * ((a - 1) * ∏ p ∈ s, (p - 1)) := by
          ring

theorem few_primes_multi (b k : ℕ) (hb : 1 < b) (hodd : Odd b) (hk : 3 ≤ k)
    (hc : b.primeFactors.card ≤ 6) : sigma 1 b ≠ k * b := by
  intro hs
  have hbound := sigma_bound b
  rw [hs] at hbound
  have hkey : k * ∏ p ∈ b.primeFactors, (p - 1) ≤ ∏ p ∈ b.primeFactors, p := by
    have h2 : b * (k * ∏ p ∈ b.primeFactors, (p - 1)) ≤ b * ∏ p ∈ b.primeFactors, p := by
      calc b * (k * ∏ p ∈ b.primeFactors, (p - 1)) = k * b * ∏ p ∈ b.primeFactors, (p - 1) := by ring
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
  have hodd' := odd_prod_bound b.primeFactors hge
  have hQ : 0 < ∏ p ∈ b.primeFactors, (p - 1) :=
    Finset.prod_pos fun p hp => by have := (hge p hp).1; omega
  have hfinal : k * (∏ j ∈ range b.primeFactors.card, (2 * j + 2)) ≤
      ∏ j ∈ range b.primeFactors.card, (2 * j + 3) := by
    have h3 : (∏ p ∈ b.primeFactors, (p - 1)) * (k * ∏ j ∈ range b.primeFactors.card, (2 * j + 2)) ≤
        (∏ p ∈ b.primeFactors, (p - 1)) * ∏ j ∈ range b.primeFactors.card, (2 * j + 3) := by
      calc (∏ p ∈ b.primeFactors, (p - 1)) * (k * ∏ j ∈ range b.primeFactors.card, (2 * j + 2))
          = (∏ j ∈ range b.primeFactors.card, (2 * j + 2)) * (k * ∏ p ∈ b.primeFactors, (p - 1)) := by
            ring
        _ ≤ (∏ j ∈ range b.primeFactors.card, (2 * j + 2)) * ∏ p ∈ b.primeFactors, p :=
            Nat.mul_le_mul_left _ hkey
        _ ≤ (∏ j ∈ range b.primeFactors.card, (2 * j + 3)) * ∏ p ∈ b.primeFactors, (p - 1) := hodd'
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left h3 hQ
  generalize b.primeFactors.card = r at hc hfinal
  interval_cases r <;> simp [Finset.prod_range_succ] at hfinal <;> omega

end OMA.A17666m

theorem OMA.solution : OMA.R_OeisA17666_conjecture_R1_H2_R1.H1 := by
  intro b k hb hodd hk hc
  exact OMA.A17666m.few_primes_multi b k hb hodd hk hc
