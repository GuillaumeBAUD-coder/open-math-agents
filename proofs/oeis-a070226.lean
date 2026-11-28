import OMAStatements.S_oeis_a070226
import Mathlib

-- Problem: OEIS A070226. If tau(k) divides rad(k) then rad(k) = tau(k).
-- Proof. Write P for the set of primes of k and f(p) = v_p(k) + 1 >= 2, so that
-- tau(k) = prod_{p in P} f(p) and rad(k) = prod_{p in P} p. Suppose tau | rad.
-- Every prime factor of tau divides rad, hence lies in P. The map p -> least prime factor
-- of f(p) is injective on P: a common prime q of f(p1) and f(p2) with p1 != p2 would give
-- q^2 | f(p1) f(p2) | tau | rad, but rad is a product of distinct primes. So tau has at
-- least |P| prime factors, all inside P, hence exactly the primes of P. Therefore every
-- p in P divides tau, so rad | tau, and rad = tau.

open OMA.S_oeis_a070226

lemma OMA.not_sq_dvd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (q : ℕ) (hq : q.Prime) :
    ¬ q * q ∣ ∏ p ∈ P, p := by
  intro h
  by_cases hqP : q ∈ P
  · rw [← Finset.mul_prod_erase P (fun p => p) hqP] at h
    have h2 : q ∣ ∏ p ∈ P.erase q, p := (Nat.mul_dvd_mul_iff_left hq.pos).mp h
    obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp h2
    have hpP := Finset.mem_of_mem_erase hp
    have hqe : q = p := (Nat.prime_dvd_prime_iff_eq hq (hP p hpP)).mp hqp
    exact (Finset.ne_of_mem_erase hp) hqe.symm
  · have h2 : q ∣ ∏ p ∈ P, p := Dvd.dvd.trans (Dvd.intro _ rfl) h
    obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp h2
    have hqe : q = p := (Nat.prime_dvd_prime_iff_eq hq (hP p hp)).mp hqp
    exact hqP (hqe ▸ hp)

lemma OMA.key (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℕ) (hf2 : ∀ p ∈ P, 2 ≤ f p)
    (hdiv : ∏ p ∈ P, f p ∣ ∏ p ∈ P, p) : ∏ p ∈ P, p = ∏ p ∈ P, f p := by
  have hT0 : (∏ p ∈ P, f p) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    have := hf2 p hp
    omega
  have hfdvd : ∀ p ∈ P, f p ∣ ∏ x ∈ P, f x := fun p hp => Finset.dvd_prod_of_mem f hp
  have hf1 : ∀ p ∈ P, f p ≠ 1 := by
    intro p hp
    have := hf2 p hp
    omega
  have hsub : (∏ p ∈ P, f p).primeFactors ⊆ P := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have h1 : q ∣ ∏ p ∈ P, p := (Nat.dvd_of_mem_primeFactors hq).trans hdiv
    obtain ⟨p, hp, hqp'⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).mp h1
    have hqe : q = p := (Nat.prime_dvd_prime_iff_eq hqp (hP p hp)).mp hqp'
    exact hqe ▸ hp
  have hcard : P.card ≤ (∏ p ∈ P, f p).primeFactors.card := by
    refine Finset.card_le_card_of_injOn (fun p => (f p).minFac) ?_ ?_
    · intro p hp
      exact Nat.mem_primeFactors.mpr
        ⟨Nat.minFac_prime (hf1 p hp), (Nat.minFac_dvd _).trans (hfdvd p hp), hT0⟩
    · intro p1 hp1 p2 hp2 heq
      have heq' : (f p1).minFac = (f p2).minFac := heq
      by_contra hne
      have hq := Nat.minFac_prime (hf1 p1 hp1)
      have h1 : (f p1).minFac ∣ f p1 := Nat.minFac_dvd _
      have h2 : (f p1).minFac ∣ f p2 := by
        rw [heq']
        exact Nat.minFac_dvd _
      have h3 : f p1 * f p2 ∣ ∏ x ∈ P, f x := by
        have hsub2 : ({p1, p2} : Finset ℕ) ⊆ P := by
          intro x hx
          rcases Finset.mem_insert.mp hx with hx | hx
          · rw [hx]
            exact hp1
          · rw [Finset.mem_singleton.mp hx]
            exact hp2
        have h4 := Finset.prod_dvd_prod_of_subset _ _ f hsub2
        rwa [Finset.prod_pair hne] at h4
      exact OMA.not_sq_dvd P hP _ hq (((Nat.mul_dvd_mul h1 h2).trans h3).trans hdiv)
  have heqP : (∏ p ∈ P, f p).primeFactors = P := Finset.eq_of_subset_of_card_le hsub hcard
  have hRT : ∏ p ∈ P, p ∣ ∏ p ∈ P, f p := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (hP p hp).prime
    · intro p hp
      rw [← heqP] at hp
      exact Nat.dvd_of_mem_primeFactors hp
  exact Nat.dvd_antisymm hRT hdiv

theorem OMA.solution : type_of% @OMA.S_oeis_a070226.main := by
  intro k hk hdiv
  have hk0 : k ≠ 0 := by omega
  have htau : tau k = ∏ p ∈ k.primeFactors, (k.factorization p + 1) := Nat.card_divisors hk0
  have hrad : rad k = ∏ p ∈ k.primeFactors, p := rfl
  rw [htau, hrad] at hdiv
  rw [htau, hrad]
  refine OMA.key k.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (fun p => k.factorization p + 1) ?_ hdiv
  intro p hp
  have hpos : 0 < k.factorization p :=
    Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hk0
      (Nat.dvd_of_mem_primeFactors hp)
  omega
