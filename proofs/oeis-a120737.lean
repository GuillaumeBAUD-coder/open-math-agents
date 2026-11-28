import OMAStatements.S_oeis_a120737

-- Problem oeis-a120737: for k > 0, if d(k) (the number of divisors) divides rad(k), then rad(k) / d(k) = 1.
-- Upstream: statements/oeis-a120737.lean (declaration OMA.S_oeis_a120737.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: let s be the set of primes dividing k and e_p their exponents, so d(k) is the product of e_p + 1 over s
-- and rad(k) is the product of s. rad(k) is squarefree, so its divisor d(k) is squarefree too. Then the factors
-- e_p + 1 >= 2 are pairwise coprime and each has a prime factor of its own: d(k) has at least |s| distinct prime
-- factors, all dividing rad(k), whose prime factors are exactly the |s| elements of s. So the prime factors of
-- d(k) are exactly s, a squarefree number is the product of its prime factors, hence d(k) = rad(k) and the
-- quotient is 1.

open UniqueFactorizationMonoid

private lemma squarefree_prod_primes_a120737 (s : Finset ℕ) :
    (∀ p ∈ s, p.Prime) → Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp
  | insert a s ha ih =>
    intro hs
    rw [Finset.prod_insert ha, Nat.squarefree_mul_iff]
    have hpa : a.Prime := hs a (Finset.mem_insert_self a s)
    refine ⟨?_, Irreducible.squarefree hpa, ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))⟩
    apply Nat.Coprime.prod_right
    intro q hq
    refine (Nat.coprime_primes hpa (hs q (Finset.mem_insert_of_mem hq))).mpr ?_
    rintro rfl
    exact ha hq

private lemma card_le_card_primeFactors_a120737 (s : Finset ℕ) (f : ℕ → ℕ) :
    (∀ p ∈ s, 2 ≤ f p) → Squarefree (∏ p ∈ s, f p) → s.card ≤ (∏ p ∈ s, f p).primeFactors.card := by
  induction s using Finset.induction_on with
  | empty =>
    intro _ _
    simp
  | insert a s ha ih =>
    intro hf hsq
    rw [Finset.prod_insert ha] at hsq ⊢
    obtain ⟨hcop, _, hsqs⟩ := Nat.squarefree_mul_iff.mp hsq
    rw [Finset.card_insert_of_notMem ha, hcop.primeFactors_mul,
      Finset.card_union_of_disjoint hcop.disjoint_primeFactors]
    have hfa : 1 < f a := hf a (Finset.mem_insert_self a s)
    have h1 : 0 < (f a).primeFactors.card := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hfa)
    have h2 := ih (fun p hp => hf p (Finset.mem_insert_of_mem hp)) hsqs
    omega

private lemma key_a120737 (s : Finset ℕ) (f : ℕ → ℕ) (hs : ∀ p ∈ s, p.Prime) (hf : ∀ p ∈ s, 2 ≤ f p)
    (hdvd : ∏ p ∈ s, f p ∣ ∏ p ∈ s, p) : ∏ p ∈ s, p = ∏ p ∈ s, f p := by
  have hR : Squarefree (∏ p ∈ s, p) := squarefree_prod_primes_a120737 s hs
  have hT : Squarefree (∏ p ∈ s, f p) := Squarefree.squarefree_of_dvd hdvd hR
  have hsub : (∏ p ∈ s, f p).primeFactors ⊆ s := by
    have h := Nat.primeFactors_mono hdvd hR.ne_zero
    rwa [Nat.primeFactors_prod hs] at h
  have hcard := card_le_card_primeFactors_a120737 s f hf hT
  have heq : (∏ p ∈ s, f p).primeFactors = s := Finset.eq_of_subset_of_card_le hsub hcard
  have hprod := Nat.prod_primeFactors_of_squarefree hT
  rw [heq] at hprod
  exact hprod

theorem OMA.solution : type_of% @OMA.S_oeis_a120737.main := by
  intro k hk hdvd
  have hk0 : k ≠ 0 := by omega
  rw [Nat.radical_eq_prod_primeFactors, Nat.card_divisors hk0] at hdvd ⊢
  have hf : ∀ p ∈ k.primeFactors, 2 ≤ k.factorization p + 1 := by
    intro p hp
    have hpos := Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hk0
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  have heq := key_a120737 k.primeFactors (fun p => k.factorization p + 1)
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hf hdvd
  rw [heq]
  exact Nat.div_self (Finset.prod_pos (fun p _ => Nat.succ_pos _))
