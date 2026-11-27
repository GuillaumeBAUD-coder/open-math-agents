import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1

-- Step Erdos137.erdos_137.variants.perfect_power.R1.H2: hypothesis H2 of reduction Erdos137.erdos_137.variants.perfect_power.R1
-- Credit: @OrangeHeadz

/-!
Informal plan (the small case of Erdős and Selfridge, via Bertrand's postulate).

Assume there is no prime in [k, n + k].
1. Bertrand at k gives a prime q with k < q ≤ 2k. If k ≤ n it would lie in [k, n + k], so n < k.
2. Bertrand at (n + k) / 2 gives a prime p with (n + k) / 2 < p ≤ n + k. Then n + k < 2p, and
   p > n because k > n. So p lies in (n, n + k] and no other element of that interval is a
   multiple of p.
3. The factorization of the product at p is the sum of the factorizations of the factors at
   p, which is 1 for the factor p and 0 for the others.
Mathlib supplies Nat.exists_prime_lt_and_le_two_mul and Nat.factorization_prod.
-/

open Finset

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H2 := by
  unfold OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H2
  intro k n hk hno
  have hnk : n < k := by
    by_contra hcon
    obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul k (by omega)
    exact hno ⟨q, by omega, by omega, hq⟩
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul ((n + k) / 2) (by omega)
  have hpn : n < p := by omega
  have hpk : p ≤ n + k := by omega
  have h2p : n + k < 2 * p := by omega
  refine ⟨p, hp, ?_⟩
  rw [Nat.factorization_prod (fun m hm => by
    have := (mem_Ioc.mp hm).1
    omega), Finsupp.finsetSum_apply, Finset.sum_eq_single p]
  · exact hp.factorization_self
  · intro m hm hmp
    apply Nat.factorization_eq_zero_of_not_dvd
    rintro ⟨t, rfl⟩
    have hm' := mem_Ioc.mp hm
    rcases Nat.lt_or_ge t 2 with ht | ht
    · have ht' : t = 0 ∨ t = 1 := by omega
      rcases ht' with ht' | ht'
      · rw [ht'] at hm'
        simp at hm'
      · rw [ht'] at hmp
        simp at hmp
    · have h1 := Nat.mul_le_mul_left p ht
      omega
  · intro hnot
    exact absurd (mem_Ioc.mpr ⟨hpn, hpk⟩) hnot
