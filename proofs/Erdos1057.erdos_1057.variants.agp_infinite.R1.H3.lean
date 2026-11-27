import OMAReductions.R_Erdos1057_erdos_1057_variants_agp_infinite_R1
import Mathlib

-- Step Erdos1057.erdos_1057.variants.agp_infinite.R1.H3: hypothesis H3 of reduction Erdos1057.erdos_1057.variants.agp_infinite.R1
-- Credit: @ivillar
--
-- Korselt's criterion (sufficiency): for b coprime to n and each prime p | n, Fermat gives
-- b^(p-1) = 1 in ZMod p, hence b^(n-1) = 1 since (p - 1) | (n - 1); as n is squarefree it is the
-- product of its prime factors, all of which divide b^(n-1) - 1.

theorem OMA.solution : OMA.R_Erdos1057_erdos_1057_variants_agp_infinite_R1.H3 := by
  unfold OMA.R_Erdos1057_erdos_1057_variants_agp_infinite_R1.H3
  intro n hn hnp hsq hdvd b hb hcop
  refine ⟨?_, hnp, hn⟩
  unfold Nat.ProbablePrime
  have hpow : 1 ≤ b ^ (n - 1) := Nat.one_le_pow _ _ hb
  have key : ∀ p ∈ n.primeFactors, p ∣ b ^ (n - 1) - 1 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    have := Fact.mk hpp
    obtain ⟨k, hk⟩ := hdvd p hpp hpn
    have hb0 : (b : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hpb
      have hg := Nat.dvd_gcd hpn hpb
      rw [Nat.Coprime.gcd_eq_one hcop] at hg
      exact hpp.not_dvd_one hg
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpow, Nat.cast_pow, hk, pow_mul,
      ZMod.pow_card_sub_one_eq_one hb0, one_pow, Nat.cast_one, sub_self]
  have := Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) key
  rwa [Nat.prod_primeFactors_of_squarefree hsq] at this
