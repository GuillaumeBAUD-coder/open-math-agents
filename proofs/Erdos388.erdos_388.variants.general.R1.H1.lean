import OMAReductions.R_Erdos388_erdos_388_variants_general_R1

-- Step Erdos388.erdos_388.variants.general.R1.H1
-- Credit: @caa1982

open Finset

private lemma prod_Icc_pos (n k : ℕ) : 0 < ∏ i ∈ Icc 1 k, (n + i) :=
  Finset.prod_pos fun i hi => by
    have := (Finset.mem_Icc.mp hi).1
    omega

theorem OMA.solution : OMA.R_Erdos388_erdos_388_variants_general_R1.H1 := by
  intro a b m₁ k₁ m₂ k₂ ha hb hk₁ hk₂ hOrder hEq
  constructor
  · intro hm₂a
    have hmem : k₂ ∈ Icc 1 k₂ := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
    have hdvd : m₂ + k₂ ∣ ∏ j ∈ Icc 1 k₂, (m₂ + j) :=
      Finset.dvd_prod_of_mem (fun j => m₂ + j) hmem
    have hle1 : k₂ ≤ ∏ j ∈ Icc 1 k₂, (m₂ + j) :=
      le_trans (by omega : k₂ ≤ m₂ + k₂) (Nat.le_of_dvd (prod_Icc_pos m₂ k₂) hdvd)
    have hle2 : ∏ j ∈ Icc 1 k₂, (m₂ + j) ≤ b * ∏ j ∈ Icc 1 k₂, (m₂ + j) :=
      Nat.le_mul_of_pos_left _ hb
    have hprod1 : ∏ i ∈ Icc 1 k₁, (m₁ + i) ≤ a ^ k₁ := by
      calc ∏ i ∈ Icc 1 k₁, (m₁ + i)
          ≤ ∏ _i ∈ Icc 1 k₁, a := by
            apply Finset.prod_le_prod'
            intro i hi
            have := (Finset.mem_Icc.mp hi).2
            omega
        _ = a ^ k₁ := by simp
    have hpow : a ^ k₁ ≤ a ^ a := Nat.pow_le_pow_right ha (by omega)
    calc k₂ ≤ b * ∏ j ∈ Icc 1 k₂, (m₂ + j) := hle1.trans hle2
      _ = a * ∏ i ∈ Icc 1 k₁, (m₁ + i) := hEq.symm
      _ ≤ a * a ^ a := Nat.mul_le_mul_left a (hprod1.trans hpow)
  · intro ham₂
    have hfac : ∀ p ∈ (∏ j ∈ Icc 1 k₂, (m₂ + j)).primeFactors, p ≤ m₂ := by
      intro p hp_mem
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hdvd2 : p ∣ ∏ j ∈ Icc 1 k₂, (m₂ + j) := Nat.dvd_of_mem_primeFactors hp_mem
      have hdvd1 : p ∣ a * ∏ i ∈ Icc 1 k₁, (m₁ + i) := by
        rw [hEq]
        exact dvd_mul_of_dvd_right hdvd2 b
      rcases hp.dvd_mul.mp hdvd1 with hpa | hpprod
      · exact (Nat.le_of_dvd ha hpa).trans ham₂
      · obtain ⟨i, hi_mem, hi_dvd⟩ := (hp.prime.dvd_finset_prod_iff _).mp hpprod
        have hi := Finset.mem_Icc.mp hi_mem
        have hple : p ≤ m₁ + i := Nat.le_of_dvd (by omega) hi_dvd
        omega
    refine ⟨?_, hfac⟩
    by_contra hge
    push Not at hge
    obtain ⟨p, hp, hgt, hle2⟩ := Nat.exists_prime_lt_and_le_two_mul m₂ (by omega)
    have hj_mem : p - m₂ ∈ Icc 1 k₂ := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hdvd : p ∣ ∏ j ∈ Icc 1 k₂, (m₂ + j) := by
      have hsub := Finset.dvd_prod_of_mem (fun j => m₂ + j) hj_mem
      rwa [show m₂ + (p - m₂) = p by omega] at hsub
    have hpmem : p ∈ (∏ j ∈ Icc 1 k₂, (m₂ + j)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hdvd, (prod_Icc_pos m₂ k₂).ne'⟩
    have hple : p ≤ m₂ := hfac p hpmem
    omega
