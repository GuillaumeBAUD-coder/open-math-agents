import OMAReductions.R_Erdos931_erdos_931_variants_exists_prime_R1

-- Step Erdos931.erdos_931.variants.exists_prime.R1.H1
-- Credit: @caa1982

open Finset

private lemma prod_Icc_pos (n k : ℕ) : 0 < ∏ i ∈ Icc 1 k, (n + i) :=
  Finset.prod_pos fun i hi => by
    have := (Finset.mem_Icc.mp hi).1
    omega

theorem OMA.solution : OMA.R_Erdos931_erdos_931_variants_exists_prime_R1.H1 := by
  intro k₁ k₂ n₁ n₂ hOrder hEq
  constructor
  · intro q hq hgt hle
    have hj_mem : q - n₂ ∈ Icc 1 k₂ := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hq_dvd2 : q ∣ ∏ j ∈ Icc 1 k₂, (n₂ + j) := by
      have hsub := Finset.dvd_prod_of_mem (fun j => n₂ + j) hj_mem
      rwa [show n₂ + (q - n₂) = q by omega] at hsub
    have hq_pf2 : q ∈ (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hq_dvd2, (prod_Icc_pos n₂ k₂).ne'⟩
    have hq_pf1 : q ∈ (∏ i ∈ Icc 1 k₁, (n₁ + i)).primeFactors := hEq.symm ▸ hq_pf2
    have hq_dvd1 : q ∣ ∏ i ∈ Icc 1 k₁, (n₁ + i) := Nat.dvd_of_mem_primeFactors hq_pf1
    obtain ⟨i, hi_mem, hi_dvd⟩ := (hq.prime.dvd_finset_prod_iff _).mp hq_dvd1
    have hi := Finset.mem_Icc.mp hi_mem
    have hq_le : q ≤ n₁ + i := Nat.le_of_dvd (by omega) hi_dvd
    omega
  · intro q hq_pf1
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hq_pf1
    have hq_dvd1 : q ∣ ∏ i ∈ Icc 1 k₁, (n₁ + i) := Nat.dvd_of_mem_primeFactors hq_pf1
    have hq_dvd2 : q ∣ ∏ j ∈ Icc 1 k₂, (n₂ + j) := Nat.dvd_of_mem_primeFactors (hEq ▸ hq_pf1)
    obtain ⟨i, hi_mem, hi_dvd⟩ := (hq.prime.dvd_finset_prod_iff _).mp hq_dvd1
    obtain ⟨j, hj_mem, hj_dvd⟩ := (hq.prime.dvd_finset_prod_iff _).mp hq_dvd2
    have hi := Finset.mem_Icc.mp hi_mem
    have hj := Finset.mem_Icc.mp hj_mem
    have hdiff_dvd : q ∣ (n₂ + j) - (n₁ + i) := Nat.dvd_sub hj_dvd hi_dvd
    have hdiff_pos : 0 < (n₂ + j) - (n₁ + i) := by omega
    have hq_le : q ≤ (n₂ + j) - (n₁ + i) := Nat.le_of_dvd hdiff_pos hdiff_dvd
    omega
