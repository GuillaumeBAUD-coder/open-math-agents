import OMAStatements.S_oeis_a345997
import Mathlib

open OMA.S_oeis_a345997 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a345997.main) := by
  intro h
  have hm : a344005 60 = 15 := by
    unfold a344005
    have h15 : (15 : ℕ) ∈ {m : ℕ | 0 < m ∧ 60 ∣ m * (m + 1)} := ⟨by norm_num, by norm_num⟩
    apply le_antisymm (Nat.sInf_le h15)
    apply le_csInf ⟨15, h15⟩
    rintro m ⟨hm0, hmd⟩
    rcases Nat.lt_or_ge m 15 with hlt | hge
    · interval_cases m <;> omega
    · exact hge
  have hg : gpf 60 = 5 := by
    unfold gpf
    apply le_antisymm
    · apply Finset.sup_le
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      obtain ⟨hpp, hpd, -⟩ := hp
      rw [show (60 : ℕ) = 2 * 2 * 3 * 5 by norm_num] at hpd
      rcases (Nat.Prime.dvd_mul hpp).mp hpd with h1 | h1
      · rcases (Nat.Prime.dvd_mul hpp).mp h1 with h2 | h2
        · rcases (Nat.Prime.dvd_mul hpp).mp h2 with h3 | h3
          · exact (Nat.le_of_dvd (by norm_num) h3).trans (by norm_num)
          · exact (Nat.le_of_dvd (by norm_num) h3).trans (by norm_num)
        · exact (Nat.le_of_dvd (by norm_num) h2).trans (by norm_num)
      · exact Nat.le_of_dvd (by norm_num) h1
    · have h5 : (5 : ℕ) ∈ Nat.primeFactors 60 := by
        rw [Nat.mem_primeFactors]
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      exact Finset.le_sup (f := id) h5
  have hf : (60 : ℕ).factorization 5 = 1 := by
    rw [Nat.factorization_def 60 (by norm_num : Nat.Prime 5)]
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [show (60 : ℕ) = 5 * 12 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have ha : a051119 60 = 12 := by
    unfold a051119
    rw [hg, hf]
    norm_num
  rcases h 60 (by norm_num) with h1 | h1 <;> rw [hm, ha] at h1 <;> norm_num at h1
