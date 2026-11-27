import OMAReductions.R_Erdos828_erdos_828_R1
import Mathlib.Tactic

/-! Proof of step H1 of Erdos828.erdos_828.R1 -/

-- Credit: @nijv

theorem OMA.solution : OMA.R_Erdos828_erdos_828_R1.H1 := by
  unfold OMA.R_Erdos828_erdos_828_R1.H1
  intro a ha
  rcases ha with rfl | ⟨m, hmpos, hmdvd, rfl⟩
  · refine Set.infinite_of_injective_forall_mem
      (f := fun j : ℕ => 2 ^ (j + 1))
      (fun i j hij => by
        have h := (Nat.pow_right_inj (by decide : 1 < 2)).mp hij
        omega)
      (fun j => ?_)
    simp only [Set.mem_ofPred_eq, add_zero]
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos j)]
    norm_cast
    exact ⟨2, by simp [pow_succ]⟩
  · have hinf : {p : ℕ | p.Prime ∧ m < p}.Infinite := by
      refine (Nat.infinite_setOfPred_prime.sdiff (Set.finite_le_nat m)).mono ?_
      intro p ⟨hp, hnotle⟩
      exact ⟨hp, Nat.lt_of_not_ge hnotle⟩
    refine (hinf.image (f := fun p => m * p) ?_).mono ?_
    · intro p₁ _ p₂ _ heq
      exact Nat.eq_of_mul_eq_mul_left hmpos heq
    · rintro n ⟨p, ⟨hp, hmp⟩, rfl⟩
      simp only [Set.mem_ofPred_eq]
      have hcop : m.Coprime p := (hp.coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt hmpos hmp)).symm
      rw [Nat.totient_mul hcop, Nat.totient_prime hp]
      have hsub : (m * p : ℕ) + -(m : ℤ) = ((m * (p - 1) : ℕ) : ℤ) := by
        have hp1 : 1 ≤ p := hp.one_le
        zify [hp1]
        ring
      rw [hsub]
      exact_mod_cast mul_dvd_mul_right hmdvd (p - 1)
