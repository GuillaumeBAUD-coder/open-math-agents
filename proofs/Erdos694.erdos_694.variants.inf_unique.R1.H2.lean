import OMAReductions.R_Erdos694_erdos_694_variants_inf_unique_R1

-- Step Erdos694.erdos_694.variants.inf_unique.R1.H2: hypothesis H2 of reduction Erdos694.erdos_694.variants.inf_unique.R1
-- Credit: @loremcdmx
-- H2 := ∀ n p : ℕ, 0 < n → p.Prime → n + 1 < p →     (∀ m : ℕ, Nat.totient m = n → Nat.totient (p * m) = n * (p - 1)) ∧     ∀ x : ℕ, Nat.totient x = n * (p - 1) → p ∣ x →       ∃ m : ℕ, Nat.totient m = n ∧ x = p * m

namespace OMA.Aux

theorem not_dvd_aux (n p m : ℕ) (hn : 0 < n) (hp : p.Prime) (hb : n + 1 < p)
    (hm : Nat.totient m = n) : ¬ p ∣ m := by
  intro h
  have h1 := Nat.totient_dvd_of_dvd h
  rw [Nat.totient_prime hp, hm] at h1
  have := Nat.le_of_dvd hn h1
  omega

end OMA.Aux

theorem OMA.solution : OMA.R_Erdos694_erdos_694_variants_inf_unique_R1.H2 := by
  intro n p hn hp hb
  refine ⟨?_, ?_⟩
  · intro m hm
    have hc : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 (OMA.Aux.not_dvd_aux n p m hn hp hb hm)
    rw [Nat.totient_mul hc, Nat.totient_prime hp, hm]
    exact Nat.mul_comm _ _
  · intro x hx hpx
    obtain ⟨m, rfl⟩ := hpx
    have hp1 : 0 < p - 1 := by have := hp.two_le; omega
    by_cases hpm : p ∣ m
    · exfalso
      rw [Nat.totient_mul_of_prime_of_dvd hp hpm] at hx
      have h2 : p ∣ n * (p - 1) := ⟨_, hx.symm⟩
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h | h
      · have := Nat.le_of_dvd hn h; omega
      · have := Nat.le_of_dvd hp1 h; omega
    · have hc : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
      rw [Nat.totient_mul hc, Nat.totient_prime hp] at hx
      refine ⟨m, ?_, rfl⟩
      have : (p - 1) * Nat.totient m = (p - 1) * n := by rw [hx, Nat.mul_comm]
      exact Nat.eq_of_mul_eq_mul_left hp1 this
