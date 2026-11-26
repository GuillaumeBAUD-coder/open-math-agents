import OMAReductions.R_Erdos420_erdos_420_parts_i_R1

-- Step Erdos420.erdos_420.parts.i.R1.H2: hypothesis H2 of reduction Erdos420.erdos_420.parts.i.R1
-- Credit: @Ronandt
-- H2 := ∀ a b p s : ℕ, p.Prime → 0 < s → s < p → a < s * p → s * p ≤ b → (s + 1) * (σ 0 a.factorial) ≤ s * (σ 0 b.factorial)

open scoped ArithmeticFunction.sigma

theorem OMA.solution : OMA.R_Erdos420_erdos_420_parts_i_R1.H2 := by
  intro a b p s hp _hs hsp ha hb
  let ea := a.factorial.factorization p
  let ua := ordCompl[p] a.factorial
  let eb := b.factorial.factorization p
  let ub := ordCompl[p] b.factorial
  have ha0 : a.factorial ≠ 0 := Nat.factorial_ne_zero a
  have hb0 : b.factorial ≠ 0 := Nat.factorial_ne_zero b
  have hsa : p ^ ea * ua = a.factorial := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hsb : p ^ eb * ub = b.factorial := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hca : p.Coprime ua := Nat.coprime_ordCompl hp ha0
  have hcb : p.Coprime ub := Nat.coprime_ordCompl hp hb0
  have hsig_a : σ 0 a.factorial = (ea + 1) * σ 0 ua := by
    rw [← hsa, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hca.pow_left ea),
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  have hsig_b : σ 0 b.factorial = (eb + 1) * σ 0 ub := by
    rw [← hsb, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcb.pow_left eb),
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  have hab_dvd : a.factorial ∣ b.factorial := Nat.factorial_dvd_factorial (by omega)
  have hua_dvd_a : ua ∣ a.factorial := ⟨p ^ ea, by rw [← hsa, Nat.mul_comm]⟩
  have hua_dvd_b : ua ∣ p ^ eb * ub := by
    rw [hsb]
    exact hua_dvd_a.trans hab_dvd
  have hua_dvd_ub : ua ∣ ub :=
    Nat.Coprime.dvd_of_dvd_mul_left (hca.pow_left eb).symm hua_dvd_b
  have hub0 : ub ≠ 0 := by
    intro h
    apply hb0
    rw [← hsb, h, Nat.mul_zero]
  have hσu : σ 0 ua ≤ σ 0 ub := by
    simp only [ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card (Nat.divisors_subset_of_dvd hub0 hua_dvd_ub)
  have hval_sp : (s * p).factorial.factorization p = s := by
    rw [Nat.mul_comm s p, Nat.factorization_factorial_mul hp,
      Nat.factorization_factorial_eq_zero_of_lt hsp, Nat.zero_add]
  have heb : s ≤ eb := by
    have h := (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero (s * p)) hb0).2
      (Nat.factorial_dvd_factorial hb) p
    rwa [hval_sp] at h
  have hpa_dvd : p * a.factorial ∣ (s * p).factorial := by
    obtain ⟨t, ht⟩ : ∃ t : ℕ, s * p = t + 1 := ⟨s * p - 1, by omega⟩
    rw [ht, Nat.factorial_succ]
    exact Nat.mul_dvd_mul (by rw [← ht]; exact dvd_mul_left p s)
      (Nat.factorial_dvd_factorial (by omega))
  have hea : ea + 1 ≤ s := by
    have h := (Nat.factorization_le_iff_dvd (Nat.mul_ne_zero hp.ne_zero ha0)
      (Nat.factorial_ne_zero (s * p))).2 hpa_dvd p
    rw [Nat.factorization_mul hp.ne_zero ha0, Finsupp.add_apply, hp.factorization_self,
      hval_sp] at h
    simpa [ea, Nat.add_comm] using h
  have hcoeff : (s + 1) * (ea + 1) ≤ s * (eb + 1) := by
    calc
      (s + 1) * (ea + 1) ≤ (s + 1) * s := Nat.mul_le_mul_left (s + 1) hea
      _ = s * (s + 1) := Nat.mul_comm (s + 1) s
      _ ≤ s * (eb + 1) := Nat.mul_le_mul_left s (Nat.succ_le_succ heb)
  rw [hsig_a, hsig_b, ← Nat.mul_assoc, ← Nat.mul_assoc]
  exact Nat.mul_le_mul hcoeff hσu
