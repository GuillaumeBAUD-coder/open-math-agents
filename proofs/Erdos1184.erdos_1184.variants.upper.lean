import FormalConjectures.ErdosProblems.«1184»

-- Problem: Erdős Problem 1184 — upper
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1184.lean (declaration Erdos1184.erdos_1184.variants.upper)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA1184

lemma prod_Icc_eq_ascFactorial (n : ℕ) :
    ∀ k : ℕ, ∏ i ∈ Finset.Icc 1 k, (n + i) = (n + 1).ascFactorial k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.ascFactorial_succ]
    ring

end OMA1184

theorem OMA.solution : type_of% @Erdos1184.erdos_1184.variants.upper := by
  intro α k n hk hn
  set F := (Finset.Icc 1 k).filter (fun i => k < (n + i).maxPrimeFac) with hF
  have hfeq : Erdos1184.f n k = F.card := rfl
  rw [hfeq]
  have hprime : ∀ i ∈ F, (n + i).maxPrimeFac.Prime := by
    intro i hi
    have hlt := (Finset.mem_filter.mp hi).2
    have hi1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).1
    have h1 : 1 < n + i := by
      by_contra h
      have h' : n + i = 1 := by omega
      rw [h', Nat.maxPrimeFac_one] at hlt
      omega
    exact Nat.prime_maxPrimeFac_of_one_lt _ h1
  have hdvd1 : ∏ i ∈ F, (n + i).maxPrimeFac ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) :=
    (Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => Nat.maxPrimeFac_dvd)).trans
      (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
  have hcop : Nat.Coprime (∏ i ∈ F, (n + i).maxPrimeFac) k.factorial := by
    apply Nat.Coprime.prod_left
    intro i hi
    rw [Nat.Prime.coprime_iff_not_dvd (hprime i hi), Nat.Prime.dvd_factorial (hprime i hi)]
    exact not_le.mpr (Finset.mem_filter.mp hi).2
  have hdvd2 : k.factorial ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) := by
    rw [OMA1184.prod_Icc_eq_ascFactorial]
    exact Nat.factorial_dvd_ascFactorial _ _
  have hmain : (∏ i ∈ F, (n + i).maxPrimeFac) * k.factorial ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd1 hdvd2
  have hpos : 0 < ∏ i ∈ Finset.Icc 1 k, (n + i) :=
    Finset.prod_pos (fun i hi => by simp at hi; omega)
  have hle1 := Nat.le_of_dvd hpos hmain
  have hle2 : (k + 1) ^ F.card ≤ ∏ i ∈ F, (n + i).maxPrimeFac :=
    Finset.pow_card_le_prod _ _ _ (fun i hi => (Finset.mem_filter.mp hi).2)
  have hle3 : ∏ i ∈ Finset.Icc 1 k, (n + i) ≤ (n + k) ^ k := by
    have := Finset.prod_le_pow_card (Finset.Icc 1 k) (fun i => n + i) (n + k)
      (fun i hi => by simp at hi; omega)
    simpa using this
  have hnat : (k + 1) ^ F.card * k.factorial ≤ (n + k) ^ k :=
    le_trans (Nat.mul_le_mul_right _ hle2) (hle1.trans hle3)
  -- real estimates
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlogk : 0 < Real.log k := Real.log_pos (by linarith)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hα : 1 ≤ α := by
    have hkk : (k : ℝ) ≤ (k : ℝ) ^ α := by linarith
    by_contra h
    push_neg at h
    have := Real.rpow_lt_rpow_of_exponent_lt (by linarith : (1 : ℝ) < k) h
    rw [Real.rpow_one] at this
    linarith
  have hnk : (n : ℝ) + k ≤ (k : ℝ) ^ α := by linarith
  have hfpos : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hR : ((k : ℝ) + 1) ^ F.card * (k.factorial : ℝ) ≤ ((k : ℝ) ^ α) ^ k := by
    have h' : (((k + 1) ^ F.card * k.factorial : ℕ) : ℝ) ≤ (((n + k) ^ k : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at h'
    calc _ ≤ ((n : ℝ) + k) ^ k := h'
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hnk k
  have hfact : (k : ℝ) ^ k ≤ k.factorial * Real.exp k := by
    have := Real.pow_div_factorial_le_exp (k : ℝ) (le_of_lt hk0) k
    rw [div_le_iff₀ hfpos] at this
    linarith [mul_comm (k.factorial : ℝ) (Real.exp k)]
  have L1 : F.card * Real.log (k + 1) + Real.log k.factorial ≤ k * (α * Real.log k) := by
    have := Real.log_le_log (by positivity) hR
    rw [Real.log_mul (by positivity) hfpos.ne', Real.log_pow, Real.log_pow,
      Real.log_rpow hk0] at this
    linarith
  have L2 : k * Real.log k ≤ Real.log k.factorial + k := by
    have := Real.log_le_log (by positivity) hfact
    rw [Real.log_mul hfpos.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at this
    linarith
  have L3 : (F.card : ℝ) * Real.log k < (α - 1) * k * Real.log k + k := by
    rcases Nat.eq_zero_or_pos F.card with h0 | h0
    · rw [h0]
      have : 0 ≤ (α - 1) * k * Real.log k :=
        mul_nonneg (mul_nonneg (by linarith) hk0.le) hlogk.le
      simp only [Nat.cast_zero, zero_mul]
      linarith
    · have hlt : Real.log k < Real.log (k + 1) := Real.log_lt_log hk0 (by linarith)
      have hc : (0 : ℝ) < F.card := by exact_mod_cast h0
      have := mul_lt_mul_of_pos_left hlt hc
      nlinarith
  rw [show (k : ℝ) * (α - 1) + k / Real.log k =
      ((α - 1) * k * Real.log k + k) / Real.log k by field_simp]
  rw [lt_div_iff₀ hlogk]
  linarith
