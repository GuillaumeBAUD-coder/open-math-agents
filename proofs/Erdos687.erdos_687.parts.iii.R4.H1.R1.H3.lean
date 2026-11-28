import OMAReductions.R_Erdos687_erdos_687_parts_iii_R4_H1_R1

namespace Erdos687H3Aux

open Finset

lemma S_eq (m M : ℕ) (hm : m ≤ M) :
    ∑ k ∈ range m, (ArithmeticFunction.vonMangoldt k : ℝ) * ((m : ℝ) - k) =
    ∑ k ∈ range M, (ArithmeticFunction.vonMangoldt k : ℝ) * (((m - k : ℕ)) : ℝ) := by
  calc _ = ∑ k ∈ range m, (ArithmeticFunction.vonMangoldt k : ℝ) * (((m - k : ℕ)) : ℝ) :=
        sum_congr rfl (fun k hk => by
          rw [Nat.cast_sub (by simp at hk; omega)])
    _ = _ := sum_subset (range_subset_range.mpr hm) (fun k _ hk => by
          simp at hk; simp [Nat.sub_eq_zero_of_le hk])

lemma second_diff_le (a h : ℕ) (hp : ∀ k, k.Prime → a < k → k < a + 2 * h → False) :
    (∑ k ∈ range (a + 2 * h), (ArithmeticFunction.vonMangoldt k : ℝ) * (((a + 2 * h : ℕ) : ℝ) - k))
    - 2 * (∑ k ∈ range (a + h), (ArithmeticFunction.vonMangoldt k : ℝ) * (((a + h : ℕ) : ℝ) - k))
    + (∑ k ∈ range a, (ArithmeticFunction.vonMangoldt k : ℝ) * ((a : ℝ) - k))
    ≤ (h : ℝ) * (Chebyshev.psi ((a + 2 * h : ℕ) : ℝ) - Chebyshev.theta ((a + 2 * h : ℕ) : ℝ)) := by
  rw [S_eq (a + 2 * h) (a + 2 * h) le_rfl, S_eq (a + h) (a + 2 * h) (by omega),
    S_eq a (a + 2 * h) (by omega), Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast,
    sum_filter]
  set g : ℕ → ℝ := fun k => if ¬ k.Prime then (ArithmeticFunction.vonMangoldt k : ℝ) else 0
    with hg
  have key : ∀ k ∈ range (a + 2 * h),
      (ArithmeticFunction.vonMangoldt k : ℝ) * (((a + 2 * h - k : ℕ)) : ℝ)
      - 2 * ((ArithmeticFunction.vonMangoldt k : ℝ) * (((a + h - k : ℕ)) : ℝ))
      + (ArithmeticFunction.vonMangoldt k : ℝ) * (((a - k : ℕ)) : ℝ) ≤ (h : ℝ) * g k := by
    intro k hk
    simp only [mem_range] at hk
    have hL : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt k := ArithmeticFunction.vonMangoldt_nonneg
    have e1 : ((a + 2 * h - k : ℕ) : ℝ) + ((a - k : ℕ) : ℝ) ≤ h + 2 * ((a + h - k : ℕ) : ℝ) := by
      have : (a + 2 * h - k) + (a - k) ≤ h + 2 * (a + h - k) := by omega
      exact_mod_cast this
    have e0 : 2 * ((a + h - k : ℕ) : ℝ) ≤ ((a + 2 * h - k : ℕ) : ℝ) + ((a - k : ℕ) : ℝ) := by
      have : 2 * (a + h - k) ≤ (a + 2 * h - k) + (a - k) := by omega
      exact_mod_cast this
    by_cases hpk : k.Prime
    · have hka : k ≤ a := by
        by_contra hc
        exact hp k hpk (by omega) hk
      have : ((a + 2 * h - k : ℕ) : ℝ) + ((a - k : ℕ) : ℝ) = 2 * ((a + h - k : ℕ) : ℝ) := by
        have : (a + 2 * h - k) + (a - k) = 2 * (a + h - k) := by omega
        exact_mod_cast this
      simp only [hg, hpk, not_true_eq_false, if_false, mul_zero]
      nlinarith
    · simp only [hg, hpk, not_false_eq_true, if_true]
      nlinarith
  calc _ = ∑ k ∈ range (a + 2 * h),
      ((ArithmeticFunction.vonMangoldt k : ℝ) * (((a + 2 * h - k : ℕ)) : ℝ)
      - 2 * ((ArithmeticFunction.vonMangoldt k : ℝ) * (((a + h - k : ℕ)) : ℝ))
      + (ArithmeticFunction.vonMangoldt k : ℝ) * (((a - k : ℕ)) : ℝ)) := by
        rw [sum_add_distrib, sum_sub_distrib, mul_sum]
    _ ≤ ∑ k ∈ range (a + 2 * h), (h : ℝ) * g k := sum_le_sum key
    _ = (h : ℝ) * ∑ k ∈ range (a + 2 * h), g k := by rw [mul_sum]
    _ ≤ (h : ℝ) * ∑ k ∈ Ioc 0 (a + 2 * h), g k := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rw [← sum_erase (range (a + 2 * h)) (a := 0) (by simp [hg])]
        apply sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [mem_erase, mem_range] at hx
          simp only [mem_Ioc]
          omega
        · intro i _ _
          simp only [hg]
          split_ifs
          · exact le_rfl
          · exact ArithmeticFunction.vonMangoldt_nonneg


lemma floor_cube_le (n : ℕ) (hn : 1 ≤ n) : ⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ ^ 3 ≤ n ^ 2 := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) ^ (33/50 : ℝ) := by positivity
  have h1 : ((⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) ^ (33/50 : ℝ) := Nat.floor_le h0
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : ((n : ℝ) ^ (33/50 : ℝ)) ^ 3 ≤ (n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast (n : ℝ) 2]
    apply Real.rpow_le_rpow_of_exponent_le hn'
    norm_num
  have h3 : ((⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ : ℕ) : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 :=
    le_trans (pow_le_pow_left₀ (Nat.cast_nonneg _) h1 3) h2
  exact_mod_cast h3

lemma analytic (n : ℕ) (hn : 1 ≤ n) (h1000 : (1000 : ℝ) ≤ (n : ℝ) ^ (3/50 : ℝ))
    (x : ℝ) (hx1 : 1 ≤ x) (hx : x ≤ 3 * n) :
    16 * (Real.sqrt x * Real.log x) + 2 ≤ (n : ℝ) ^ (33/50 : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log x ≤ x ^ (1/10 : ℝ) / (1/10) := Real.log_le_rpow_div (by linarith) (by norm_num)
  have hsq : Real.sqrt x = x ^ (1/2 : ℝ) := by rw [Real.sqrt_eq_rpow]
  have hx0 : 0 ≤ x := by linarith
  have e1 : Real.sqrt x * Real.log x ≤ 10 * x ^ (3/5 : ℝ) := by
    have : Real.sqrt x * Real.log x ≤ x ^ (1/2 : ℝ) * (x ^ (1/10 : ℝ) / (1/10)) := by
      rw [hsq]; exact mul_le_mul_of_nonneg_left hlog (by positivity)
    have e : x ^ (1/2 : ℝ) * (x ^ (1/10 : ℝ) / (1/10)) = 10 * x ^ (3/5 : ℝ) := by
      rw [show (3/5 : ℝ) = 1/2 + 1/10 by norm_num, Real.rpow_add' hx0 (by norm_num)]
      ring
    linarith
  have e2 : x ^ (3/5 : ℝ) ≤ 3 * (n : ℝ) ^ (3/5 : ℝ) := by
    calc x ^ (3/5 : ℝ) ≤ (3 * n) ^ (3/5 : ℝ) := Real.rpow_le_rpow hx0 hx (by norm_num)
      _ = (3 : ℝ) ^ (3/5 : ℝ) * (n : ℝ) ^ (3/5 : ℝ) := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 3 * (n : ℝ) ^ (3/5 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (3 : ℝ) ^ (3/5 : ℝ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 3 := Real.rpow_one 3
  have e3 : (n : ℝ) ^ (33/50 : ℝ) = (n : ℝ) ^ (3/5 : ℝ) * (n : ℝ) ^ (3/50 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have e4 : (1 : ℝ) ≤ (n : ℝ) ^ (3/5 : ℝ) := Real.one_le_rpow hn' (by norm_num)
  rw [e3]
  nlinarith

end Erdos687H3Aux

open Filter in
theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R4_H1_R1.H3 := by
  have ev1 := ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/50)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1000 : ℝ))
  filter_upwards [ev1, eventually_ge_atTop 1] with n hn1 hn
  change (1000 : ℝ) ≤ (n : ℝ) ^ (3/50 : ℝ) at hn1
  intro hD
  by_contra hne
  push Not at hne
  have hF3 := Erdos687H3Aux.floor_cube_le n hn
  have hFlow : (n : ℝ) ^ (33/50 : ℝ) < (⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  generalize ⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ = F at hD hF3 hFlow
  have hFn : F ≤ n := by
    by_contra hc
    push Not at hc
    have : n ^ 3 < F ^ 3 := Nat.pow_lt_pow_left hc (by norm_num)
    have : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by norm_num)
    omega
  have hprime : ∀ k, k.Prime → n + 1 < k → k < n + 1 + 2 * (F / 2) → False := by
    intro k hk h1 h2
    have h3 := hne k hk (by omega)
    have : (k - n) ^ 3 ≤ F ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have hdiff := Erdos687H3Aux.second_diff_le (n + 1) (F / 2) hprime
  have hM1 : (1 : ℝ) ≤ ((n + 1 + 2 * (F / 2) : ℕ) : ℝ) := by
    have : 1 ≤ n + 1 + 2 * (F / 2) := by omega
    exact_mod_cast this
  have hM3 : ((n + 1 + 2 * (F / 2) : ℕ) : ℝ) ≤ 3 * n := by
    have : n + 1 + 2 * (F / 2) ≤ 3 * n := by omega
    exact_mod_cast this
  have hbound := Chebyshev.psi_sub_theta_le hM1
  have han := Erdos687H3Aux.analytic n hn hn1 _ hM1 hM3
  have hh : (F : ℝ) ≤ 2 * ((F / 2 : ℕ) : ℝ) + 1 := by
    have : F ≤ 2 * (F / 2) + 1 := by omega
    exact_mod_cast this
  have hh0 : (0 : ℝ) ≤ ((F / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  set hR : ℝ := ((F / 2 : ℕ) : ℝ)
  set P := Chebyshev.psi ((n + 1 + 2 * (F / 2) : ℕ) : ℝ) - Chebyshev.theta ((n + 1 + 2 * (F / 2) : ℕ) : ℝ)
  have hP : P ≤ hR / 8 := by nlinarith
  have := mul_le_mul_of_nonneg_left hP hh0
  nlinarith
