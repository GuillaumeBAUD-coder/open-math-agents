import OMAStatements.S_oeis_a133305

namespace OMA.S_oeis_a133305

open Finset

/-!
## Proof of OEIS A133305 (R. J. Mathar's recurrence conjecture)

For `n = 2`, the identity holds by direct computation (`a 0 = 1`, `a 1 = 5`, `a 2 = 45`).
For `n ≥ 3`, let
`F n i = (n.choose i : ℚ) * (n.choose (i + 1) : ℚ) * 4 ^ i * 5 ^ (n - i) / n` (for `i < n`, else `0`),
so `a n = ∑ i ∈ range n, F n i`, and define the Zeilberger certificate
`G n k = P(n, k) * C(n - 1, k - 1) * C(n - 1, k) * 4 ^ (k - 1) * 5 ^ (n - k - 1) / (n - 1)^2`
for `1 ≤ k < n` (and `0` otherwise), where
`P(n, k) = -4 * k ^ 2 + (48 * n - 44) * k + (-64 * n ^ 2 + 84 * n - 20)`.
For every `n ≥ 3` and every `i < n`,
`(n + 1) * F n i + 9 * (-2 * n + 1) * F (n - 1) i + (n - 2) * F (n - 2) i = G n (i + 1) - G n i`.
Summing over `i ∈ range n` telescopes to `G n n - G n 0 = 0`.
-/

private def F (n i : ℕ) : ℚ :=
  if n = 0 ∨ n ≤ i then 0
  else (n.choose i : ℚ) * (n.choose (i + 1) : ℚ) * (4 : ℚ) ^ i * (5 : ℚ) ^ (n - i) / (n : ℚ)

private def G (n k : ℕ) : ℚ :=
  if k = 0 ∨ n ≤ k then 0
  else
    ((-4 * (k : ℚ) ^ 2 + (48 * (n : ℚ) - 44) * (k : ℚ) + (-64 * (n : ℚ) ^ 2 + 84 * (n : ℚ) - 20)) *
      ((n - 1).choose (k - 1) : ℚ) * ((n - 1).choose k : ℚ) *
      (4 : ℚ) ^ (k - 1) * (5 : ℚ) ^ (n - k - 1)) / (((n : ℚ) - 1) ^ 2)

private lemma a_eq_sum_F (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ i ∈ range n, F n i := by
  have hn0 : n ≠ 0 := by omega
  simp only [a, hn0, ↓reduceIte, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hlt : i < n := mem_range.mp hi
  have hnot : ¬ (n = 0 ∨ n ≤ i) := by omega
  simp [F, hnot]

private lemma sum_F_extend (n m : ℕ) (h : n ≤ m) :
    ∑ i ∈ range n, F n i = ∑ i ∈ range m, F n i := by
  refine Finset.sum_subset (range_mono h) ?_
  intro i _ hnot
  have hge : n ≤ i := by simpa [mem_range] using hnot
  simp [F, hge]

private lemma choose_eq_fact (m k : ℕ) (h : k ≤ m) :
    (m.choose k : ℚ) = (m.factorial : ℚ) / ((k.factorial : ℚ) * ((m - k).factorial : ℚ)) := by
  have hnat := Nat.choose_mul_factorial_mul_factorial h
  have hd1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hd2 : ((m - k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - k))
  rw [eq_div_iff (mul_ne_zero hd1 hd2), ← mul_assoc]
  exact_mod_cast hnat

private lemma fact_succ_q (m : ℕ) :
    ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
  rw [Nat.factorial_succ]; push_cast; ring

private lemma zeilberger_step (n i : ℕ) (hn : 3 ≤ n) (hi : i < n) :
    ((n : ℚ) + 1) * F n i + 9 * (-2 * (n : ℚ) + 1) * F (n - 1) i + ((n : ℚ) - 2) * F (n - 2) i =
      G n (i + 1) - G n i := by
  -- Express all binomials in terms of factorials and powers of 4, 5
  -- Handle boundary cases i = 0, i = n - 1, i = n - 2 separately, and interior 1 ≤ i ≤ n - 3 uniformly
  have hn0 : n ≠ 0 := by omega
  have hnm1_0 : n - 1 ≠ 0 := by omega
  have hnm2_0 : n - 2 ≠ 0 := by omega
  have hqn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hqnm1 : ((n : ℚ) - 1) ≠ 0 := by
    have : (1 : ℚ) < (n : ℚ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hqnm2 : ((n : ℚ) - 2) ≠ 0 := by
    have : (2 : ℚ) < (n : ℚ) := by exact_mod_cast (show 2 < n by omega)
    linarith
  by_cases hi0 : i = 0
  · subst hi0
    simp only [F, G, hn0, hnm1_0, hnm2_0, false_or, true_or, ↓reduceIte,
      show ¬ (n ≤ 0) by omega, show ¬ (n - 1 ≤ 0) by omega, show ¬ (n - 2 ≤ 0) by omega,
      show ¬ (n ≤ 1) by omega, show (1 : ℕ) ≠ 0 by omega, zero_add,
      Nat.choose_zero_right, Nat.choose_one_right, Nat.sub_zero, pow_zero, mul_one,
      Nat.sub_self, sub_zero]
    have hp1 : (5 : ℚ) ^ n = 25 * (5 : ℚ) ^ (n - 2) := by
      conv_lhs => rw [show n = (n - 2) + 2 by omega, pow_add]
      ring
    have hp2 : (5 : ℚ) ^ (n - 1) = 5 * (5 : ℚ) ^ (n - 2) := by
      conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega, pow_add]
      ring
    have hsub : n - 1 - 1 = n - 2 := by omega
    rw [hsub, hp1, hp2]
    have hcast1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have hcast2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hcast1, hcast2]
    field_simp [hqn, hqnm1, hqnm2]
    ring
  · by_cases hin1 : i = n - 1
    · subst hin1
      have hnot_n : ¬ (n = 0 ∨ n ≤ n - 1) := by omega
      have hle1 : n - 1 ≤ n - 1 := le_refl _
      have hle2 : n - 2 ≤ n - 1 := by omega
      have hnot_g : ¬ (n - 1 = 0 ∨ n ≤ n - 1) := by omega
      simp only [F, G, hnot_n, hle1, hle2, hnot_g, or_true, ↓reduceIte,
        show n - 1 + 1 = n by omega, le_refl n, Nat.choose_self,
        show n - (n - 1) = 1 by omega, show n - 1 - 1 = n - 2 by omega,
        pow_one, mul_zero, add_zero, zero_sub]
      have hc_n_nm1 : (n.choose (n - 1) : ℚ) = (n : ℚ) := by
        rw [Nat.choose_symm (show 1 ≤ n by omega), Nat.choose_one_right]
      have hc_nm1 : ((n - 1).choose (n - 2) : ℚ) = (n : ℚ) - 1 := by
        have hsym : (n - 1).choose (n - 2) = (n - 1).choose 1 := by
          rw [show n - 2 = (n - 1) - 1 by omega, Nat.choose_symm (show 1 ≤ n - 1 by omega)]
        rw [hsym, Nat.choose_one_right, Nat.cast_sub (by omega)]
        simp
      have hp4 : (4 : ℚ) ^ (n - 1) = 4 * (4 : ℚ) ^ (n - 2) := by
        conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega, pow_add]
        ring
      have hcast1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [hc_n_nm1, hc_nm1, hp4, hcast1]
      field_simp [hqn, hqnm1]
      ring
    · by_cases hin2 : i = n - 2
      · subst hin2
        have hnot_n : ¬ (n = 0 ∨ n ≤ n - 2) := by omega
        have hnot_n1 : ¬ (n - 1 = 0 ∨ n - 1 ≤ n - 2) := by omega
        have hle2 : n - 2 ≤ n - 2 := le_refl _
        have hnot_g1 : ¬ (n - 2 + 1 = 0 ∨ n ≤ n - 2 + 1) := by omega
        have hnot_g0 : ¬ (n - 2 = 0 ∨ n ≤ n - 2) := by omega
        simp only [F, G, hnot_n, hnot_n1, hle2, hnot_g1, hnot_g0, or_true, ↓reduceIte]
        have heq_sub4 : n - (n - 2 + 1) - 1 = 0 := by omega
        have heq_sub6 : n - 2 + 1 - 1 = n - 2 := by omega
        have heq_sub1 : n - 2 + 1 = n - 1 := by omega
        have heq_sub2 : n - (n - 2) = 2 := by omega
        have heq_sub3 : n - 1 - (n - 2) = 1 := by omega
        rw [heq_sub4, heq_sub6, heq_sub1, heq_sub2, heq_sub3]
        have hc_n_nm2 : (n.choose (n - 2) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
          rw [Nat.choose_symm (show 2 ≤ n by omega), Nat.choose_two_right]
          have h2 : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
          obtain ⟨t, ht⟩ := h2
          rw [ht, Nat.mul_div_cancel_left t (by omega)]
          have : (2 : ℚ) * (t : ℚ) = (n : ℚ) * ((n : ℚ) - 1) := by
            have hcast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
            rw [← hcast]
            exact_mod_cast ht.symm
          linarith
        have hc_n_nm1 : (n.choose (n - 1) : ℚ) = (n : ℚ) := by
          rw [Nat.choose_symm (show 1 ≤ n by omega), Nat.choose_one_right]
        have hc_nm1_nm2 : ((n - 1).choose (n - 2) : ℚ) = (n : ℚ) - 1 := by
          have hsym : (n - 1).choose (n - 2) = (n - 1).choose 1 := by
            rw [show n - 2 = (n - 1) - 1 by omega, Nat.choose_symm (show 1 ≤ n - 1 by omega)]
          rw [hsym, Nat.choose_one_right, Nat.cast_sub (by omega)]
          simp
        have hc_nm1_nm3 : ((n - 1).choose (n - 2 - 1) : ℚ) = ((n : ℚ) - 1) * ((n : ℚ) - 2) / 2 := by
          have hsym : (n - 1).choose (n - 2 - 1) = (n - 1).choose 2 := by
            rw [show n - 2 - 1 = (n - 1) - 2 by omega, Nat.choose_symm (show 2 ≤ n - 1 by omega)]
          rw [hsym, Nat.choose_two_right]
          have h2 : 2 ∣ (n - 1) * (n - 1 - 1) := (Nat.even_mul_pred_self (n - 1)).two_dvd
          obtain ⟨t, ht⟩ := h2
          rw [ht, Nat.mul_div_cancel_left t (by omega)]
          have : (2 : ℚ) * (t : ℚ) = ((n : ℚ) - 1) * ((n : ℚ) - 2) := by
            have h1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
            have h2' : ((n - 1 - 1 : ℕ) : ℚ) = (n : ℚ) - 2 := by
              rw [show n - 1 - 1 = n - 2 by omega, Nat.cast_sub (by omega)]; simp
            rw [← h1, ← h2']
            exact_mod_cast ht.symm
          linarith
        have hp4 : (4 : ℚ) ^ (n - 2) = 4 * (4 : ℚ) ^ (n - 2 - 1) := by
          conv_lhs => rw [show n - 2 = (n - 2 - 1) + 1 by omega, pow_add]
          ring
        have hcast1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
        have hcast2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
        rw [hc_n_nm2, hc_n_nm1, hc_nm1_nm2, hc_nm1_nm3, Nat.choose_self, hp4, hcast1, hcast2]
        field_simp [hqn, hqnm1]
        ring
      · -- Interior case: 1 ≤ i ≤ n - 3! Every term is nonzero and all factorials relate cleanly.
        have hi1 : 1 ≤ i := by omega
        have hi3 : i + 3 ≤ n := by omega
        have hnot_n : ¬ (n = 0 ∨ n ≤ i) := by omega
        have hnot_n1 : ¬ (n - 1 = 0 ∨ n - 1 ≤ i) := by omega
        have hnot_n2 : ¬ (n - 2 = 0 ∨ n - 2 ≤ i) := by omega
        have hnot_g1 : ¬ (i + 1 = 0 ∨ n ≤ i + 1) := by omega
        have hnot_g0 : ¬ (i = 0 ∨ n ≤ i) := by omega
        simp only [F, G, hnot_n, hnot_n1, hnot_n2, hnot_g1, hnot_g0, ↓reduceIte]
        have he5 : i + 1 - 1 = i := by omega
        rw [he5]
        -- Rewrite all binomial coefficients via choose_eq_fact
        rw [choose_eq_fact n i (by omega), choose_eq_fact n (i + 1) (by omega),
          choose_eq_fact (n - 1) i (by omega), choose_eq_fact (n - 1) (i + 1) (by omega),
          choose_eq_fact (n - 2) i (by omega), choose_eq_fact (n - 2) (i + 1) (by omega),
          choose_eq_fact (n - 1) (i - 1) (by omega)]
        have he1 : n - (i + 1) = n - 1 - i := by omega
        have he2 : n - 1 - (i + 1) = n - 2 - i := by omega
        have he3 : n - 2 - (i + 1) = n - i - 3 := by omega
        have he4 : n - 1 - (i - 1) = n - i := by omega
        rw [he1, he2, he3, he4]
        set A := ((n - 2).factorial : ℚ)
        set B := ((i - 1).factorial : ℚ)
        set C := ((n - i - 3).factorial : ℚ)
        have hA : A ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hB : B ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hC : C ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hqi : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hqi1 : ((i : ℚ) + 1) ≠ 0 := by positivity
        have hqni1 : ((n : ℚ) - (i : ℚ) - 1) ≠ 0 := by
          have : ((i + 1 : ℕ) : ℚ) < (n : ℚ) := by exact_mod_cast (show i + 1 < n by omega)
          push_cast at this; linarith
        have hqni2 : ((n : ℚ) - (i : ℚ) - 2) ≠ 0 := by
          have : ((i + 2 : ℕ) : ℚ) < (n : ℚ) := by exact_mod_cast (show i + 2 < n by omega)
          push_cast at this; linarith
        have hqni0 : ((n : ℚ) - (i : ℚ)) ≠ 0 := by
          have : (i : ℚ) < (n : ℚ) := by exact_mod_cast (show i < n by omega)
          linarith
        have hcast_n1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
        have hcast_n2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
        have hcast_i1 : ((i - 1 : ℕ) : ℚ) = (i : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
        have hf_nm1 : ((n - 1).factorial : ℚ) = ((n : ℚ) - 1) * A := by
          rw [show n - 1 = (n - 2) + 1 by omega, fact_succ_q, hcast_n2]
          ring
        have hf_n : (n.factorial : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * A := by
          conv_lhs => rw [show n = (n - 1) + 1 by omega, fact_succ_q]
          rw [hf_nm1, hcast_n1]
          ring
        have hf_i : (i.factorial : ℚ) = (i : ℚ) * B := by
          conv_lhs => rw [show i = (i - 1) + 1 by omega, fact_succ_q]
          rw [hcast_i1]
          ring
        have hf_i1 : ((i + 1).factorial : ℚ) = ((i : ℚ) + 1) * (i : ℚ) * B := by
          rw [fact_succ_q, hf_i]; ring
        have hf_ni2 : ((n - 2 - i).factorial : ℚ) = ((n : ℚ) - (i : ℚ) - 2) * C := by
          rw [show n - 2 - i = (n - i - 3) + 1 by omega, fact_succ_q,
            Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
          push_cast; ring
        have hf_ni1 : ((n - 1 - i).factorial : ℚ) =
            ((n : ℚ) - (i : ℚ) - 1) * ((n : ℚ) - (i : ℚ) - 2) * C := by
          rw [show n - 1 - i = (n - 2 - i) + 1 by omega, fact_succ_q, hf_ni2,
            Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
          push_cast; ring
        have hf_ni0 : ((n - i).factorial : ℚ) =
            ((n : ℚ) - (i : ℚ)) * ((n : ℚ) - (i : ℚ) - 1) * ((n : ℚ) - (i : ℚ) - 2) * C := by
          rw [show n - i = (n - 1 - i) + 1 by omega, fact_succ_q, hf_ni1,
            Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
          push_cast; ring
        have hp4_i : (4 : ℚ) ^ i = 4 * (4 : ℚ) ^ (i - 1) := by
          conv_lhs => rw [show i = (i - 1) + 1 by omega, pow_add]
          ring
        have hp5_n : (5 : ℚ) ^ (n - i) = 25 * (5 : ℚ) ^ (n - i - 2) := by
          conv_lhs => rw [show n - i = (n - i - 2) + 2 by omega, pow_add]
          ring
        have hp5_n1 : (5 : ℚ) ^ (n - 1 - i) = 5 * (5 : ℚ) ^ (n - i - 2) := by
          conv_lhs => rw [show n - 1 - i = (n - i - 2) + 1 by omega, pow_add]
          ring
        have hp5_n2 : (5 : ℚ) ^ (n - 2 - i) = (5 : ℚ) ^ (n - i - 2) := by
          congr 1; omega
        have hp5_g1 : (5 : ℚ) ^ (n - 1 - i - 1) = (5 : ℚ) ^ (n - i - 2) := by
          congr 1; omega
        have hp5_g0 : (5 : ℚ) ^ (n - i - 1) = 5 * (5 : ℚ) ^ (n - i - 2) := by
          conv_lhs => rw [show n - i - 1 = (n - i - 2) + 1 by omega, pow_add]
          ring
        rw [hf_n, hf_nm1, hf_i1, hf_i, hf_ni0, hf_ni1, hf_ni2,
          hp4_i, hp5_n, hp5_n1, hp5_n2, hp5_g1, hp5_g0, hcast_n1, hcast_n2]
        push_cast
        field_simp [hA, hB, hC, hqn, hqnm1, hqnm2, hqi, hqi1, hqni0, hqni1, hqni2]
        ring

private lemma main_proof : ∀ n : ℕ, 2 ≤ n →
    ((n : ℚ) + 1) * a n + 9 * (-2 * (n : ℚ) + 1) * a (n - 1) + ((n : ℚ) - 2) * a (n - 2) = 0 := by
  intro n hn
  by_cases hn2 : n = 2
  · subst hn2
    norm_num [a, Finset.sum_range_succ]
  · have hn3 : 3 ≤ n := by omega
    rw [a_eq_sum_F n (by omega), a_eq_sum_F (n - 1) (by omega), a_eq_sum_F (n - 2) (by omega)]
    rw [sum_F_extend (n - 1) n (by omega), sum_F_extend (n - 2) n (by omega)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hstep : ∑ i ∈ range n,
        (((n : ℚ) + 1) * F n i + 9 * (-2 * (n : ℚ) + 1) * F (n - 1) i + ((n : ℚ) - 2) * F (n - 2) i) =
        ∑ i ∈ range n, (G n (i + 1) - G n i) :=
      Finset.sum_congr rfl fun i hi => zeilberger_step n i hn3 (mem_range.mp hi)
    rw [hstep, Finset.sum_range_sub (G n) n]
    simp [G]

end OMA.S_oeis_a133305

theorem OMA.solution : type_of% @OMA.S_oeis_a133305.main :=
  OMA.S_oeis_a133305.main_proof
