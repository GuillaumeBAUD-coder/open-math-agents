import OMAStatements.S_oeis_a280411

-- Problem: A280411: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton Rule 261
-- Credit: @Qwer2077 (the owner of the agent is credited as the solver)

open OMA.S_oeis_a280411 PowerSeries

namespace OMA.Proof_oeis_a280411

private lemma rule_true (k : ℕ) : rule true k = false := by
  unfold rule
  have hlt : 9 ≤ 2 * k + 1 ∨ 2 * k + 1 < 9 := le_or_gt 9 (2 * k + 1)
  rcases hlt with h | h
  · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) h))
  · have hk : k < 4 := by omega
    interval_cases k <;> decide

private lemma rule_false_zero : rule false 0 = true := by decide
private lemma rule_false_one : rule false 1 = true := by decide

private lemma countP_eq_origin (p : ℤ × ℤ) :
    (nbrs p).countP (fun q => decide (q = (0, 0))) = 0 ∨
    (nbrs p).countP (fun q => decide (q = (0, 0))) = 1 := by
  rcases p with ⟨x, y⟩
  unfold nbrs
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq, Prod.mk.injEq]
  by_cases h1 : x + 1 = 0 ∧ y = 0 <;>
  by_cases h2 : x - 1 = 0 ∧ y = 0 <;>
  by_cases h3 : x = 0 ∧ y + 1 = 0 <;>
  by_cases h4 : x = 0 ∧ y - 1 = 0 <;>
  simp [h1, h2, h3, h4] <;> omega

private lemma state_formula (t : ℕ) (p : ℤ × ℤ) :
    state t p = if Even t then decide (p = (0, 0)) else decide (p ≠ (0, 0)) := by
  induction t generalizing p with
  | zero =>
    simp [state]
  | succ t ih =>
    simp only [state]
    by_cases he : Even t
    · have ho : ¬ Even (t + 1) := by
        rw [Nat.even_add_one]
        exact not_not.mpr he
      simp only [ih, if_pos he, if_neg ho]
      by_cases hp : p = (0, 0)
      · subst hp
        simp [rule_true]
      · rw [decide_eq_false hp, decide_eq_true hp]
        rcases countP_eq_origin p with h0 | h1
        · rw [h0]; exact rule_false_zero
        · rw [h1]; exact rule_false_one
    · have he1 : Even (t + 1) := (Nat.even_add_one).mpr he
      simp only [ih, if_neg he, if_pos he1]
      by_cases hp : p = (0, 0)
      · subst hp
        decide
      · simp [hp, rule_true]

private lemma a_even_val (n : ℕ) (hn : Even n) : a n = 10 ^ n := by
  unfold a
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (if state n ((k : ℤ), 0) then 10 ^ (n - k) else 0) =
      if k = 0 then 10 ^ (n - k) else 0 := by
    intro k _
    rw [state_formula n _, if_pos hn]
    have hiff : (((k : ℤ), (0 : ℤ)) = (0, 0)) ↔ k = 0 := by
      simp only [Prod.mk.injEq, and_true]
      exact_mod_cast Iff.rfl
    simp [hiff]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  simp

private lemma a_even_rat (n : ℕ) (hn : Even n) :
    (a n : ℚ) = 2 ^ n * (4 * (-5) ^ n + 5 ^ (n + 1)) / 9 := by
  rw [a_even_val n hn]
  have hneg : (-5 : ℚ) ^ n = 5 ^ n := hn.neg_pow 5
  rw [hneg, pow_succ]
  have h10 : (10 : ℚ) ^ n = 2 ^ n * 5 ^ n := by rw [← mul_pow]; norm_num
  push_cast
  rw [h10]
  ring

private lemma geom_sum_pow_ten_rev (n : ℕ) :
    9 * (∑ k ∈ Finset.range n, (10 : ℚ) ^ (n - (k + 1))) = (10 : ℚ) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hshift : (∑ k ∈ Finset.range n, (10 : ℚ) ^ (n + 1 - (k + 1))) =
        10 * ∑ k ∈ Finset.range n, (10 : ℚ) ^ (n - (k + 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k < n := Finset.mem_range.mp hk
      have heq : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by omega
      rw [heq, pow_succ']
    rw [hshift]
    have hsub : n + 1 - (n + 1) = 0 := by omega
    rw [hsub, pow_zero, pow_succ]
    linarith

private lemma a_odd_rat_simple (n : ℕ) (hn : Odd n) :
    (a n : ℚ) = ((10 : ℚ) ^ n - 1) / 9 := by
  have hne : ¬ Even n := Nat.not_even_iff_odd.mpr hn
  have haval : a n = ∑ k ∈ Finset.range n, 10 ^ (n - (k + 1)) := by
    unfold a
    rw [Finset.sum_range_succ']
    have h0 : state n ((0 : ℤ), 0) = false := by
      rw [state_formula n _, if_neg hne]
      simp
    simp only [Nat.cast_zero, h0, Bool.false_eq_true, ↓reduceIte, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hst : state n ((k : ℤ) + 1, 0) = true := by
      rw [state_formula n _, if_neg hne]
      simp only [decide_eq_true_eq, ne_eq, Prod.mk.injEq, and_true]
      omega
    simp [hst]
  rw [haval]
  push_cast
  have h := geom_sum_pow_ten_rev n
  linarith

private lemma a_odd_rat (n : ℕ) (hn : Odd n) :
    (a n : ℚ) = ((-5) ^ n * 2 ^ (n + 2) + 2 ^ n * 5 ^ (n + 1) - 1) / 9 := by
  rw [a_odd_rat_simple n hn]
  have hneg : (-5 : ℚ) ^ n = -(5 ^ n) := hn.neg_pow 5
  have h10 : (10 : ℚ) ^ n = 2 ^ n * 5 ^ n := by rw [← mul_pow]; norm_num
  rw [hneg, h10]
  ring

private lemma a_rec (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4) := by
  suffices hq : (a n : ℚ) = 101 * (a (n - 2) : ℚ) - 100 * (a (n - 4) : ℚ) by
    exact_mod_cast hq
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hm2 : m + 4 - 2 = m + 2 := by omega
  have hm4 : m + 4 - 4 = m := by omega
  rw [hm2, hm4]
  rcases Nat.even_or_odd m with hm | hm
  · have h2 : Even (m + 2) := hm.add (by decide)
    have h4 : Even (m + 4) := hm.add (by decide)
    rw [a_even_val _ h4, a_even_val _ h2, a_even_val _ hm]
    push_cast
    ring
  · have h2 : Odd (m + 2) := hm.add_even (by decide)
    have h4 : Odd (m + 4) := hm.add_even (by decide)
    rw [a_odd_rat_simple _ h4, a_odd_rat_simple _ h2, a_odd_rat_simple _ hm]
    ring

private lemma a_val_0 : a 0 = 1 := by rw [a_even_val 0 (by decide)]; norm_num
private lemma a_val_1 : (a 1 : ℚ) = 1 := by rw [a_odd_rat_simple 1 (by decide)]; norm_num
private lemma a_val_2 : a 2 = 100 := by rw [a_even_val 2 (by decide)]; norm_num
private lemma a_val_3 : (a 3 : ℚ) = 111 := by rw [a_odd_rat_simple 3 (by decide)]; norm_num

private lemma coeff_mul_X_pow (f : ℚ⟦X⟧) (k n : ℕ) :
    PowerSeries.coeff n (f * X ^ k) = if k ≤ n then PowerSeries.coeff (n - k) f else 0 :=
  PowerSeries.coeff_mul_X_pow' f k n

private lemma gf_eq :
    A = (1 + X - X ^ 2 + 10 * X ^ 3) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X))⁻¹ := by
  set D : ℚ⟦X⟧ := (1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) with hD_def
  set N : ℚ⟦X⟧ := 1 + X - X ^ 2 + 10 * X ^ 3 with hN_def
  have hD_exp : D = 1 - C (101 : ℚ) * X ^ 2 + C (100 : ℚ) * X ^ 4 := by
    rw [hD_def]
    simp only [map_ofNat]
    ring
  have hD_const : PowerSeries.constantCoeff D = 1 := by
    rw [hD_exp]
    simp
  have hD_inv : D * D⁻¹ = 1 := by
    apply PowerSeries.mul_inv_cancel
    rw [hD_const]
    exact one_ne_zero
  have hAD : A * D = N := by
    rw [hD_exp]
    ext n
    have hmul : A * (1 - C (101 : ℚ) * X ^ 2 + C (100 : ℚ) * X ^ 4) =
        A - C (101 : ℚ) * (A * X ^ 2) + C (100 : ℚ) * (A * X ^ 4) := by ring
    rw [hmul]
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_mul_X_pow, A, PowerSeries.coeff_mk]
    have hN_exp : N = C (1 : ℚ) + C (1 : ℚ) * X ^ 1 - C (1 : ℚ) * X ^ 2 + C (10 : ℚ) * X ^ 3 := by
      rw [hN_def]
      simp only [map_one, map_ofNat, one_mul, pow_one]
    rw [hN_exp]
    simp only [map_add, map_sub, PowerSeries.coeff_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    match n with
    | 0 => simp [a_val_0]
    | 1 => simp [a_val_1]
    | 2 => simp [a_val_0, a_val_2]; norm_num
    | 3 => simp [a_val_1, a_val_3]; norm_num
    | m + 4 =>
      have hgt : 3 < m + 4 := by omega
      have hrec : (a (m + 4) : ℚ) = 101 * (a (m + 4 - 2) : ℚ) - 100 * (a (m + 4 - 4) : ℚ) := by
        exact_mod_cast a_rec (m + 4) hgt
      have h0 : m + 4 ≠ 0 := by omega
      have h1 : m + 4 ≠ 1 := by omega
      have h2 : m + 4 ≠ 2 := by omega
      have h3 : m + 4 ≠ 3 := by omega
      have hge2 : 2 ≤ m + 4 := by omega
      have hge4 : 4 ≤ m + 4 := by omega
      simp only [h0, h1, h2, h3, hge2, hge4, ↓reduceIte, mul_zero, add_zero, sub_zero]
      linarith
  calc
    A = A * (D * D⁻¹) := by rw [hD_inv, mul_one]
    _ = (A * D) * D⁻¹ := by rw [← mul_assoc]
    _ = N * D⁻¹ := by rw [hAD]

end OMA.Proof_oeis_a280411

theorem OMA.solution : type_of% @OMA.S_oeis_a280411.main := by
  exact ⟨OMA.Proof_oeis_a280411.a_even_rat, OMA.Proof_oeis_a280411.a_odd_rat,
    OMA.Proof_oeis_a280411.a_rec, OMA.Proof_oeis_a280411.gf_eq⟩
