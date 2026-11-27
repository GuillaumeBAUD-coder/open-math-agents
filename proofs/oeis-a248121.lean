import OMAStatements.S_oeis_a248121

namespace OMA.P_a248121

open OMA.S_oeis_a248121 Finset

noncomputable def U (x : ℝ) : ℝ := 1 / x - 1 / (2 * x ^ 2) + 1 / (6 * x ^ 3)
noncomputable def L (x : ℝ) : ℝ := U x - 1 / (30 * x ^ 5)
noncomputable def f (k : ℕ) : ℝ := 1 / (k : ℝ) ^ 2
noncomputable def T (n : ℕ) : ℝ := ∑' k : ℕ, f (k + (n + 1))

lemma U_step {m : ℝ} (hm : 0 < m) : 1 / (m + 1) ^ 2 < U m - U (m + 1) := by
  have h : U m - U (m + 1) - 1 / (m + 1) ^ 2 = 1 / (6 * m ^ 3 * (m + 1) ^ 3) := by
    unfold U
    field_simp
    ring
  have : 0 < 1 / (6 * m ^ 3 * (m + 1) ^ 3) := by positivity
  linarith

lemma L_step {m : ℝ} (hm : 0 < m) : L m - L (m + 1) ≤ 1 / (m + 1) ^ 2 := by
  have h : 1 / (m + 1) ^ 2 - (L m - L (m + 1)) =
      (5 * m ^ 2 + 5 * m + 1) / (30 * m ^ 5 * (m + 1) ^ 5) := by
    unfold L U
    field_simp
    ring
  have : 0 ≤ (5 * m ^ 2 + 5 * m + 1) / (30 * m ^ 5 * (m + 1) ^ 5) := by positivity
  linarith

lemma U_eq {x : ℝ} (hx : 0 < x) : U x = 1 / x - (3 * x - 1) / (6 * x ^ 3) := by
  unfold U
  field_simp
  ring

lemma L_eq {x : ℝ} (hx : 0 < x) :
    L x = 1 / x - (3 * x - 1) / (6 * x ^ 3) - 1 / (30 * x ^ 5) := by
  unfold L
  rw [U_eq hx]

lemma U_pos {x : ℝ} (hx : 1 ≤ x) : 0 < U x := by
  rw [U_eq (by linarith)]
  have h : 1 / x - (3 * x - 1) / (6 * x ^ 3) = (6 * x ^ 2 - 3 * x + 1) / (6 * x ^ 3) := by
    field_simp
    ring
  rw [h]
  apply div_pos _ (by positivity)
  nlinarith

lemma L_le {x : ℝ} (hx : 1 ≤ x) : L x ≤ 1 / x := by
  rw [L_eq (by linarith)]
  have h1 : 0 ≤ (3 * x - 1) / (6 * x ^ 3) := div_nonneg (by linarith) (by positivity)
  have h2 : 0 ≤ 1 / (30 * x ^ 5) := by positivity
  linarith

lemma f_nonneg (k : ℕ) : 0 ≤ f k := by
  unfold f
  positivity

lemma summ : Summable f := hasSum_zeta_two.summable

lemma summ_shift (n : ℕ) : Summable (fun k => f (k + n)) := (summable_nat_add_iff n).2 summ

lemma T_succ (n : ℕ) : T n = f (n + 1) + T (n + 1) := by
  unfold T
  rw [(summ_shift (n + 1)).tsum_eq_zero_add]
  congr 1
  · simp
  · congr 1
    funext k
    congr 1
    omega

lemma partial_bounds (n : ℕ) (hn : 1 ≤ n) (N : ℕ) :
    L n - L ((n : ℝ) + N) ≤ ∑ k ∈ range N, f (k + (n + 1)) ∧
    ∑ k ∈ range N, f (k + (n + 1)) ≤ U n - U ((n : ℝ) + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < n + N := by positivity
    have e : f (N + (n + 1)) = 1 / (((n : ℝ) + N) + 1) ^ 2 := by
      unfold f
      push_cast
      ring
    have h1 := U_step hpos
    have h2 := L_step hpos
    have c : ((n : ℝ) + ((N + 1 : ℕ) : ℝ)) = (n + N) + 1 := by
      push_cast
      ring
    rw [c, e]
    constructor <;> linarith [ih.1, ih.2]

lemma T_le (n : ℕ) (hn : 1 ≤ n) : T n ≤ U n := by
  unfold T
  apply Real.tsum_le_of_sum_range_le (fun k => f_nonneg _)
  intro N
  have h1 := (partial_bounds n hn N).2
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (0 : ℝ) ≤ N := by positivity
  have h2 : 0 < U ((n : ℝ) + N) := U_pos (by linarith)
  linarith

lemma T_lt (n : ℕ) (hn : 1 ≤ n) : T n < U n := by
  rw [T_succ]
  have h1 := T_le (n + 1) (by omega)
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 := U_step (m := (n : ℝ)) (by linarith)
  have e : f (n + 1) = 1 / ((n : ℝ) + 1) ^ 2 := by
    unfold f
    push_cast
    ring
  have e2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [e2] at h1
  linarith

lemma L_le_T (n : ℕ) (hn : 1 ≤ n) : L n ≤ T n := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hcon)
  have h1 := (partial_bounds n hn (N + 1)).1
  have h2 : ∑ k ∈ range (N + 1), f (k + (n + 1)) ≤ T n :=
    (summ_shift (n + 1)).sum_le_tsum _ (fun k _ => f_nonneg _)
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have h3 : L ((n : ℝ) + ((N + 1 : ℕ) : ℝ)) ≤ 1 / ((n : ℝ) + ((N + 1 : ℕ) : ℝ)) :=
    L_le (by push_cast; linarith)
  have h4 : 1 / ((n : ℝ) + ((N + 1 : ℕ) : ℝ)) ≤ 1 / ((N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith
  linarith

lemma Icc_eq (n : ℕ) : ∑ k ∈ Icc 1 n, 1 / (k : ℝ) ^ 2 = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]
    rfl

lemma S_add_T (n : ℕ) : ∑ k ∈ Icc 1 n, 1 / (k : ℝ) ^ 2 + T n = Real.pi ^ 2 / 6 := by
  have h := summ.sum_add_tsum_nat_add (n + 1)
  have hz : ∑' k, f k = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
  rw [hz, sum_range_succ'] at h
  have h0 : f 0 = 0 := by
    unfold f
    simp
  rw [h0, add_zero] at h
  rw [Icc_eq]
  exact h

lemma closed (n : ℕ) (hn : 1 ≤ n) : a n = 2 * (n : ℤ) ^ 2 + (6 * (n : ℤ) + 2) / 9 := by
  have hn0 : n ≠ 0 := by omega
  have hD : 1 / (n : ℝ) - Real.pi ^ 2 / 6 + ∑ k ∈ Icc 1 n, 1 / (k : ℝ) ^ 2 = 1 / n - T n := by
    have := S_add_T n
    linarith
  unfold a
  rw [if_neg hn0, hD]
  set q : ℤ := (6 * (n : ℤ) + 2) / 9 with hq
  have hq1 : 6 * (n : ℤ) - 6 ≤ 9 * q := by omega
  have hq2 : 9 * q ≤ 6 * (n : ℤ) := by omega
  have hq1' : 6 * (n : ℝ) - 6 ≤ 9 * q := by exact_mod_cast hq1
  have hq2' : 9 * (q : ℝ) ≤ 6 * n := by exact_mod_cast hq2
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlo := T_lt n hn
  have hhi := L_le_T n hn
  rw [U_eq (by linarith)] at hlo
  rw [L_eq (by linarith)] at hhi
  rw [Int.floor_eq_iff]
  push_cast
  obtain ⟨x, hxn⟩ : ∃ x : ℝ, x = n := ⟨_, rfl⟩
  rw [← hxn] at hq1' hq2' hx1 hlo hhi ⊢
  have hA : (3 * x - 1) / (6 * x ^ 3) < 1 / x - T n := by linarith
  have hB : 1 / x - T n ≤ (3 * x - 1) / (6 * x ^ 3) + 1 / (30 * x ^ 5) := by linarith
  have hApos : 0 < (3 * x - 1) / (6 * x ^ 3) := div_pos (by linarith) (by positivity)
  have hDpos : 0 < 1 / x - T n := lt_trans hApos hA
  constructor
  · rw [le_div_iff₀ hDpos]
    have k1 : (2 * x ^ 2 + 2 * x / 3) * ((3 * x - 1) / (6 * x ^ 3) + 1 / (30 * x ^ 5)) ≤ 1 := by
      have e : (2 * x ^ 2 + 2 * x / 3) * ((3 * x - 1) / (6 * x ^ 3) + 1 / (30 * x ^ 5))
          = (90 * x ^ 5 - 10 * x ^ 3 + 6 * x ^ 2 + 2 * x) / (90 * x ^ 5) := by
        field_simp
        ring
      rw [e, div_le_one (by positivity)]
      nlinarith
    calc (2 * x ^ 2 + (q : ℝ)) * (1 / x - T n)
        ≤ (2 * x ^ 2 + 2 * x / 3) * (1 / x - T n) := by
          apply mul_le_mul_of_nonneg_right _ hDpos.le
          linarith
      _ ≤ (2 * x ^ 2 + 2 * x / 3) * ((3 * x - 1) / (6 * x ^ 3) + 1 / (30 * x ^ 5)) := by
          apply mul_le_mul_of_nonneg_left hB
          positivity
      _ ≤ 1 := k1
  · rw [div_lt_iff₀ hDpos]
    have k2 : 1 ≤ (2 * x ^ 2 + (2 * x + 1) / 3) * ((3 * x - 1) / (6 * x ^ 3)) := by
      have e : (2 * x ^ 2 + (2 * x + 1) / 3) * ((3 * x - 1) / (6 * x ^ 3))
          = (18 * x ^ 3 + x - 1) / (18 * x ^ 3) := by
        field_simp
        ring
      rw [e, le_div_iff₀ (by positivity)]
      nlinarith
    calc (1 : ℝ) ≤ (2 * x ^ 2 + (2 * x + 1) / 3) * ((3 * x - 1) / (6 * x ^ 3)) := k2
      _ ≤ (2 * x ^ 2 + (q : ℝ) + 1) * ((3 * x - 1) / (6 * x ^ 3)) := by
          apply mul_le_mul_of_nonneg_right _ hApos.le
          linarith
      _ < (2 * x ^ 2 + (q : ℝ) + 1) * (1 / x - T n) := by
          apply mul_lt_mul_of_pos_left hA
          nlinarith

lemma rec_part (n : ℕ) (hn : 5 < n) :
    a n = 2 * a (n - 1) - a (n - 2) + a (n - 3) - 2 * a (n - 4) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 5 = m + 1 by omega]
  rw [closed (m + 6) (by omega), closed (m + 5) (by omega), closed (m + 4) (by omega),
    closed (m + 3) (by omega), closed (m + 2) (by omega), closed (m + 1) (by omega)]
  push_cast
  have h : (6 * ((m : ℤ) + 6) + 2) / 9 = 2 * ((6 * ((m : ℤ) + 5) + 2) / 9)
      - (6 * ((m : ℤ) + 4) + 2) / 9 + (6 * ((m : ℤ) + 3) + 2) / 9
      - 2 * ((6 * ((m : ℤ) + 2) + 2) / 9) + (6 * ((m : ℤ) + 1) + 2) / 9 := by
    obtain ⟨t, ht | ht | ht⟩ : ∃ t : ℤ, (m : ℤ) = 3 * t ∨ (m : ℤ) = 3 * t + 1 ∨
        (m : ℤ) = 3 * t + 2 := ⟨(m : ℤ) / 3, by omega⟩ <;>
      rw [ht] <;> omega
  linear_combination h

lemma a0 : a 0 = 0 := by
  unfold a
  simp

open PowerSeries in
lemma gf : (1 - (X : PowerSeries ℤ)) ^ 3 * (1 + X + X ^ 2) * PowerSeries.mk a =
      X * (X + 1) ^ 2 * (X + 2) := by
  have e1 : (1 - (X : PowerSeries ℤ)) ^ 3 * (1 + X + X ^ 2) =
      1 - X ^ 1 - X ^ 1 + X ^ 2 - X ^ 3 + X ^ 4 + X ^ 4 - X ^ 5 := by ring
  have e2 : (X : PowerSeries ℤ) * (X + 1) ^ 2 * (X + 2) =
      X ^ 4 + X ^ 3 + X ^ 3 + X ^ 3 + X ^ 3 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 1 + X ^ 1 := by
    ring
  rw [e1, e2]
  ext k
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add, coeff_X_pow_mul', coeff_X_pow, coeff_mk]
  rcases Nat.lt_or_ge k 6 with hk | hk
  · interval_cases k <;> simp [a0, closed]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
    have hr := rec_part (m + 6) (by omega)
    simp only [show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega,
      show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, if_true]
    simp only [show m + 6 ≠ 1 by omega, show m + 6 ≠ 2 by omega, show m + 6 ≠ 3 by omega,
      show m + 6 ≠ 4 by omega, if_false]
    rw [hr]
    ring

end OMA.P_a248121

theorem OMA.solution : type_of% @OMA.S_oeis_a248121.main := by
  refine ⟨fun n hn => OMA.P_a248121.rec_part n hn, OMA.P_a248121.gf⟩
