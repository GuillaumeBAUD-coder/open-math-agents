import OMAStatements.S_oeis_a218832

open Finset OMA.S_oeis_a218832

def OMA.cnt (N : ℕ) : ℕ :=
  ((range N ×ˢ range N ×ˢ range N).filter fun p : ℕ × ℕ × ℕ =>
    0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.1 + p.2.1 + 2 * p.2.2 = N).card

lemma OMA.ncard_eq (N : ℕ) :
    Set.ncard {p : ℕ × ℕ × ℕ | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.1 + p.2.1 + 2 * p.2.2 = N} =
      OMA.cnt N := by
  have h : {p : ℕ × ℕ × ℕ | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.1 + p.2.1 + 2 * p.2.2 = N} =
      ↑((range N ×ˢ range N ×ˢ range N).filter fun p : ℕ × ℕ × ℕ =>
        0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.1 + p.2.1 + 2 * p.2.2 = N) := by
    ext ⟨p, q, r⟩
    simp only [Set.mem_setOf_eq, mem_coe, mem_filter, mem_product, mem_range]
    constructor
    · intro h
      exact ⟨⟨by omega, by omega, by omega⟩, h⟩
    · intro h
      exact h.2
  rw [h]
  first
    | exact Set.ncard_coe_finset _
    | exact Set.ncard_coe_Finset _

lemma OMA.l1 (N q r : ℕ) : ∀ m : ℕ,
    (∑ p ∈ range m, if 0 < p ∧ 0 < q ∧ 0 < r ∧ p + q + 2 * r = N then 1 else 0) =
      if 0 < q ∧ 0 < r ∧ q + 2 * r < N ∧ N - q - 2 * r < m then 1 else 0 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

lemma OMA.l2 (N r : ℕ) : ∀ m : ℕ,
    (∑ q ∈ range m, if 0 < q ∧ 0 < r ∧ q + 2 * r < N ∧ N - q - 2 * r < N then 1 else 0) =
      if 0 < r then min (m - 1) (N - 2 * r - 1) else 0 := by
  intro m
  induction m with
  | zero =>
    rw [sum_range_zero]
    split_ifs <;> omega
  | succ m ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

lemma OMA.l3 (N : ℕ) : ∀ m : ℕ, 2 * m ≤ N + 1 →
    ((∑ r ∈ range m, if 0 < r then min (N - 1) (N - 2 * r - 1) else 0 : ℕ) : ℤ) =
      if m = 0 then 0 else ((m : ℤ) - 1) * ((N : ℤ) - 1 - m) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro h
    rw [sum_range_succ, Nat.cast_add, ih (by omega)]
    rcases m with _ | k
    · simp
    · have e : ((if 0 < k + 1 then min (N - 1) (N - 2 * (k + 1) - 1) else 0 : ℕ) : ℤ) =
          (N : ℤ) - 2 * (k + 1) - 1 := by
        rw [if_pos (show 0 < k + 1 by omega)]
        omega
      rw [e, if_neg (show ¬ (k + 1 = 0) by omega), if_neg (show ¬ (k + 1 + 1 = 0) by omega)]
      push_cast
      ring

lemma OMA.l3' (N : ℕ) : ∀ m : ℕ, (N + 1) / 2 ≤ m →
    (∑ r ∈ range m, if 0 < r then min (N - 1) (N - 2 * r - 1) else 0) =
      ∑ r ∈ range ((N + 1) / 2), if 0 < r then min (N - 1) (N - 2 * r - 1) else 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

lemma OMA.cnt_eq (N : ℕ) : (OMA.cnt N : ℤ) =
    if (N + 1) / 2 = 0 then 0
    else ((((N + 1) / 2 : ℕ) : ℤ) - 1) * ((N : ℤ) - 1 - (((N + 1) / 2 : ℕ) : ℤ)) := by
  unfold OMA.cnt
  rw [card_filter]
  simp only [sum_product_right, OMA.l1, OMA.l2]
  rw [OMA.l3' N N (by omega), OMA.l3 N _ (by omega)]

theorem OMA.solution : type_of% @OMA.S_oeis_a218832.main := by
  have hz : ∀ n : ℕ, (a n : ℤ) = if (n ^ 2 + 1) / 2 = 0 then 0
      else ((((n ^ 2 + 1) / 2 : ℕ) : ℤ) - 1) *
        (((n ^ 2 : ℕ) : ℤ) - 1 - (((n ^ 2 + 1) / 2 : ℕ) : ℤ)) := by
    intro n
    have := OMA.cnt_eq (n ^ 2)
    rw [← OMA.ncard_eq] at this
    exact this
  have h1 : ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (7 + (-1) ^ n - 8 * (n : ℚ) ^ 2 + 2 * (n : ℚ) ^ 4) / 8 := by
    intro n hn
    have hzn := hz n
    rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
    · have e1 : ((2 * j) ^ 2 + 1) / 2 = 2 * j ^ 2 := by
        have : (2 * j) ^ 2 = 4 * j ^ 2 := by ring
        omega
      have e0 : ¬ (2 * j ^ 2 = 0) := by
        have : 0 < j := by omega
        have : 0 < j ^ 2 := by positivity
        omega
      rw [e1, if_neg e0] at hzn
      have hq : (a (2 * j) : ℚ) = (((2 * j ^ 2 : ℕ) : ℚ) - 1) *
          ((((2 * j) ^ 2 : ℕ) : ℚ) - 1 - ((2 * j ^ 2 : ℕ) : ℚ)) := by
        exact_mod_cast hzn
      rw [hq, (even_two_mul j).neg_one_pow]
      push_cast
      ring
    · have e1 : ((2 * j + 1) ^ 2 + 1) / 2 = 2 * j ^ 2 + 2 * j + 1 := by
        have : (2 * j + 1) ^ 2 = 4 * j ^ 2 + 4 * j + 1 := by ring
        omega
      rw [e1, if_neg (show ¬ (2 * j ^ 2 + 2 * j + 1 = 0) by omega)] at hzn
      have hq : (a (2 * j + 1) : ℚ) = (((2 * j ^ 2 + 2 * j + 1 : ℕ) : ℚ) - 1) *
          ((((2 * j + 1) ^ 2 : ℕ) : ℚ) - 1 - ((2 * j ^ 2 + 2 * j + 1 : ℕ) : ℚ)) := by
        exact_mod_cast hzn
      rw [hq, (odd_two_mul_add_one j).neg_one_pow]
      push_cast
      ring
  refine ⟨h1, ?_⟩
  have a0 : a 0 = 0 := by
    have := hz 0
    simp at this
    exact_mod_cast this
  have v1 : a 1 = 0 := by
    have := h1 1 le_rfl
    norm_num at this
    exact_mod_cast this
  have v2 : a 2 = 1 := by
    have := h1 2 (by norm_num)
    norm_num at this
    exact_mod_cast this
  have v3 : a 3 = 12 := by
    have := h1 3 (by norm_num)
    norm_num at this
    exact_mod_cast this
  have v4 : a 4 = 49 := by
    have := h1 4 (by norm_num)
    norm_num at this
    exact_mod_cast this
  have v5 : a 5 = 132 := by
    have := h1 5 (by norm_num)
    norm_num at this
    exact_mod_cast this
  have v6 : a 6 = 289 := by
    have := h1 6 (by norm_num)
    norm_num at this
    exact_mod_cast this
  ext k
  rw [mul_comm ((PowerSeries.X - 1) ^ 5 * (PowerSeries.X + 1) : PowerSeries ℤ),
    show ((PowerSeries.X - 1) ^ 5 * (PowerSeries.X + 1) : PowerSeries ℤ) =
      PowerSeries.X ^ 6 - 4 • PowerSeries.X ^ 5 + 5 • PowerSeries.X ^ 4 - 5 • PowerSeries.X ^ 2 +
        4 • PowerSeries.X ^ 1 - 1 by ring,
    show (-PowerSeries.X ^ 2 * (PowerSeries.X ^ 4 - 4 * PowerSeries.X ^ 3 + 6 * PowerSeries.X ^ 2 +
        8 * PowerSeries.X + 1) : PowerSeries ℤ) =
      4 • PowerSeries.X ^ 5 - PowerSeries.X ^ 6 - 6 • PowerSeries.X ^ 4 - 8 • PowerSeries.X ^ 3 -
        PowerSeries.X ^ 2 by ring]
  simp only [mul_add, mul_sub, mul_one, mul_smul_comm, map_add, map_sub, map_nsmul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
  by_cases hk : k < 7
  · interval_cases k <;> norm_num [a0, v1, v2, v3, v4, v5, v6]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
    simp only [if_pos (show 6 ≤ m + 7 by omega), if_pos (show 5 ≤ m + 7 by omega),
      if_pos (show 4 ≤ m + 7 by omega), if_pos (show 2 ≤ m + 7 by omega),
      if_pos (show 1 ≤ m + 7 by omega), if_neg (show ¬ (m + 7 = 5) by omega),
      if_neg (show ¬ (m + 7 = 6) by omega), if_neg (show ¬ (m + 7 = 4) by omega),
      if_neg (show ¬ (m + 7 = 3) by omega), if_neg (show ¬ (m + 7 = 2) by omega),
      show m + 7 - 6 = m + 1 from rfl, show m + 7 - 5 = m + 2 from rfl,
      show m + 7 - 4 = m + 3 from rfl, show m + 7 - 2 = m + 5 from rfl,
      show m + 7 - 1 = m + 6 from rfl, nsmul_eq_mul]
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [h1 (m + 1) (by omega), h1 (m + 2) (by omega), h1 (m + 3) (by omega), h1 (m + 5) (by omega),
      h1 (m + 6) (by omega), h1 (m + 7) (by omega)]
    push_cast
    ring
