import OMAStatements.S_oeis_a265723

open PowerSeries

namespace OMA.P_oeis_a265723

open OMA.S_oeis_a265723

lemma rule1 (l c r : Bool) : ruleOut 1 l c r = (!l && !c && !r) := by
  cases l <;> cases c <;> cases r <;> first | decide | rfl

lemma cellO_of (k : ℕ) (h : ∀ i : ℤ, cell 1 (2 * k) i = decide (i = 0)) :
    ∀ i : ℤ, cell 1 (2 * k + 1) i = decide (i < -1 ∨ 1 < i) := by
  intro i
  show ruleOut 1 (cell 1 (2 * k) (i - 1)) (cell 1 (2 * k) i) (cell 1 (2 * k) (i + 1)) = _
  rw [h, h, h, rule1, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  constructor <;> intro hh <;> omega

lemma cellE : ∀ k : ℕ, ∀ i : ℤ, cell 1 (2 * k) i = decide (i = 0)
  | 0 => fun _ => rfl
  | k + 1 => fun i => by
    have hO := cellO_of k (cellE k)
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring]
    show ruleOut 1 (cell 1 (2 * k + 1) (i - 1)) (cell 1 (2 * k + 1) i)
      (cell 1 (2 * k + 1) (i + 1)) = _
    rw [hO, hO, hO, rule1, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    constructor <;> intro hh <;> omega

lemma cell_iff (n : ℕ) (i : ℤ) :
    cell 1 n i = false ↔ (if n % 2 = 0 then i ≠ 0 else (-1 ≤ i ∧ i ≤ 1)) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [cellE k, if_pos (by omega)]
    exact decide_eq_false_iff_not
  · rw [cellO_of k (cellE k), if_neg (by omega), decide_eq_false_iff_not]
    constructor <;> intro hh <;> omega

lemma a_val (n : ℕ) : a n = if n % 2 = 0 then 2 * (n : ℤ) else 3 := by
  have hs : a n = (((Finset.range (2 * n + 1)).filter
      (fun j : ℕ => cell 1 n ((j : ℤ) - n) = false)).card : ℤ) := by
    unfold a
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rcases Bool.eq_false_or_eq_true (cell 1 n ((j : ℤ) - n)) with h | h <;> simp [h]
  rw [hs]
  split_ifs with h
  · have e : (Finset.range (2 * n + 1)).filter (fun j : ℕ => cell 1 n ((j : ℤ) - n) = false) =
        (Finset.range (2 * n + 1)).erase n := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range, cell_iff, if_pos h]
      constructor <;> intro hh <;> omega
    rw [e, Finset.card_erase_of_mem (by simp only [Finset.mem_range]; omega), Finset.card_range,
      Nat.add_sub_cancel]
    push_cast
    ring
  · have e : (Finset.range (2 * n + 1)).filter (fun j : ℕ => cell 1 n ((j : ℤ) - n) = false) =
        {n - 1, n, n + 1} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, cell_iff, if_neg h, Finset.mem_insert,
        Finset.mem_singleton]
      constructor <;> intro hh <;> omega
    rw [e, Finset.card_eq_three.2 ⟨n - 1, n, n + 1, by omega, by omega, by omega, rfl⟩]
    norm_num

end OMA.P_oeis_a265723

open OMA.S_oeis_a265723 OMA.P_oeis_a265723

theorem OMA.solution : type_of% @OMA.S_oeis_a265723.main := by
  have hrec : ∀ n > 3, a n = 2 * a (n - 2) - a (n - 4) := by
    intro n hn
    rw [a_val, a_val, a_val]
    split_ifs <;> omega
  refine ⟨fun n => ?_, hrec, ?_⟩
  · rw [a_val]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [if_pos (by omega), zpow_natCast, pow_mul]
      push_cast
      norm_num <;> ring
    · rw [if_neg (by omega), zpow_natCast, pow_succ, pow_mul]
      push_cast
      norm_num <;> ring
  · ext m
    have e1 : ((1 : PowerSeries ℚ) - X) ^ 2 * (1 + X) ^ 2 = 1 - (X ^ 2 + X ^ 2) + X ^ 4 := by
      ring
    have e2 : (X : PowerSeries ℚ) * (3 + 4 * X - 3 * X ^ 2) =
        (X + X + X) + (X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2) - (X ^ 3 + X ^ 3 + X ^ 3) := by
      ring
    rw [e1, e2]
    simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mk, coeff_mul_X_pow',
      coeff_X, coeff_X_pow]
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m <;> split_ifs <;> first | contradiction | omega | norm_num [a_val]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      have h := hrec (k + 4) (by omega)
      rw [show k + 4 - 2 = k + 2 by omega, show k + 4 - 4 = k by omega] at h
      have h' := congrArg (Int.cast : ℤ → ℚ) h
      push_cast at h'
      split_ifs <;> first
        | contradiction
        | omega
        | (rw [show k + 4 - 2 = k + 2 by omega, show k + 4 - 4 = k by omega]; linarith)
