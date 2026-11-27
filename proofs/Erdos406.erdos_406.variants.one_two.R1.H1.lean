import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1

namespace OMA.Erdos406H1

/-- If the base-3 digit of `n` at position `i` is `0` and `n` has more than `i + 1` digits
positions available (`3 ^ (i + 1) ≤ n`), then `0` occurs among the base-3 digits of `n`. -/
lemma zero_mem_digits_three : ∀ (i n : ℕ), 3 ^ (i + 1) ≤ n → n / 3 ^ i % 3 = 0 →
    0 ∈ Nat.digits 3 n := by
  intro i
  induction i with
  | zero =>
    intro n hn h0
    have hpos : 0 < n := by omega
    rw [Nat.digits_def' (by norm_num) hpos]
    simp only [pow_zero, Nat.div_one] at h0
    simp [h0]
  | succ i ih =>
    intro n hn h0
    have hpos : 0 < n := by
      have : 0 < 3 ^ (i + 1 + 1) := by positivity
      omega
    rw [Nat.digits_def' (by norm_num) hpos]
    apply List.mem_cons_of_mem
    apply ih
    · rw [Nat.le_div_iff_mul_le (by norm_num)]
      calc 3 ^ (i + 1) * 3 = 3 ^ (i + 1 + 1) := by ring
        _ ≤ n := hn
    · rw [Nat.div_div_eq_div_mul, ← pow_succ']
      exact h0

/-- The finite check: for every `15 < k ≤ 1000` one of the 26 lowest base-3 digits of `2 ^ k`
is `0`. -/
lemma check : ∀ k < 1001, 15 < k →
    ∃ i < 26, 3 ^ (i + 1) ≤ 2 ^ k ∧ 2 ^ k / 3 ^ i % 3 = 0 := by
  decide +kernel

end OMA.Erdos406H1

theorem OMA.solution : OMA.R_Erdos406_erdos_406_variants_one_two_R1.H1 := by
  intro k hk hk' hsub
  obtain ⟨i, -, hi, h0⟩ := OMA.Erdos406H1.check k (by omega) hk
  have h := hsub (OMA.Erdos406H1.zero_mem_digits_three i (2 ^ k) hi h0)
  simp at h
