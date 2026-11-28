import OMAStatements.S_oeis_a006231

namespace OMA.P_oeis_a006231

open OMA.S_oeis_a006231

/-- `c n = Sum_{k=1..n+1} n(n-1)...(n-k+1)/k`, i.e. `a n + n`. -/
def c (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.descFactorial (k + 1) / (k + 1)

/-- `e n = Sum_{j=0..n} n!/(n-j)!` (A000522). -/
def e (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), n.descFactorial j

theorem a_eq (n : ℕ) : a n + n = c n := by
  unfold a c
  rw [Finset.sum_range_succ', Nat.descFactorial_one, Nat.div_one]
  congr 1
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  rcases n with _ | m
  · simp
  · rw [Finset.sum_range_succ, Nat.descFactorial_of_lt (by omega : m + 1 < m + 1 + 1), Nat.zero_div,
      add_zero, show m + 1 + 1 - 2 = m by omega]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show 2 + k = k + 1 + 1 by omega]

theorem dF_succ (n k : ℕ) : (n + 1).descFactorial (k + 1) / (k + 1) =
    n.descFactorial (k + 1) / (k + 1) + n.descFactorial k := by
  rw [Nat.succ_descFactorial_succ]
  have h : (n + 1) * n.descFactorial k = n.descFactorial (k + 1) + (k + 1) * n.descFactorial k := by
    rw [Nat.descFactorial_succ]
    rcases Nat.lt_or_ge n k with hlt | hle
    · simp [Nat.descFactorial_of_lt hlt]
    · zify [hle]; ring
  rw [h, Nat.add_mul_div_left _ _ (Nat.succ_pos k)]

theorem c_succ (n : ℕ) : c (n + 1) = c n + e n := by
  unfold c e
  simp only [dF_succ, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ (fun k => n.descFactorial (k + 1) / (k + 1)),
    Finset.sum_range_succ (fun k => n.descFactorial k) (n + 1),
    Nat.descFactorial_of_lt (by omega : n < n + 1 + 1),
    Nat.descFactorial_of_lt (by omega : n < n + 1)]
  simp

theorem e_succ (n : ℕ) : e (n + 1) = (n + 1) * e n + 1 := by
  unfold e
  rw [Finset.sum_range_succ', Nat.descFactorial_zero]
  simp only [Nat.succ_descFactorial_succ, ← Finset.mul_sum]

end OMA.P_oeis_a006231

open OMA.P_oeis_a006231 in
theorem OMA.solution : type_of% @OMA.S_oeis_a006231.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have ha : ∀ k, (OMA.S_oeis_a006231.a k : ℤ) = c k - k := by
    intro k; have := a_eq k; zify at this; linarith
  have h1 : (c (m + 1) : ℤ) = c m + e m := by exact_mod_cast c_succ m
  have h2 : (c (m + 2) : ℤ) = c (m + 1) + e (m + 1) := by exact_mod_cast c_succ (m + 1)
  have h3 : (c (m + 3) : ℤ) = c (m + 2) + e (m + 2) := by exact_mod_cast c_succ (m + 2)
  have h4 : (c (m + 4) : ℤ) = c (m + 3) + e (m + 3) := by exact_mod_cast c_succ (m + 3)
  have g1 : (e (m + 1) : ℤ) = (m + 1) * e m + 1 := by exact_mod_cast e_succ m
  have g2 : (e (m + 2) : ℤ) = (m + 2) * e (m + 1) + 1 := by
    exact_mod_cast e_succ (m + 1)
  have g3 : (e (m + 3) : ℤ) = (m + 3) * e (m + 2) + 1 := by
    exact_mod_cast e_succ (m + 2)
  have s1 : m + 4 - 1 = m + 3 := by omega
  have s2 : m + 4 - 2 = m + 2 := by omega
  have s3 : m + 4 - 3 = m + 1 := by omega
  have s4 : m + 4 - 4 = m := by omega
  rw [s1, s2, s3, s4, ha, ha, ha, ha, ha, h4, h3, h2, h1, g3, g2, g1]
  push_cast
  ring
