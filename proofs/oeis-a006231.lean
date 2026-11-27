import OMAStatements.S_oeis_a006231

namespace OMA.S_oeis_a006231

open Finset

def c (n : ℕ) : ℕ := ∑ k ∈ range n, n.descFactorial (k + 1) / (k + 1)
def e (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), n.descFactorial k

lemma term (n k : ℕ) : (n + 1).descFactorial (k + 1) / (k + 1) =
    n.descFactorial (k + 1) / (k + 1) + n.descFactorial k := by
  have h : (n + 1).descFactorial (k + 1) = n.descFactorial (k + 1) + n.descFactorial k * (k + 1) := by
    rw [Nat.succ_descFactorial_succ, Nat.descFactorial_succ]
    rcases le_or_gt k n with hk | hk
    · rw [show n + 1 = (n - k) + (k + 1) by omega]; ring
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk]; ring
  rw [h, Nat.add_mul_div_right _ _ (Nat.succ_pos k)]

lemma c_succ (n : ℕ) : c (n + 1) = c n + e n := by
  unfold c e
  simp only [term, sum_add_distrib]
  rw [sum_range_succ (fun k => n.descFactorial (k + 1) / (k + 1)),
    Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_succ_self n), Nat.zero_div, add_zero]

lemma e_succ (n : ℕ) : e (n + 1) = (n + 1) * e n + 1 := by
  unfold e
  rw [sum_range_succ', mul_sum]
  simp only [Nat.succ_descFactorial_succ, Nat.descFactorial_zero]

lemma R (j : ℕ) : (c (j + 2) : ℤ) = (j + 2) * c (j + 1) - (j + 1) * c j + 1 := by
  have h1 := c_succ (j + 1)
  have h2 := c_succ j
  have h3 := e_succ j
  zify at h1 h2 h3
  push_cast
  linear_combination h1 - ((j : ℤ) + 1) * h2 + h3

lemma a_eq (n : ℕ) : (a n : ℤ) = c n - n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a, c]
  · have hc : c n = ∑ k ∈ Icc 1 n, n.descFactorial k / k := by
      unfold c
      rw [show Icc 1 n = Ico 1 (n + 1) by ext x; simp only [mem_Icc, mem_Ico]; omega, sum_Ico_eq_sum_range]
      apply sum_congr (by congr 1); intro k _; ring_nf
    have hI : Icc 1 n = insert 1 (Icc 2 n) := by
      ext x; simp; omega
    rw [hc, hI, sum_insert (by simp)]
    simp [a]

theorem solution_main : ∀ n : ℕ, 5 ≤ n →
    (a n : ℤ) + (-(n : ℤ) - 2) * a (n - 1) + (3 * (n : ℤ) - 2) * a (n - 2)
      + 3 * (-(n : ℤ) + 2) * a (n - 3) + ((n : ℤ) - 3) * a (n - 4) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
    a_eq, a_eq, a_eq, a_eq, a_eq]
  have r0 := R (m + 3)
  have r1 := R (m + 2)
  have r2 := R (m + 1)
  rw [show m + 3 + 2 = m + 5 by ring, show m + 3 + 1 = m + 4 by ring] at r0
  rw [show m + 2 + 2 = m + 4 by ring, show m + 2 + 1 = m + 3 by ring] at r1
  rw [show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring] at r2
  push_cast at r0 r1 r2 ⊢
  linear_combination r0 - 2 * r1 + r2

end OMA.S_oeis_a006231

theorem OMA.solution : type_of% @OMA.S_oeis_a006231.main := OMA.S_oeis_a006231.solution_main
