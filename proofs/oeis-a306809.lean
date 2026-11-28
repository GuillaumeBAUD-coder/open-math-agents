import OMAStatements.S_oeis_a306809

namespace OMA.P306809

open OMA.S_oeis_a306809 Finset

/-- The transform of an integer sequence. -/
def T (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), (n.choose k : ℤ) * f k

lemma T_succ (f : ℕ → ℤ) (n : ℕ) : T f (n + 1) = T f n + T (fun k => f (k + 1)) n := by
  unfold T
  rw [sum_range_succ' _ (n + 1)]
  have h1 : ∀ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℤ) * f (k + 1)
      = (n.choose k : ℤ) * f (k + 1) + (n.choose (k + 1) : ℤ) * f (k + 1) := by
    intro k _
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  rw [sum_congr rfl h1, sum_add_distrib]
  rw [sum_range_succ' (fun k => (n.choose k : ℤ) * f k) n]
  rw [sum_range_succ (fun k => (n.choose (k + 1) : ℤ) * f (k + 1)) n]
  simp
  ring

/-- The transform of the continued fraction sequence shifted by `j`. -/
def D (j n : ℕ) : ℤ := T (fun k => (b (k + j) : ℤ)) n

lemma D_succ (j n : ℕ) : D j (n + 1) = D j n + D (j + 1) n := by
  unfold D
  rw [T_succ]
  have h : (fun k => (b (k + 1 + j) : ℤ)) = (fun k => (b (k + (j + 1)) : ℤ)) := by
    funext k
    have e : k + 1 + j = k + (j + 1) := by omega
    rw [e]
  rw [h]

lemma b_succ (k : ℕ) : b (k + 1) = if (k + 1) % 3 = 2 then 2 * (k + 2) / 3 else 1 := rfl

lemma b_rec (k : ℕ) : b (k + 7) + b (k + 1) = 2 * b (k + 4) := by
  rw [b_succ (k + 6), b_succ (k + 3), b_succ k]
  split_ifs <;> omega

lemma D_rec (n : ℕ) : D 7 n = 2 * D 4 n - D 1 n := by
  unfold D T
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  have h : (b (k + 7) : ℤ) + (b (k + 1) : ℤ) = 2 * (b (k + 4) : ℤ) := by
    exact_mod_cast b_rec k
  linear_combination (n.choose k : ℤ) * h

lemma a_eq (n : ℕ) : a n = D 0 n := rfl

end OMA.P306809

open OMA.S_oeis_a306809 OMA.P306809 in
theorem OMA.solution : type_of% @OMA.S_oeis_a306809.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have e1 : m + 7 - 1 = m + 6 := by omega
  have e2 : m + 7 - 2 = m + 5 := by omega
  have e3 : m + 7 - 3 = m + 4 := by omega
  have e4 : m + 7 - 4 = m + 3 := by omega
  have e5 : m + 7 - 5 = m + 2 := by omega
  have e6 : m + 7 - 6 = m + 1 := by omega
  have e7 : m + 7 - 7 = m := by omega
  rw [e1, e2, e3, e4, e5, e6, e7]
  simp only [a_eq]
  have h0_0 : D 0 (m + 1) = D 0 m + D 1 m := D_succ 0 m
  have h0_1 : D 1 (m + 1) = D 1 m + D 2 m := D_succ 1 m
  have h0_2 : D 2 (m + 1) = D 2 m + D 3 m := D_succ 2 m
  have h0_3 : D 3 (m + 1) = D 3 m + D 4 m := D_succ 3 m
  have h0_4 : D 4 (m + 1) = D 4 m + D 5 m := D_succ 4 m
  have h0_5 : D 5 (m + 1) = D 5 m + D 6 m := D_succ 5 m
  have h0_6 : D 6 (m + 1) = D 6 m + D 7 m := D_succ 6 m
  have h1_0 : D 0 (m + 2) = D 0 (m + 1) + D 1 (m + 1) := D_succ 0 (m + 1)
  have h1_1 : D 1 (m + 2) = D 1 (m + 1) + D 2 (m + 1) := D_succ 1 (m + 1)
  have h1_2 : D 2 (m + 2) = D 2 (m + 1) + D 3 (m + 1) := D_succ 2 (m + 1)
  have h1_3 : D 3 (m + 2) = D 3 (m + 1) + D 4 (m + 1) := D_succ 3 (m + 1)
  have h1_4 : D 4 (m + 2) = D 4 (m + 1) + D 5 (m + 1) := D_succ 4 (m + 1)
  have h1_5 : D 5 (m + 2) = D 5 (m + 1) + D 6 (m + 1) := D_succ 5 (m + 1)
  have h2_0 : D 0 (m + 3) = D 0 (m + 2) + D 1 (m + 2) := D_succ 0 (m + 2)
  have h2_1 : D 1 (m + 3) = D 1 (m + 2) + D 2 (m + 2) := D_succ 1 (m + 2)
  have h2_2 : D 2 (m + 3) = D 2 (m + 2) + D 3 (m + 2) := D_succ 2 (m + 2)
  have h2_3 : D 3 (m + 3) = D 3 (m + 2) + D 4 (m + 2) := D_succ 3 (m + 2)
  have h2_4 : D 4 (m + 3) = D 4 (m + 2) + D 5 (m + 2) := D_succ 4 (m + 2)
  have h3_0 : D 0 (m + 4) = D 0 (m + 3) + D 1 (m + 3) := D_succ 0 (m + 3)
  have h3_1 : D 1 (m + 4) = D 1 (m + 3) + D 2 (m + 3) := D_succ 1 (m + 3)
  have h3_2 : D 2 (m + 4) = D 2 (m + 3) + D 3 (m + 3) := D_succ 2 (m + 3)
  have h3_3 : D 3 (m + 4) = D 3 (m + 3) + D 4 (m + 3) := D_succ 3 (m + 3)
  have h4_0 : D 0 (m + 5) = D 0 (m + 4) + D 1 (m + 4) := D_succ 0 (m + 4)
  have h4_1 : D 1 (m + 5) = D 1 (m + 4) + D 2 (m + 4) := D_succ 1 (m + 4)
  have h4_2 : D 2 (m + 5) = D 2 (m + 4) + D 3 (m + 4) := D_succ 2 (m + 4)
  have h5_0 : D 0 (m + 6) = D 0 (m + 5) + D 1 (m + 5) := D_succ 0 (m + 5)
  have h5_1 : D 1 (m + 6) = D 1 (m + 5) + D 2 (m + 5) := D_succ 1 (m + 5)
  have h6_0 : D 0 (m + 7) = D 0 (m + 6) + D 1 (m + 6) := D_succ 0 (m + 6)
  have hr := D_rec m
  linarith
