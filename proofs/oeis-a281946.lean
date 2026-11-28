import OMAStatements.S_oeis_a281946

-- Problem: A281946: Number of sequences of balls colored with at most n colors such that exactly two balls are of a color seen earlier in the sequence.
-- Upstream: formal-conjectures statements/oeis-a281946.lean:0 (declaration OMA.S_oeis_a281946.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write a(n) = n! t(n) and A281912(n) = n! s(n) with t(n) = Sum_{j<n} (C(j+3,3) + 3 C(j+3,4))/(n-1-j)! and
s(n) = Sum_{j<n} C(j+2,2)/(n-1-j)!. The Stirling numbers S2(i+2,i) are C(i+2,3) + 3 C(i+2,4), which gives the
first equality. For the second, with W(N) = Sum_{j<=N} (j+1) C(j+2,2)/(N-j)! one has
(N+1) s(N+1) = W(N) + s(N) and t(N+1) = t(N) + W(N). -/

namespace A281946Aux

open OMA.S_oeis_a281946

noncomputable def s (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, ((j + 2).choose 2 : ℚ) / ((n - 1 - j).factorial : ℚ)

noncomputable def t (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n,
    (((j + 3).choose 3 : ℚ) + 3 * ((j + 3).choose 4 : ℚ)) / ((n - 1 - j).factorial : ℚ)

noncomputable def W (N : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (N + 1), ((j : ℚ) + 1) * ((j + 2).choose 2 : ℚ) / ((N - j).factorial : ℚ)

theorem sum_Icc_two (f : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 2 (n + 1), f k = ∑ j ∈ Finset.range n, f (j + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact Finset.sum_Icc_succ_top (by omega) f

theorem sum_Icc_three (f : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 3 (n + 2), f k = ∑ j ∈ Finset.range n, f (j + 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact Finset.sum_Icc_succ_top (by omega) f

theorem a_eq (n : ℕ) : a n = (n.factorial : ℚ) * t n := by
  unfold a t
  rw [sum_Icc_three]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  show (((j + 3).choose 3 : ℚ) + 3 * ((j + 3).choose 4 : ℚ)) / ((n + 2 - (j + 3)).factorial : ℚ) = _
  rw [show n + 2 - (j + 3) = n - 1 - j by omega]

theorem b_eq (n : ℕ) : b n = (n.factorial : ℚ) * s n := by
  unfold b s
  rw [sum_Icc_two]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  show ((j + 2).choose 2 : ℚ) / ((n + 1 - (j + 2)).factorial : ℚ) = _
  rw [show n + 1 - (j + 2) = n - 1 - j by omega]

theorem stirling_two (i : ℕ) :
    Nat.stirlingSecond (i + 2) i = (i + 2).choose 3 + 3 * (i + 2).choose 4 := by
  induction i with
  | zero => decide
  | succ i ih =>
    have h1 : Nat.stirlingSecond (i + 3) (i + 1) =
        (i + 1) * Nat.stirlingSecond (i + 2) (i + 1) + Nat.stirlingSecond (i + 2) i :=
      Nat.stirlingSecond_succ_succ (i + 2) i
    have h2 : Nat.stirlingSecond (i + 2) (i + 1) = (i + 2).choose 2 :=
      Nat.stirlingSecond_succ_self_left (i + 1)
    have h3 : (i + 3).choose 3 = (i + 2).choose 2 + (i + 2).choose 3 := Nat.choose_succ_succ' (i + 2) 2
    have h4 : (i + 3).choose 4 = (i + 2).choose 3 + (i + 2).choose 4 := Nat.choose_succ_succ' (i + 2) 3
    have h5 : (i + 2).choose 3 * 3 = (i + 2).choose 2 * i := Nat.choose_succ_right_eq (i + 2) 2
    show Nat.stirlingSecond (i + 3) (i + 1) = (i + 3).choose 3 + 3 * (i + 3).choose 4
    rw [h1, h2, ih, h3, h4]
    nlinarith [h5]

theorem part1 (n : ℕ) : 3 * A 2 n / ((n + 2).choose 2 : ℚ) = (n.factorial : ℚ) * t n := by
  have key : ∀ j ∈ Finset.range n,
      ((2 + n).factorial : ℚ) * (Nat.stirlingSecond (2 + (j + 1)) (j + 1) : ℚ) /
          ((n - (j + 1)).factorial : ℚ) =
        (((n : ℚ) + 2) * ((n : ℚ) + 1)) * ((n.factorial : ℚ) *
          ((((j + 3).choose 3 : ℚ) + 3 * ((j + 3).choose 4 : ℚ)) / ((n - 1 - j).factorial : ℚ))) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show 2 + (j + 1) = (j + 1) + 2 by omega, stirling_two (j + 1), show j + 1 + 2 = j + 3 by omega,
      show 2 + n = n + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ,
      show n - (j + 1) = n - 1 - j by omega]
    push_cast
    ring
  have hz : ((2 + n).factorial : ℚ) * (Nat.stirlingSecond (2 + 0) 0 : ℚ) / ((n - 0).factorial : ℚ) = 0 := by
    rw [show Nat.stirlingSecond (2 + 0) 0 = 0 by decide]
    simp
  have h3 : ((2 + 1).factorial : ℚ) = 6 := by norm_num [Nat.factorial]
  have hC : ((n + 2).choose 2 : ℚ) = ((n : ℚ) + 2) * ((n : ℚ) + 1) / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hne : ((n : ℚ) + 2) * ((n : ℚ) + 1) / 2 ≠ 0 := by positivity
  unfold A t
  rw [Finset.sum_range_succ', Finset.sum_congr rfl key, hz, add_zero, ← Finset.mul_sum, ← Finset.mul_sum, h3, hC,
    div_eq_iff hne]
  ring

theorem A1 (N : ℕ) : ((N : ℚ) + 1) * s (N + 1) = W N + s N := by
  have hs : s (N + 1) =
      ∑ j ∈ Finset.range (N + 1), ((j + 2).choose 2 : ℚ) / ((N - j).factorial : ℚ) := by
    unfold s
    apply Finset.sum_congr rfl
    intro j hj
    rw [show N + 1 - 1 - j = N - j by omega]
  have hsN : s N = ∑ j ∈ Finset.range (N + 1),
      ((N - j : ℕ) : ℚ) * ((j + 2).choose 2 : ℚ) / ((N - j).factorial : ℚ) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, zero_div, add_zero]
    unfold s
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hfac : ((N - j).factorial : ℚ) = ((N - j : ℕ) : ℚ) * ((N - 1 - j).factorial : ℚ) := by
      rw [show N - j = (N - 1 - j) + 1 by omega, Nat.factorial_succ]
      push_cast
      ring
    have hpos : ((N - j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hfac, mul_div_mul_left _ _ hpos]
  rw [hs, hsN]
  unfold W
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hcast : ((N - j : ℕ) : ℚ) = (N : ℚ) - (j : ℚ) := by
    rw [Nat.cast_sub (by omega)]
  rw [hcast]
  ring

theorem A2 (N : ℕ) : t (N + 1) = t N + W N := by
  unfold t W
  rw [Finset.sum_range_succ', Finset.sum_range_succ', ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have i1 : (j + 4).choose 3 = (j + 3).choose 2 + (j + 3).choose 3 := Nat.choose_succ_succ' (j + 3) 2
    have i2 : (j + 4).choose 4 = (j + 3).choose 3 + (j + 3).choose 4 := Nat.choose_succ_succ' (j + 3) 3
    have i3 : (j + 3).choose 3 * 3 = (j + 3).choose 2 * (j + 1) := Nat.choose_succ_right_eq (j + 3) 2
    have i3' : ((j + 3).choose 3 : ℚ) * 3 = ((j + 3).choose 2 : ℚ) * ((j : ℚ) + 1) := by exact_mod_cast i3
    rw [show N + 1 - 1 - (j + 1) = N - 1 - j by omega, show N - (j + 1) = N - 1 - j by omega,
      show j + 1 + 3 = j + 4 by omega, show j + 1 + 2 = j + 3 by omega, i1, i2, ← add_div]
    congr 1
    push_cast
    linear_combination i3'
  all_goals norm_num [Nat.choose]

theorem part2 (m : ℕ) :
    a (m + 1 + 1) = ((m : ℚ) + 2) * (a (m + 1) + b (m + 1 + 1) - b (m + 1)) := by
  have hf : ((m + 1 + 1).factorial : ℚ) = ((m : ℚ) + 2) * ((m + 1).factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have h1 := A1 (m + 1)
  have h2 := A2 (m + 1)
  rw [a_eq (m + 1 + 1), a_eq (m + 1), b_eq (m + 1 + 1), b_eq (m + 1), h2, hf]
  push_cast at h1 ⊢
  linear_combination (-(((m : ℚ) + 2) * ((m + 1).factorial : ℚ))) * h1

end A281946Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a281946.main := by
  constructor
  · intro n _
    rw [A281946Aux.a_eq, A281946Aux.part1]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
    rw [show m + 1 + 1 - 1 = m + 1 from rfl, A281946Aux.part2 m]
    push_cast
    ring
