import OMAStatements.S_oeis_a057083

-- Credit: @oh-meh
open OMA.S_oeis_a057083 Finset

private def b (n r : ℕ) : ℤ :=
  ∑ j ∈ range (n+1), (-1)^j * (n.choose (3*j+r) : ℤ)

private theorem truncate_b (n r : ℕ) :
    (∑ j ∈ range (n/3+1), (-1)^j * (n.choose (3*j+r) : ℤ)) = b n r := by
  apply sum_subset (range_mono (by omega))
  intro j hj hj'
  simp only [mem_range] at hj hj'
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

private theorem b_next (n r : ℕ) : b (n+1) (r+1) = b n r + b n (r+1) := by
  unfold b
  rw [sum_range_succ, Nat.choose_eq_zero_of_lt (by omega : n+1 < 3*(n+1)+(r+1))]
  simp only [Nat.cast_zero, mul_zero, add_zero, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [← Nat.add_assoc, Nat.choose_succ_succ, Nat.cast_add, mul_add]

private theorem b_wrap (n : ℕ) : b (n+1) 0 = b n 0 - b n 2 := by
  have hp : b n 0 = ∑ j ∈ range (n+2), (-1)^j * (n.choose (3*j) : ℤ) := by
    rw [sum_range_succ, Nat.choose_eq_zero_of_lt (by omega : n < 3*(n+1))]
    simp [b]
  rw [hp]
  unfold b
  simp only [Nat.add_zero]
  rw [sum_range_succ', sum_range_succ' (fun j => (-1:ℤ)^j * n.choose (3*j))]
  simp only [pow_zero, Nat.mul_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [show (∑ j ∈ range (n+1), (-1:ℤ)^(j+1) * n.choose (3*(j+1))) + 1 -
      (∑ j ∈ range (n+1), (-1:ℤ)^j * n.choose (3*j+2)) =
      (∑ j ∈ range (n+1), ((-1:ℤ)^(j+1) * n.choose (3*(j+1)) -
      (-1:ℤ)^j * n.choose (3*j+2))) + 1 by rw [sum_sub_distrib]; ring]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [show 3*(j+1)=3*j+2+1 by omega, Nat.choose_succ_succ, Nat.cast_add, pow_succ]
  ring

private theorem b_two (n : ℕ) : b n 2 = z n := by
  match n with
  | 0 | 1 | 2 | 3 => decide
  | n+4 =>
    change b (n+4) 2 = 3 * a (n+1) - 3 * a n
    have h₁ := b_two (n+3)
    have h₀ := b_two (n+2)
    change b (n+3) 2 = a (n+1) at h₁
    change b (n+2) 2 = a n at h₀
    rw [← h₁, ← h₀]
    have h : b (n+1) 0 - b (n+1) 1 + b (n+1) 2 = 0 := by
      rw [b_wrap, b_next n 0, b_next n 1]
      ring
    have hu := b_wrap (n+1)
    have hv := b_next (n+1) 0
    have hw := b_next (n+1) 1
    have hv' := b_next (n+2) 0
    have hw' := b_next (n+2) 1
    have hw'' := b_next (n+3) 1
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a057083.main := by
  intro K V _ _ _ M hM n
  rw [show A057681 n = b n 0 from truncate_b n 0,
    show A057682 n = b n 1 from truncate_b n 1, ← b_two]
  induction n with
  | zero => simp [b]
  | succ n ih =>
    rw [pow_succ, ih, b_wrap, b_next n 0, b_next n 1]
    simp only [mul_sub, mul_one, add_mul, sub_mul, smul_mul_assoc, one_mul,
      ← pow_succ, hM, add_zsmul, sub_zsmul]
    rw [← sq M]
    abel
