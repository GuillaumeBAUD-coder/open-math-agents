import OMAStatements.S_oeis_a133308

-- Credit: @asher-lanzone

open Finset OMA.S_oeis_a133308

private def B (n k : ℕ) : ℚ := n.choose k

private lemma row (n k : ℕ) : B n k * (n + 1) = B (n+1) k * (n + 1 - k) := by
  unfold B
  by_cases h : k ≤ n+1
  · exact_mod_cast (show (n.choose k : ℚ) * ((n+1 : ℕ) : ℚ) = ((n+1).choose k : ℚ) * ((n+1 : ℕ) - (k : ℚ)) by
      rw [← Nat.cast_sub h]; exact_mod_cast Nat.choose_mul_succ_eq n k)
  · simp [Nat.choose_eq_zero_of_lt (show n < k by omega), Nat.choose_eq_zero_of_lt (show n+1 < k by omega)]

private lemma col (n k : ℕ) : B n (k+1) * (k+1) = B n k * (n-k) := by
  unfold B
  by_cases h : k ≤ n
  · rw [← Nat.cast_sub h]; exact_mod_cast Nat.choose_succ_right_eq n k
  · simp [Nat.choose_eq_zero_of_lt (show n < k by omega), Nat.choose_eq_zero_of_lt (show n < k+1 by omega)]

private def T (n k : ℕ) : ℚ := B n k * B n (k+1) * 8^n * (7/8)^k

private lemma trow (n k : ℕ) : 8*(n+1)^2*T n k = (n+1-k)*(n-k)*T (n+1) k := by
  unfold T
  rw [pow_succ (8 : ℚ)]
  have h := row n (k+1)
  push_cast at h
  linear_combination (B n (k+1) * 8^n * (7/8)^k * 8 * (n+1)) * row n k +
    (B (n+1) k * 8^n * (7/8)^k * 8 * (n+1-k)) * h

private lemma tcol (n k : ℕ) : 8*(k+1)*(k+2)*T n (k+1) = 7*(n-k)*(n-k-1)*T n k := by
  unfold T
  rw [pow_succ (7/8 : ℚ)]
  have h := col n (k+1)
  push_cast at h
  linear_combination (B n (k+1+1) * 8^n * (7/8)^k * 7 * (k+2)) * col n k +
    (B n k * 8^n * (7/8)^k * 7 * (n-k)) * h

private def Q (n k : ℚ) := -k^2 + (18*n-17)*k -25*n^2 +33*n-8
private def F (n k : ℕ) : ℚ := 8*k*(k+1)*Q n k*T n k

private lemma point (n k : ℕ) :
    64*(n+3)*(n+2)*(n+1)^2*T (n+2) k +
    960*(1-2*(n+2))*(n+1)*(n+2)^2*T (n+1) k +
    64*(n+2)^2*(n+1)^2*T n k = F (n+2) (k+1) - F (n+2) k := by
  have h := trow (n+1) k
  have g := tcol (n+2) k
  unfold F Q
  push_cast at h g ⊢
  linear_combination (8*(n+2)^2)*trow n k +
    (((n+1-k)*(n-k)) + 120*(1-2*(n+2))*(n+1))*h -
    (-(k+1)^2 + (18*(n+2)-17)*(k+1) -25*(n+2)^2 +33*(n+2)-8)*g

private lemma T_zero {n k : ℕ} (h : n ≤ k) : T n k = 0 := by
  simp [T, B, Nat.choose_eq_zero_of_lt (show n < k+1 by omega)]

private lemma sum_T (n m : ℕ) (h : n ≤ m) : ∑ k ∈ range m, T n k = (n : ℚ)*a n := by
  rw [← sum_subset_zero_on_sdiff (s₁ := range n) (s₂ := range m) (g := T n) (f := T n) (range_mono h)]
  · cases n with
    | zero => simp
    | succ n =>
      rw [a, if_neg (by omega)]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity)]
      apply sum_congr rfl; intro k hk
      have hk' : k ≤ n+1 := (mem_range.mp hk).le
      unfold T B
      have hp : (8 : ℚ)^(n+1) = 8^(n+1-k)*8^k := by rw [← pow_add, Nat.sub_add_cancel hk']
      rw [div_pow, hp]
      field_simp
  · intro k hk; exact T_zero (by simpa only [mem_range, not_lt] using (mem_sdiff.mp hk).2)
  · simp

theorem OMA.solution : type_of% @OMA.S_oeis_a133308.main := by
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
  have e := sum_congr (s₁ := range (n+2)) rfl (fun k _ => point n k)
  rw [sum_range_sub (F (n+2))] at e
  simp only [sum_add_distrib, ← mul_sum, F, T_zero (le_refl (n+2)), Nat.cast_zero,
    mul_zero, zero_mul, sub_zero] at e
  rw [sum_T _ _ (by omega), sum_T _ _ (by omega), sum_T _ _ (by omega)] at e
  rw [show n+2-1 = n+1 by omega, show n+2-2=n by omega]
  simp only [Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one] at e ⊢
  apply (mul_left_inj' (show (64*((n : ℚ)+2)^2*(n+1)^2 : ℚ) ≠ 0 by positivity)).mp
  linear_combination e
