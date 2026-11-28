import OMAReductions.R_Erdos933_erdos_933_R1

/-! Powers of three minus one give infinitely many witnesses for the base bound. -/

theorem OMA.solution : OMA.R_Erdos933_erdos_933_R1.H1 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Set.infinite_of_injective_forall_mem
    (f := fun r : ℕ => 3 ^ (2 ^ (r + 1)) - 1) ?_ ?_
  · intro i j h
    have hi : 0 < (3 : ℕ) ^ (2 ^ (i + 1)) := by positivity
    have hj : 0 < (3 : ℕ) ^ (2 ^ (j + 1)) := by positivity
    have hp : (3 : ℕ) ^ (2 ^ (i + 1)) = 3 ^ (2 ^ (j + 1)) := by
      change 3 ^ (2 ^ (i + 1)) - 1 = 3 ^ (2 ^ (j + 1)) - 1 at h
      omega
    exact add_left_injective 1
      (Nat.pow_right_injective (a := 2) (by decide)
        (Nat.pow_right_injective (a := 3) (by decide) hp))
  · intro r
    let m : ℕ := 2 ^ (r + 1)
    let n : ℕ := 3 ^ m - 1
    have hm : 0 < m := by positivity
    have hn : 0 < n := Nat.sub_pos_of_lt (one_lt_pow₀ (by decide) hm.ne')
    have hpow : 0 < (3 : ℕ) ^ m := by positivity
    have hnext : n + 1 = 3 ^ m := Nat.sub_add_cancel hpow
    have heven : Even m := by
      dsimp [m]
      rw [pow_succ]
      exact Nat.even_mul.mpr (Or.inr (by decide))
    have hval2 := padicValNat.pow_two_sub_one_ge (x := 3) (n := m)
      (by decide) (by decide) hm.ne' heven
    have hk : r + 2 ≤ Erdos933.k n := by
      rw [Erdos933.k, padicValNat.mul hn.ne' (Nat.succ_ne_zero n)]
      have hvm : padicValNat 2 m = r + 1 := padicValNat.prime_pow (r + 1)
      rw [hvm] at hval2
      change r + 1 + 2 ≤ padicValNat 2 n at hval2
      omega
    have hl : m ≤ Erdos933.l n := by
      rw [Erdos933.l, padicValNat.mul hn.ne' (Nat.succ_ne_zero n)]
      change m ≤ padicValNat 3 n + padicValNat 3 (n + 1)
      rw [hnext, padicValNat.prime_pow]
      omega
    have h2 : 2 * m ≤ 2 ^ Erdos933.k n := by
      simpa only [m, pow_succ 2 (r + 1), mul_comm] using
        (Nat.pow_le_pow_right (by decide : 0 < 2) hk)
    have h3 : n < 3 ^ Erdos933.l n := by
      exact (show n < 3 ^ m by omega).trans_le (Nat.pow_le_pow_right (by decide) hl)
    have hlog3 : Real.log 3 < 2 := by
      have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
        (show (3 : ℝ) ≠ 1 by norm_num)
      norm_num at h
      exact h
    have hlog : Real.log (n : ℝ) < 2 * (m : ℝ) := by
      calc
        Real.log (n : ℝ) < Real.log ((3 : ℝ) ^ m) :=
          Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast (show n < 3 ^ m by omega))
        _ = (m : ℝ) * Real.log 3 := Real.log_pow _ _
        _ < 2 * (m : ℝ) := by
          rw [mul_comm 2]
          exact mul_lt_mul_of_pos_left hlog3 (by exact_mod_cast hm)
    change (n : ℝ) * Real.log (n : ℝ) <
      ((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ)
    calc
      _ < (n : ℝ) * (2 * (m : ℝ)) := mul_lt_mul_of_pos_left hlog (by exact_mod_cast hn)
      _ ≤ _ := by
        exact_mod_cast (show n * (2 * m) ≤ 2 ^ Erdos933.k n * 3 ^ Erdos933.l n by
          rw [mul_comm n]
          exact Nat.mul_le_mul h2 h3.le)

