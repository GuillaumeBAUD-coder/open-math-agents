import OMAReductions.R_Erdos311_delta_ge_exp_R1

-- Step Erdos311.delta_ge_exp.R1.H2: hypothesis H2 of reduction Erdos311.delta_ge_exp.R1
-- Credit: @YourFriendPollux
-- H2 := ∀ N : ℕ, 1 / ((Nat.lcmUpto N : ℝ)) ≤ Erdos311.delta N

open Finset

theorem OMA.solution : OMA.R_Erdos311_delta_ge_exp_R1.H2 := by
  intro N
  unfold Erdos311.delta
  apply le_csInf
  · refine ⟨1, one_ne_zero, ∅, empty_subset _, ?_⟩
    simp
  · intro x hx
    obtain ⟨hx0, A, hA, rfl⟩ := hx
    have hLpos : (0:ℝ) < Nat.lcmUpto N := by exact_mod_cast Nat.lcmUpto_pos N
    have hLne : (Nat.lcmUpto N : ℝ) ≠ 0 := ne_of_gt hLpos
    have hdiv : ∀ n ∈ A, n ∣ Nat.lcmUpto N :=
      fun n hn => Finset.dvd_lcm (show n ∈ Finset.Icc 1 N from hA hn)
    have hterm : ∀ n ∈ A, (1:ℝ)/n = ((Nat.lcmUpto N / n : ℕ) : ℝ) / Nat.lcmUpto N := by
      intro n hn
      have h1n : 1 ≤ n := (Finset.mem_Icc.mp (hA hn)).1
      have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : 0 < n).ne'
      have hLn : (Nat.lcmUpto N : ℝ) = n * ((Nat.lcmUpto N / n : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' (hdiv n hn)]
      rw [div_eq_div_iff hn0 hLne]
      rw [hLn]
      ring
    have hsum : ∑ n ∈ A, (1:ℝ)/n =
        (((∑ n ∈ A, Nat.lcmUpto N / n : ℕ) : ℝ) / Nat.lcmUpto N) := by
      rw [Finset.sum_congr rfl (fun n hn => hterm n hn), ← Finset.sum_div]
      push_cast
      rfl
    set m := ∑ n ∈ A, Nat.lcmUpto N / n with hm
    have hx' : |(1:ℝ) - ∑ n ∈ A, (1:ℝ)/n| = |((Nat.lcmUpto N : ℤ) - (m : ℤ) : ℤ)| / Nat.lcmUpto N := by
      rw [hsum]
      have hc : (1:ℝ) - ((m : ℝ) / Nat.lcmUpto N) = (((Nat.lcmUpto N : ℤ) - (m : ℤ) : ℤ) : ℝ) / Nat.lcmUpto N := by
        push_cast
        field_simp
      rw [hc, abs_div, abs_of_pos hLpos, Int.cast_abs]
    have hk0 : ((Nat.lcmUpto N : ℤ) - (m : ℤ) : ℤ) ≠ 0 := by
      intro hk
      apply hx0
      rw [hx']
      simp [hk]
    have h1 : (1:ℝ) ≤ |((Nat.lcmUpto N : ℤ) - (m : ℤ) : ℤ)| := by
      have := Int.one_le_abs hk0
      exact_mod_cast this
    rw [hx']
    gcongr
