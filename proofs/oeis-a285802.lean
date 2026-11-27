import OMAStatements.S_oeis_a285802

-- Problem: A285802, "35 is the highest value to occur" for the least k with a 7 in k*n.
-- Credit: @ShoQo
-- Proof: trailing zeros of n only append zeros to k*n, so reduce to n with n % 10 ≠ 0. The last
-- two digits of k*n depend only on k and n % 100, and a finite check over the 90 residues finds
-- k ≤ 35 with a 7 among them.

open OMA.S_oeis_a285802

namespace OMA_A285802_Proof

/-- A 7 among the last two digits of `x` is a 7 in its decimal expansion. -/
lemma hasSeven_of_low {x : ℕ} (h : x % 10 = 7 ∨ x / 10 % 10 = 7) : HasSeven x := by
  unfold HasSeven
  have hx : 0 < x := by rcases h with h | h <;> (rcases Nat.eq_zero_or_pos x with rfl | hx <;> simp_all)
  rw [Nat.digits_def' (by norm_num) hx]
  rcases h with h | h
  · rw [h]; exact List.mem_cons_self
  · have hy : 0 < x / 10 := by
      rcases Nat.eq_zero_or_pos (x / 10) with h0 | h0
      · rw [h0] at h; simp at h
      · exact h0
    rw [Nat.digits_def' (by norm_num) hy, h]
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The finite check: every residue mod 100 not ending in 0 has a good multiplier `k ≤ 35`. -/
lemma residue_check : ∀ r < 100, r % 10 ≠ 0 →
    ∃ k < 36, 1 ≤ k ∧ ((k * r) % 10 = 7 ∨ (k * r) / 10 % 10 = 7) := by
  decide +kernel

lemma hasSeven_mul_ten {x : ℕ} (hx : 0 < x) (h : HasSeven x) : HasSeven (10 * x) := by
  unfold HasSeven at *
  rw [Nat.digits_def' (by norm_num) (by omega)]
  simp only [Nat.mul_mod_right, Nat.mul_div_cancel_left x (by norm_num : 0 < 10)]
  exact List.mem_cons_of_mem _ h

lemma good (n : ℕ) (hn : 1 ≤ n) : ∃ k : ℕ, 1 ≤ k ∧ k ≤ 35 ∧ HasSeven (k * n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h0 : n % 10 = 0
    · obtain ⟨m, rfl⟩ : ∃ m, n = 10 * m := ⟨n / 10, by omega⟩
      obtain ⟨k, hk1, hk35, hk⟩ := ih m (by omega) (by omega)
      refine ⟨k, hk1, hk35, ?_⟩
      rw [show k * (10 * m) = 10 * (k * m) by ring]
      exact hasSeven_mul_ten (Nat.mul_pos (by omega) (by omega)) hk
    · obtain ⟨k, hk35, hk1, hk⟩ := residue_check (n % 100) (Nat.mod_lt _ (by norm_num)) (by omega)
      refine ⟨k, hk1, by omega, hasSeven_of_low ?_⟩
      have hm : (k * n) % 100 = (k * (n % 100)) % 100 := by
        rw [Nat.mul_mod k n, Nat.mul_mod k (n % 100), Nat.mod_mod]
      omega

end OMA_A285802_Proof

open OMA_A285802_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a285802.main := by
  refine ⟨good, ?_, ?_⟩
  · intro k hk1 hk35
    unfold HasSeven
    interval_cases k <;> norm_num
  · unfold HasSeven; norm_num
