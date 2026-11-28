import OMAStatements.S_oeis_a273400

open OMA.S_oeis_a273400

private lemma L (n : ℕ) : 2 ^ n ≤ catalan (n + 1) := by
  induction n with
  | zero => simp [catalan_one]
  | succ n ih =>
    rw [catalan_succ, Fin.sum_univ_succ, Fin.sum_univ_castSucc, pow_succ]
    simp [catalan_zero]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a273400.main := by
  have q (m : ℕ) : 4 * m + 25 ≤ 2 ^ (m + 5) := by
    induction m with
    | zero => norm_num
    | succ m ih => rw [pow_succ]; omega
  refine (Set.finite_lt_nat 4).subset fun n hn => ?_
  by_contra h
  simp only [Set.mem_ofPred_eq, not_lt] at h hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, catalan (k + 4) = m + 6 :=
    ⟨_, (Nat.sub_add_cancel (le_trans (by norm_num) ((Nat.pow_le_pow_right two_pos
      (by omega : 3 ≤ k + 3)).trans (L (k + 3))))).symm⟩
  have h1 : 4 * m + 25 ≤ catalan (m + 6) := (q m).trans (L _)
  have h2 := L (catalan (m + 6) - 1)
  rw [Nat.sub_add_cancel (by omega)] at h2
  have h3 : 10 ^ (m + 6) ≤ 2 ^ (catalan (m + 6) - 1) :=
    (Nat.pow_le_pow_left (by norm_num : 10 ≤ 2 ^ 4) _).trans
      (by rw [← pow_mul]; exact Nat.pow_le_pow_right two_pos (by omega))
  have h4 := Nat.lt_base_pow_length_digits (b := 10) (m := a (k + 4)) (by norm_num)
  have h5 := Nat.pow_le_pow_right (by norm_num : 0 < 10) hn.le
  unfold a at h4 h5
  rw [hm] at h4 h5
  omega
