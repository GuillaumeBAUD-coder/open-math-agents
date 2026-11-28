import FormalConjectures.ErdosProblems.«1148»

/-! With m = sqrt n and n - m^2 = e: e = 0 gives (m,0,0), e odd gives (m,j+1,j), e = 2(i+1) gives (m+1,k,k+1). Every square is at most n + 2m. -/

theorem OMA.solution : type_of% @Erdos1148.erdos_1148.variants.weaker := by
  intro n
  have h1 := Nat.sqrt_le' n
  have h2 : n < (n.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' n
  generalize n.sqrt = m at *
  have b (x : ℕ) (h : x ^ 2 ≤ n + 2 * m) : (x : ℝ) ^ 2 ≤ n + 2 * √n := by
    have : (m : ℝ) ≤ √n := Real.le_sqrt_of_sq_le (by exact_mod_cast h1)
    have : (x : ℝ) ^ 2 ≤ n + 2 * m := by exact_mod_cast h
    linarith
  rcases Nat.even_or_odd (n - m ^ 2) with ⟨_ | i, hi⟩ | ⟨j, hi⟩ <;>
    have hn := (Nat.sub_eq_iff_eq_add h1).1 hi
  · exact ⟨m, 0, 0, by simp [hn], b _ (by omega), b _ (by simp), b _ (by simp)⟩
  · have : i < m := by nlinarith
    obtain ⟨k, rfl⟩ : ∃ k, m = i + 1 + k := ⟨m - (i + 1), by omega⟩
    refine ⟨i + k + 2, k, k + 1, ?_, b _ (by nlinarith), b _ (by nlinarith), b _ (by nlinarith)⟩
    rw [eq_tsub_iff_add_eq_of_le (by nlinarith)]
    nlinarith
  · have : j < m := by nlinarith
    refine ⟨m, j + 1, j, ?_, b _ (by omega), b _ (by nlinarith), b _ (by nlinarith)⟩
    rw [eq_tsub_iff_add_eq_of_le (by nlinarith)]
    nlinarith
