import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k g B H f ⟨a, d, D, h⟩
  choose! j b c e using h
  have E {x y} (_ : 4 ^ x < 4 ^ y * 4) (_ : 4 ^ y < 4 ^ x * 4) : x = y := by
    by_contra! n; rcases n.lt_or_gt with t | t <;> have := Nat.pow_le_pow_right zero_lt_four t <;> omega
  have Q i t : _ ∧ _ := ⟨Finset.mem_Icc.1 (H _ (c i t)), e i t⟩
  have := Q 1 (by omega); have := Q 2 g
  rw [show j 1 = j 2 from E (by omega) (by omega)] at *
  have : d ≤ a := by omega
  have S i : i < k → j i = j 0 := by
    induction' i with i p
    · simp
    ·
      intro t; have := Q i (by omega); have := Q (i + 1) t; have := add_mul i 1 d
      exact (E (by omega) (by omega)).trans (p (by omega))
  refine f (j 0) ⟨b 0, d, D, fun i t => ?_⟩
  have q := S i t; have := e 0 (by omega); have := e i t; have := congrArg (4 ^ ·) q
  rw [show b 0 + i * d = b i by omega, ← q]; exact c i t
