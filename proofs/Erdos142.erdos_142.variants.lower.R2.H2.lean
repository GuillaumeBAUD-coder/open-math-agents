import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

/-! Variations on the geometric block argument in PRs #5265 and #37307.
The second and third terms have the same block because their ratio is at most two.
Their separation then bounds the common difference by the first term. -/

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k hk B hB hf ⟨a, d, hd, h⟩
  choose! j b mem place using h
  have gap {u v : ℕ} (h : u < v) : 4 * 4 ^ u ≤ 4 ^ v := by
    simpa only [pow_succ'] using (Nat.pow_le_pow_right (by decide : 0 < 4) h)
  have bounds i (hi : i < k) : 4 * 4 ^ j i < a + i * d ∧ a + i * d ≤ 5 * 4 ^ j i := by
    have := Finset.mem_Icc.mp (hB _ (mem i hi))
    have := place i hi
    omega
  have near i (hi : i + 1 < k) (h : d ≤ a + i * d) : j i = j (i + 1) := by
    have := bounds i (by omega)
    have next := bounds (i + 1) hi
    rw [add_mul, one_mul] at next
    rcases lt_trichotomy (j i) (j (i + 1)) with h | h | h
    · have := gap h; omega
    · exact h
    · have := gap h; omega
  have hsmall : d ≤ a := by
    have h12 := near 1 (by omega) (by omega)
    have := bounds 1 (by omega)
    have third := bounds 2 (by omega)
    rw [← h12] at third
    omega
  have same i (hi : i < k) : j i = j 0 := by
    induction i with
    | zero => rfl
    | succ i ih => exact (near i hi (by omega)).symm.trans (ih (by omega))
  refine hf (j 0) ⟨a - 4 * 4 ^ j 0, d, hd, fun i hi => ?_⟩
  have := bounds 0 (by omega)
  have eq := place i hi
  rw [same i hi] at eq
  rw [show a - 4 * 4 ^ j 0 + i * d = b i by omega, ← same i hi]
  exact mem i hi
