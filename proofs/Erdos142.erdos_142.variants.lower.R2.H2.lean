import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

/-!
The first two points of a progression must share a block. A pair in different
blocks would place the third point in a gap. Then the common difference is
smaller than the next gap, so the whole progression stays in that block.
Builds on Salofe's proof and weizj99's revision in PR 32324.
-/

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k hk B hB hfree ⟨a, d, hd, h⟩
  have gap {i j : ℕ} (hij : i < j) : 4 * 4 ^ i ≤ 4 ^ j := by
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by decide) hij
  have separated (i j : ℕ) := (lt_trichotomy i j).imp gap (Or.imp id gap)
  have bounds {j b : ℕ} (hb : b ∈ B j) := Finset.mem_Icc.mp (hB j hb)
  obtain ⟨j0, b0, hb0, e0⟩ := h 0 (by omega)
  obtain ⟨j1, b1, hb1, e1⟩ := h 1 (by omega)
  obtain ⟨j2, b2, hb2, e2⟩ := h 2 (by omega)
  have h0 := bounds hb0
  have h1 := bounds hb1
  have h2 := bounds hb2
  simp only [zero_mul, add_zero, one_mul] at e0 e1
  have same : j0 = j1 := by
    rcases separated j0 j1 with hj | hj | hj
    · rcases separated j1 j2 with hnext | rfl | hnext <;> omega
    · exact hj
    · omega
  subst j0
  have small : d < 4 ^ j1 := by omega
  have inside : ∀ i < k, ∃ b ∈ B j1, a + i * d = 4 * 4 ^ j1 + b := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨b0, hb0, by simpa using e0⟩
    | succ i ih =>
      intro hi
      obtain ⟨b, hb, e⟩ := ih (by omega)
      obtain ⟨j, b', hb', e'⟩ := h (i + 1) hi
      have := bounds hb
      have := bounds hb'
      rw [Nat.add_mul, one_mul] at e'
      rcases separated j1 j with hj | rfl | hj
      · omega
      · exact ⟨b', hb', by simpa [Nat.add_mul] using e'⟩
      · omega
  apply hfree j1
  refine ⟨a - 4 * 4 ^ j1, d, hd, fun i hi => ?_⟩
  obtain ⟨b, hb, e⟩ := inside i hi
  rwa [show a - 4 * 4 ^ j1 + i * d = b by omega]
