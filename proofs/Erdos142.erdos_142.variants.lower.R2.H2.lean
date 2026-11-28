import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

/-! Consecutive terms that increase by at most a factor of two stay in one block. -/

private theorem same_block {i j x y : ℕ}
    (hx : x ∈ Finset.Icc 1 (4 ^ i)) (hy : y ∈ Finset.Icc 1 (4 ^ j))
    (lo : 4 * 4 ^ i + x ≤ 4 * 4 ^ j + y)
    (hi : 4 * 4 ^ j + y ≤ 2 * (4 * 4 ^ i + x)) : i = j := by
  have scale {s t : ℕ} (h : s < t) : 4 * 4 ^ s ≤ 4 ^ t := by
    simpa only [pow_succ'] using
      (show (4 : ℕ) ^ (s + 1) ≤ 4 ^ t from Nat.pow_le_pow_right (by decide) h)
  obtain ⟨hx0, hx1⟩ := Finset.mem_Icc.mp hx
  obtain ⟨hy0, hy1⟩ := Finset.mem_Icc.mp hy
  rcases lt_trichotomy i j with h | h | h
  · have := scale h
    omega
  · exact h
  · have := scale h
    omega

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k hk B hB hfree ⟨a, d, hd, h⟩
  obtain ⟨j, x, hx, ex⟩ := h 0 (by omega)
  obtain ⟨l, y, hy, ey⟩ := h 1 (by omega)
  obtain ⟨m, z, hz, ez⟩ := h 2 (by omega)
  simp only [zero_mul, add_zero, one_mul] at ex ey ez
  have hlm := same_block (hB l hy) (hB m hz) (by omega) (by omega)
  subst m
  have hdle : d ≤ a := by
    have hy' := Finset.mem_Icc.mp (hB l hy)
    have hz' := Finset.mem_Icc.mp (hB l hz)
    omega
  have all (i : ℕ) (hi : i < k) :
      ∃ b ∈ B j, a + i * d = 4 * 4 ^ j + b := by
    induction i with
    | zero => exact ⟨x, hx, by simpa using ex⟩
    | succ i ih =>
      obtain ⟨u, hu, eu⟩ := ih (by omega)
      obtain ⟨t, v, hv, ev⟩ := h (i + 1) hi
      rw [Nat.add_mul, Nat.one_mul] at ev
      have he := same_block (hB j hu) (hB t hv) (by omega) (by omega)
      exact ⟨v, he.symm ▸ hv, by rw [Nat.add_mul, Nat.one_mul, ev, ← he]⟩
  apply hfree j
  refine ⟨a - 4 * 4 ^ j, d, hd, fun i hi => ?_⟩
  obtain ⟨b, hb, e⟩ := all i hi
  rwa [show a - 4 * 4 ^ j + i * d = b by omega]

