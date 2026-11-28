import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k hk B hB hf ⟨a, d, hd, h⟩
  choose! j b hb e using h
  have gap {x y : ℕ} (h : x < y) : 4 * 4 ^ x ≤ 4 ^ y := by
    simpa [pow_succ'] using Nat.pow_le_pow_right (by decide : 0 < 4) h
  have q i (hi : i < k) := And.intro (e i hi) (Finset.mem_Icc.mp (hB _ (hb _ hi)))
  have tri i (hi : i + 2 < k) : j i = j (i+1) ∧ j (i+1) = j (i+2) := by
    have := q i (by omega)
    have u := q (i+1) (by omega)
    have v := q (i+2) hi
    simp only [Nat.add_mul, one_mul] at u v
    rcases lt_trichotomy (j i) (j (i+1)) with t|t|t <;>
      rcases lt_trichotomy (j (i+1)) (j (i+2)) with s|s|s <;>
      (try have := gap t) <;> (try have := gap s) <;> grind
  have same i (hi : i < k) : j i = j 0 := by
    induction i using Nat.twoStepInduction with
    | zero => rfl
    | one => grind [tri 0]
    | more i _ _ => grind [tri i]
  apply hf (j 0)
  refine ⟨b 0, d, hd, fun i hi ↦ ?_⟩
  have := e 0 (by omega)
  have z := e i hi
  rw [same i hi] at z
  simpa only [same i hi, show b i = b 0 + i * d by omega] using hb i hi
