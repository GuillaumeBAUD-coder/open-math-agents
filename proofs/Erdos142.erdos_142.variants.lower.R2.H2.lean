import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

-- Step Erdos142.erdos_142.variants.lower.R2.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2
-- Credit: @ishaanzee
-- Proof: the blocks (4*4^j, 5*4^j] are far apart, so a progression with at least three terms in
-- their union has all terms in one block; shifting back gives a progression in B j.

namespace E142Aux

lemma four_mul_pow_le {j j' : ℕ} (h : j < j') : 4 * 4 ^ j ≤ 4 ^ j' := by
  calc 4 * 4 ^ j = 4 ^ (j + 1) := by ring
    _ ≤ 4 ^ j' := Nat.pow_le_pow_right (by norm_num) h

/-- The blocks `(4 * 4 ^ j, 5 * 4 ^ j]` are so far apart that a progression with at least three
terms in their union stays inside one block, where it is a progression of `B j` shifted. -/
theorem core (k : ℕ) (hk : 3 ≤ k) (B : ℕ → Finset ℕ) (hB : ∀ j, B j ⊆ Finset.Icc 1 (4 ^ j))
    (hfree : ∀ j, ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ B j)
    (a d : ℕ) (hd : 0 < d) (h : ∀ i < k, ∃ j b, b ∈ B j ∧ a + i * d = 4 * 4 ^ j + b) : False := by
  choose! J bb hbmem hxeq using h
  have hbnd : ∀ i < k, 4 * 4 ^ J i < a + i * d ∧ a + i * d ≤ 5 * 4 ^ J i := by
    intro i hi
    have := Finset.mem_Icc.1 (hB _ (hbmem i hi))
    rw [hxeq i hi]
    constructor <;> omega
  have h0 := hbnd 0 (by omega)
  have h1 := hbnd 1 (by omega)
  have h2 := hbnd 2 (by omega)
  simp only [one_mul, zero_mul, add_zero] at h0 h1
  have hJ12 : J 1 = J 2 := by
    rcases lt_trichotomy (J 1) (J 2) with hlt | heq | hgt
    · have := four_mul_pow_le hlt
      omega
    · exact heq
    · have := four_mul_pow_le hgt
      omega
  set P := 4 ^ J 1 with hP
  have h2' : 4 * P < a + 2 * d ∧ a + 2 * d ≤ 5 * P := by rw [hP, hJ12]; exact h2
  have hdP : d < P := by omega
  have hJ0 : J 0 = J 1 := by
    rcases lt_trichotomy (J 0) (J 1) with hlt | heq | hgt
    · have := four_mul_pow_le hlt
      omega
    · exact heq
    · have := four_mul_pow_le hgt
      omega
  have hJup : ∀ m, 2 + m < k → J (2 + m) = J 1 := by
    intro m
    induction m with
    | zero => intro _; exact hJ12.symm
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      have hprev := hbnd (2 + m) (by omega)
      rw [ih'] at hprev
      have hcur := hbnd (2 + (m + 1)) (by omega)
      have hstep : a + (2 + (m + 1)) * d = a + (2 + m) * d + d := by ring
      rw [hstep] at hcur
      rcases lt_trichotomy (J (2 + (m + 1))) (J 1) with hlt | heq | hgt
      · have := four_mul_pow_le hlt
        omega
      · exact heq
      · have := four_mul_pow_le hgt
        omega
  have hJall : ∀ i < k, J i = J 1 := by
    intro i hi
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · interval_cases i
      · exact hJ0
      · rfl
    · have := hJup (i - 2) (by omega)
      rwa [show 2 + (i - 2) = i by omega] at this
  apply hfree (J 1)
  refine ⟨bb 0, d, hd, fun i hi => ?_⟩
  have e1 := hxeq i hi
  have e0 := hxeq 0 (by omega)
  rw [hJall i hi] at e1
  rw [hJ0] at e0
  simp only [zero_mul, add_zero] at e0
  have : bb 0 + i * d = bb i := by omega
  rw [this, ← hJall i hi]
  exact hbmem i hi

end E142Aux

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  rintro k hk B hB hfree ⟨a, d, hd, h⟩
  exact E142Aux.core k hk B hB hfree a d hd h
