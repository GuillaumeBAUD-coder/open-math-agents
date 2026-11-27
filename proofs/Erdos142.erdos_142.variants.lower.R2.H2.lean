import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

/-!
# Proof of `Erdos142.erdos_142.variants.lower.R2.H2`

We prove that packing progression-free blocks `B j ⊆ {1, ..., 4^j}` into disjoint intervals
`4 * 4^j + B j ⊆ (4 * 4^j, 5 * 4^j]` preserves the absence of `k`-term arithmetic progressions
for every `k ≥ 3`.

The key observation is that any 3-term arithmetic progression `x₀ + x₂ = 2 x₁` in
`⋃_j (4 * 4^j, 5 * 4^j]` must lie in a single block:
- If `j₁ < j₂`, then `x₂ > 4 * 4^(j₁ + 1) = 16 * 4^j₁ > 10 * 4^j₁ ≥ 2 x₁ = x₀ + x₂`.
- If `j₀ < j₁ = j₂`, then `4 * (x₀ + x₂) ≤ 5 * 4^j₁ + 20 * 4^j₁ = 25 * 4^j₁ < 32 * 4^j₁ < 4 * (2 x₁)`.
Hence all `k` terms lie in the same block `j`, contradicting that `B j` is `k`-AP-free.
-/

-- Credit: @skhakim

private lemma block_index_eq_of_three_ap {B : ℕ → Finset ℕ}
    (hB : ∀ j, B j ⊆ Finset.Icc 1 (4 ^ j))
    {x₀ x₁ x₂ j₀ j₁ j₂ b₀ b₁ b₂ : ℕ}
    (hb₀ : b₀ ∈ B j₀) (hb₁ : b₁ ∈ B j₁) (hb₂ : b₂ ∈ B j₂)
    (hx₀ : x₀ = 4 * 4 ^ j₀ + b₀) (hx₁ : x₁ = 4 * 4 ^ j₁ + b₁) (hx₂ : x₂ = 4 * 4 ^ j₂ + b₂)
    (hinc : x₀ < x₁) (hap : x₀ + x₂ = 2 * x₁) :
    j₀ = j₁ ∧ j₁ = j₂ := by
  have hb₀' := Finset.mem_Icc.mp (hB j₀ hb₀)
  have hb₁' := Finset.mem_Icc.mp (hB j₁ hb₁)
  have hb₂' := Finset.mem_Icc.mp (hB j₂ hb₂)
  have hj₀₁ : j₀ ≤ j₁ := by
    by_contra hlt
    push Not at hlt
    have hpow : 4 * 4 ^ j₁ ≤ 4 ^ j₀ := by
      have : 4 ^ (j₁ + 1) ≤ 4 ^ j₀ := Nat.pow_le_pow_right (by norm_num) hlt
      simpa [pow_succ'] using this
    omega
  have hj₁₂ : j₁ ≤ j₂ := by
    by_contra hlt
    push Not at hlt
    have hpow : 4 * 4 ^ j₂ ≤ 4 ^ j₁ := by
      have : 4 ^ (j₂ + 1) ≤ 4 ^ j₁ := Nat.pow_le_pow_right (by norm_num) hlt
      simpa [pow_succ'] using this
    omega
  have hj₁₂_eq : j₁ = j₂ := by
    by_contra hne
    have hlt : j₁ < j₂ := lt_of_le_of_ne hj₁₂ hne
    have hpow : 4 * 4 ^ j₁ ≤ 4 ^ j₂ := by
      have : 4 ^ (j₁ + 1) ≤ 4 ^ j₂ := Nat.pow_le_pow_right (by norm_num) hlt
      simpa [pow_succ'] using this
    omega
  have hj₀₁_eq : j₀ = j₁ := by
    by_contra hne
    have hlt : j₀ < j₁ := lt_of_le_of_ne hj₀₁ hne
    have hpow : 4 * 4 ^ j₀ ≤ 4 ^ j₁ := by
      have : 4 ^ (j₀ + 1) ≤ 4 ^ j₁ := Nat.pow_le_pow_right (by norm_num) hlt
      simpa [pow_succ'] using this
    subst hj₁₂_eq
    omega
  exact ⟨hj₀₁_eq, hj₁₂_eq⟩

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k hk B hB hfree ⟨a, d, hd, hap⟩
  choose j b hb heq using hap
  have hall_eq : ∀ i (hi : i < k), j i hi = j 0 (by omega) := by
    intro i hi
    induction i with
    | zero => rfl
    | succ m ih =>
      by_cases hm : m = 0
      · subst hm
        have hstep := block_index_eq_of_three_ap hB
          (hb 0 (by omega)) (hb 1 hi) (hb 2 (by omega))
          (heq 0 (by omega)) (heq 1 hi) (heq 2 (by omega))
          (by omega) (by ring)
        exact hstep.1.symm
      · have hstep := block_index_eq_of_three_ap hB
          (hb (m - 1) (by omega)) (hb m (by omega)) (hb (m + 1) hi)
          (heq (m - 1) (by omega)) (heq m (by omega)) (heq (m + 1) hi)
          (by have : (m - 1) * d < m * d := Nat.mul_lt_mul_of_pos_right (by omega) hd; omega) (by
            have hm1 : m - 1 + 1 = m := by omega
            have hm2 : (m - 1) * d + (m + 1) * d = 2 * (m * d) := by
              have : (m - 1) + (m + 1) = 2 * m := by omega
              calc (m - 1) * d + (m + 1) * d = ((m - 1) + (m + 1)) * d := (add_mul _ _ _).symm
                _ = (2 * m) * d := by rw [this]
                _ = 2 * (m * d) := by ring
            linarith)
        rw [← hstep.2, ih (by omega)]
  let J := j 0 (by omega)
  apply hfree J
  refine ⟨b 0 (by omega), d, hd, fun i hi ↦ ?_⟩
  have hj_eq : j i hi = J := hall_eq i hi
  have h0 := heq 0 (by omega)
  have hi_eq := heq i hi
  rw [hj_eq] at hi_eq
  have hb_eq : b 0 (by omega) + i * d = b i hi := by
    have h0' : a = 4 * 4 ^ J + b 0 (by omega) := by simpa [J] using h0
    omega
  rw [hb_eq]
  simpa [hj_eq] using hb i hi
