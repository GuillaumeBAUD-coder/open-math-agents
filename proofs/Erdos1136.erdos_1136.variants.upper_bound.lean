import FormalConjectures.ErdosProblems.«1136»

/-! Pair each selected integer with its unselected complement to a power of two. -/

open Filter

theorem OMA.solution : type_of% @Erdos1136.erdos_1136.variants.upper_bound := by
  classical
  intro A hA
  have hpartial (k : ℕ) : A.partialDensity Set.univ (2 ^ k + 1) ≤ 1 / 2 := by
    let U := Finset.range (2 ^ k + 1)
    let S := U.filter (· ∈ A)
    have hsub : S ⊆ U := Finset.filter_subset _ _
    have hpair : S.card ≤ (U \ S).card := by
      apply Finset.card_le_card_of_injOn (fun a => 2 ^ k - a)
      · intro a ha
        have haS : a ∈ S := ha
        obtain ⟨haU, haA⟩ := Finset.mem_filter.mp haS
        have hle : a ≤ 2 ^ k := Nat.le_of_lt_succ (Finset.mem_range.mp haU)
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _)), ?_⟩
        intro hb
        have hbA : 2 ^ k - a ∈ A := (Finset.mem_filter.mp hb).2
        exact hA a haA _ hbA k (by omega)
      · intro a ha b hb heq
        have haS : a ∈ S := ha
        have hbS : b ∈ S := hb
        have haU : a < 2 ^ k + 1 := Finset.mem_range.mp (hsub haS)
        have hbU : b < 2 ^ k + 1 := Finset.mem_range.mp (hsub hbS)
        change 2 ^ k - a = 2 ^ k - b at heq
        omega
    have hsize : 2 * S.card ≤ 2 ^ k + 1 := by
      rw [Finset.card_sdiff_of_subset hsub, show U.card = 2 ^ k + 1 by simp [U]] at hpair
      have hpow : (0 : ℕ) < 2 ^ k := by positivity
      omega
    have hcoe : (S : Set ℕ) = A ∩ Set.Iio (2 ^ k + 1) := by
      ext a
      simp [S, U, and_comm]
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, ← hcoe,
      Set.ncard_coe_finset, Set.ncard_Iio_nat]
    have hn : 0 < ((2 ^ k + 1 : ℕ) : ℝ) := by positivity
    have hsize' : 2 * (S.card : ℝ) ≤ ((2 ^ k + 1 : ℕ) : ℝ) := by
      exact_mod_cast hsize
    apply (div_le_iff₀ hn).mpr
    linarith
  rw [Set.lowerDensity, Filter.liminf_eq]
  apply Real.sSup_le _ (by norm_num)
  intro d hd
  have hd' : ∀ᶠ n in atTop, d ≤ A.partialDensity Set.univ n := hd
  obtain ⟨b, hb⟩ := eventually_atTop.1 hd'
  have hindex : b ≤ 2 ^ b + 1 := b.lt_two_pow_self.le.trans (Nat.le_succ _)
  exact (hb _ hindex).trans (hpartial b)