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
        obtain ⟨haU, haA⟩ := Finset.mem_filter.mp ha
        have haU' := Finset.mem_range.mp haU
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _)),
            fun hb => hA a haA _ (Finset.mem_filter.mp hb).2 k (by
              change a + (2 ^ k - a) = 2 ^ k
              omega)⟩
      · intro a ha b hb heq
        have := Finset.mem_range.mp (hsub ha)
        have := Finset.mem_range.mp (hsub hb)
        change 2 ^ k - a = 2 ^ k - b at heq
        omega
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_range] at hpair
    have hcoe : (S : Set ℕ) = A ∩ Set.Iio (2 ^ k + 1) := by
      ext a
      simp [S, U, and_comm]
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, ← hcoe,
      Set.ncard_coe_finset, Set.ncard_Iio_nat]
    apply (div_le_iff₀ (by positivity)).mpr
    have hsize : (2 : ℝ) * S.card ≤ ((2 ^ k + 1 : ℕ) : ℝ) := by
      have hpow : (0 : ℕ) < 2 ^ k := by positivity
      exact_mod_cast (show 2 * S.card ≤ 2 ^ k + 1 by omega)
    linarith
  rw [Set.lowerDensity, Filter.liminf_eq]
  apply Real.sSup_le _ (by norm_num)
  intro d hd
  obtain ⟨b, hb⟩ := eventually_atTop.mp hd
  exact (hb _ (b.lt_two_pow_self.le.trans (Nat.le_succ _))).trans (hpartial b)
