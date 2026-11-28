import OMAReductions.R_Green24_variants_conjecture_R1

open Filter

namespace G24H2

lemma count (m N : ℕ) (hN : 3 * m ≤ N) : 3 * (m * m - m) ≤
    ((Finset.Ico (0:ℤ) N ×ˢ Finset.Ico (0:ℤ) N).filter
    (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ Finset.Ico (0:ℤ) N)).card := by
  let f : ℕ × ℕ × ℕ → ℤ × ℤ := fun t => (3 * t.2.1 + t.1, 2 * t.2.1 + t.2.2 + t.1)
  have hcard : ((Finset.range 3) ×ˢ (Finset.range m).offDiag).card = 3 * (m * m - m) := by
    rw [Finset.card_product, Finset.offDiag_card]; simp
  rw [← hcard]
  apply Finset.card_le_card_of_injOn f
  · intro t ht
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range,
      Finset.mem_offDiag] at ht
    obtain ⟨h1, h2, h3, h4⟩ := ht
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_Ico, Set.mem_ofPred_eq, f]
    omega
  · intro a ha b hb hab
    obtain ⟨a1, a2, a3⟩ := a
    obtain ⟨b1, b2, b3⟩ := b
    simp only [f, Prod.mk.injEq] at hab
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at ha hb
    simp only [Prod.mk.injEq]
    omega

lemma lower (m : ℕ) : 3 * (m * m - m) ≤ Green24.max013AffineTranslates (3 * m) := by
  refine le_trans (count m (3 * m) le_rfl) ?_
  apply le_csSup
  · refine ⟨(3 * m) ^ 2, ?_⟩
    rintro k ⟨A, hA, rfl⟩
    apply le_trans (Finset.card_filter_le _ _)
    rw [Finset.card_product, hA, pow_two]
  · refine ⟨Finset.Ico (0:ℤ) ((3 * m : ℕ) : ℤ), ?_, rfl⟩
    rw [Int.card_Ico]; omega

theorem result : (1 : ℝ) / 3 ≤ Green24.variants.gamma := by
  have hb : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (Green24.max013AffineTranslates n : ℝ) / ((n : ℝ)^2)) := by
    refine isBoundedUnder_of ⟨1, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · apply div_le_one_of_le₀ _ (by positivity)
      exact_mod_cast (Green24.variants.upper_trivial (n := n))
  apply le_of_forall_pos_le_add
  intro ε hε
  have key : (1 : ℝ) / 3 - ε ≤ Green24.variants.gamma := by
    apply le_limsup_of_frequently_le _ hb
    rw [frequently_atTop]
    intro a
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    refine ⟨3 * (a + k + 1), by omega, ?_⟩
    set m := a + k + 1 with hm
    have hm1 : (1 : ℝ) ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a), (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hmk : (k : ℝ) + 1 ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)]
    have hmε : 1 ≤ m * ε := by
      have := (div_lt_iff₀ hε).1 hk
      nlinarith
    have hl := lower m
    have hle : m ≤ m * m := Nat.le_mul_self m
    have hc : ((3 * (m * m - m) : ℕ) : ℝ) = 3 * ((m:ℝ) * m - m) := by
      rw [Nat.cast_mul, Nat.cast_sub hle]; push_cast; ring
    have hl' : 3 * ((m:ℝ) * m - m) ≤ (Green24.max013AffineTranslates (3 * m) : ℝ) := by
      rw [← hc]; exact_mod_cast hl
    rw [le_div_iff₀ (by positivity)]
    push_cast
    nlinarith
  linarith

end G24H2

theorem OMA.solution : OMA.R_Green24_variants_conjecture_R1.H2 := G24H2.result
