import OMAReductions.R_Erdos205_erdos_205_variants_odd_counterexamples_R1

-- Step Erdos205.erdos_205.variants.odd_counterexamples.R1.H2: hypothesis H2 of reduction Erdos205.erdos_205.variants.odd_counterexamples.R1
-- Credit: @its-shitzu
-- H2 := ∀ a b : ℕ, b ≠ 0 → a ∣ b → Ω a ≤ Ω b

theorem OMA.solution : OMA.R_Erdos205_erdos_205_variants_odd_counterexamples_R1.H2 := by
  intro a b hb hab
  have ha : a ≠ 0 := by
    rintro rfl
    exact hb (zero_dvd_iff.mp hab)
  have hle : a.factorization ≤ b.factorization :=
    (Nat.factorization_le_iff_dvd ha hb).mpr hab
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization,
    ArithmeticFunction.cardFactors_eq_sum_factorization]
  exact Finsupp.sum_le_sum_index hle
    (fun _ _ => monotone_id) (fun _ _ => rfl)
