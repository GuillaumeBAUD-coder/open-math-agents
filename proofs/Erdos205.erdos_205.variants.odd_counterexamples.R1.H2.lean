import OMAReductions.R_Erdos205_erdos_205_variants_odd_counterexamples_R1
import Mathlib

/-!
Step H2 of reduction Erdos205.erdos_205.variants.odd_counterexamples.R1:
`Ω` (prime factors counted with multiplicity) is monotone along divisibility of nonzero numbers.
If `a ∣ b` with `b ≠ 0`, write `b = a * c` with `a, c ≠ 0`; then `Ω b = Ω a + Ω c ≥ Ω a`.
-/

theorem OMA.solution : OMA.R_Erdos205_erdos_205_variants_odd_counterexamples_R1.H2 := by
  unfold OMA.R_Erdos205_erdos_205_variants_odd_counterexamples_R1.H2
  intro a b hb hab
  obtain ⟨c, rfl⟩ := hab
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hb
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hb
  rw [ArithmeticFunction.cardFactors_mul ha hc]
  exact Nat.le_add_right _ _
