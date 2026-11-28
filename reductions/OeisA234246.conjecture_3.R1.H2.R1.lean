import OMAReductions.R_OeisA234246_conjecture_3_R1
import Mathlib.Tactic

/-!
# Reduction of the quantitative binary Goldbach step in A234246

Any prime `p ≤ 128` for which `e - p` is also prime immediately supplies the
required decomposition.  This file discharges that small-prime case directly.
The residual case, in which no such small prime witness exists, is split according
to divisibility of `e` by `3`; the case `3 ∣ e` is distinctive because the most
obvious candidate `e - 3` is then composite.
-/

namespace OMA.R_OeisA234246_conjecture_3_R1_H2_R1

/-- The residual case with no small-prime witness and `3 ∣ e`. -/
def H1 : Prop :=
  ∀ e : ℕ, 8 ≤ e → Even e → ¬ (∃ p : ℕ, p.Prime ∧ p ≤ 128 ∧ p < e ∧ (e - p).Prime ∧ p ≠ e - p) → 3 ∣ e →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = e ∧ (p ≤ 128 ∨ 16 * p < e)

/-- The residual case with no small-prime witness and `3 ∤ e`. -/
def H2 : Prop :=
  ∀ e : ℕ, 8 ≤ e → Even e → ¬ (∃ p : ℕ, p.Prime ∧ p ≤ 128 ∧ p < e ∧ (e - p).Prime ∧ p ≠ e - p) → ¬ 3 ∣ e →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = e ∧ (p ≤ 128 ∨ 16 * p < e)

theorem main : H1 → H2 → OMA.R_OeisA234246_conjecture_3_R1.H2 := by
  intro h1 h2 e he heven
  by_cases hs : ∃ p : ℕ, p.Prime ∧ p ≤ 128 ∧ p < e ∧ (e - p).Prime ∧ p ≠ e - p
  · obtain ⟨p, hp, hp128, hplt, hq, hpq⟩ := hs
    exact ⟨p, e - p, hp, hq, hpq, by omega, Or.inl hp128⟩
  · by_cases h3 : 3 ∣ e
    · exact h1 e he heven hs h3
    · exact h2 e he heven hs h3

end OMA.R_OeisA234246_conjecture_3_R1_H2_R1
