import OMAReductions.R_oeis_a006093_R2

/-!
# Reduction of the positive-shift case of Sun's shifted-prime reciprocal sums

The positive-shift step `oeis-a006093.R2.H2` has two logically different parts.
Away from the unit shift and linear exponent there should be no collision at all;
in the exceptional unit case one must still classify the colliding index intervals.
Those two parts are likely to use different arguments: size and congruence
obstructions in the first, and a sharper analysis of consecutive shifted primes
in the second.
-/

namespace OMA.R_oeis_a006093_R2_H2_R1

open OMA.S_oeis_a006093

/-- Outside the unit shift and linear exponent, separated intervals have unequal sums. -/
def H1 : Prop :=
  ∀ (d : ℤ) (m i j s t : ℕ), 0 < d → 0 < m → 0 < i → i ≤ j → j < s → s ≤ t →
    (d ≠ 1 ∨ m ≠ 1) → intervalSum d m i j = intervalSum d m s t → False

/-- The unit-shift linear case has only the exceptional collision. -/
def H2 : Prop :=
  ∀ i j s t : ℕ, 0 < i → i ≤ j → j < s → s ≤ t →
    intervalSum 1 1 i j = intervalSum 1 1 s t →
    i = 4 ∧ j = 4 ∧ s = 8 ∧ t = 10

theorem main : H1 → H2 → OMA.R_oeis_a006093_R2.H2 := by
  intro h1 h2 d m i j s t hd hm hi hij hjs hst he
  by_cases hd1 : d = 1
  · by_cases hm1 : m = 1
    · subst d
      subst m
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h2 i j s t hi hij hjs hst he
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact False.elim (h1 d m i j s t hd hm hi hij hjs hst (Or.inr hm1) he)
  · exact False.elim (h1 d m i j s t hd hm hi hij hjs hst (Or.inl hd1) he)

end OMA.R_oeis_a006093_R2_H2_R1
