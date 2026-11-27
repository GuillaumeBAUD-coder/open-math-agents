import Mathlib

/-!
# The largest-proper-divisor formula for OEIS A242992

Sources: https://oeis.org/A242992 and https://oeis.org/A032742
Credit: @Heart-galaxy

Ridouane Oudra's conjecture was proved by Sela Fried in 2026. See
https://arxiv.org/pdf/2607.24832, Theorem 29.

The natural-number inequality `n / 2 < k` expresses the source's strict bound
on the integer `k`, since integer division rounds `n / 2` down.
-/

namespace OMA.S_oeis_a242992

/-- The least admissible index, with the default zero for an empty set. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | n / 2 < k ∧ k < n ∧ (2 ^ (n - k) - 1) ∣ (2 ^ k - 2)}

/-- OEIS A032742, the largest proper divisor for indices greater than one. -/
def b (n : ℕ) : ℕ := if n = 1 then 1 else n.properDivisors.sup id

/-- Oudra's formula for the terms of A242992 above index two. -/
theorem main : ∀ n : ℕ, 2 < n → a n = n - b (n - 1) := by
  sorry

end OMA.S_oeis_a242992
