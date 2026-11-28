import OMAStatements.S_oeis_a329725
import Mathlib

/-!
# OEIS A329725: `a(10n + 1) - a(10n - 1) = 1`

Using the defining rule twice,

  `a(10n+1) = (10n+1) - p(10n+1) - a(10n)`,   `a(10n) = 10n - p(10n) - a(10n-1)`,

so `a(10n+1) - a(10n-1) = 1 - p(10n+1) + p(10n)`. The decimal digits of `10n + 1` and `10n` are
those of `n` preceded by a last digit `1`, respectively `0`, so the products of their nonzero
digits agree: `p(10n+1) = p(10n)`.
-/

open OMA.S_oeis_a329725

namespace OMA.A329725

/-- The defining rule. -/
lemma a_step (m : ℕ) : a (m + 2) = ((m + 2 : ℕ) : ℤ) - p (m + 2) - a (m + 1) := by
  rw [a]

/-- Appending a last digit `1` or `0` gives the same product of nonzero digits. -/
lemma p_eq (n : ℕ) (hn : 1 ≤ n) : p (10 * n + 1) = p (10 * n) := by
  unfold p
  rw [Nat.digits_def' (by norm_num : 1 < 10) (by omega : 0 < 10 * n + 1),
    Nat.digits_def' (by norm_num : 1 < 10) (by omega : 0 < 10 * n)]
  have h1 : (10 * n + 1) % 10 = 1 := by omega
  have h2 : (10 * n + 1) / 10 = n := by omega
  have h3 : (10 * n) % 10 = 0 := by omega
  have h4 : (10 * n) / 10 = n := by omega
  rw [h1, h2, h3, h4]
  simp

end OMA.A329725

open OMA.A329725 in
theorem OMA.solution : type_of% @OMA.S_oeis_a329725.main := by
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m, 10 * n = m + 2 := ⟨10 * n - 2, by omega⟩
  have hp := p_eq n hn
  rw [hm] at hp
  have e1 : 10 * n + 1 = m + 1 + 2 := by omega
  have e2 : 10 * n - 1 = m + 1 := by omega
  rw [e1, e2, a_step (m + 1), show m + 1 + 1 = m + 2 by omega, a_step m,
    show m + 1 + 2 = m + 2 + 1 by omega, hp]
  push_cast
  ring
