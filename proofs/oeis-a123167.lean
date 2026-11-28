import OMAStatements.S_oeis_a123167
import Mathlib

/-!
# OEIS A123167: the reduced numerator of `4/n - 2/n² = (4n - 2)/n²`

* `n = 2j + 1` odd: `(4n - 2)/n² = (8j + 2)/(2j + 1)²`, and `j (8j + 2) + (1 - 4j)(2j + 1) = 1`
  shows the fraction is reduced, so the numerator is `8j + 2 = 8 (n+1)/2 - 6`.
* `n = 2j` even: `(4n - 2)/n² = (4j - 1)/(2j²)`; `4j - 1` is coprime to `2` and to `j`, so the
  fraction is reduced and the numerator is `4j - 1 = 4 (n/2) - 1`.
-/

open OMA.S_oeis_a123167

namespace OMA.A123167

/-- A coprime pair of integers gives a reduced fraction. -/
lemma num_of_isCoprime {p q : ℤ} (hq : 0 < q) (h : IsCoprime p q) : ((p : ℚ) / (q : ℚ)).num = p :=
  Rat.num_div_eq_of_coprime hq (Int.isCoprime_iff_gcd_eq_one.mp h)

end OMA.A123167

open OMA.A123167 in
theorem OMA.solution : type_of% @OMA.S_oeis_a123167.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · -- `n = 2j`
    have hj : 1 ≤ j := by omega
    have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    have e : (4 / ((j + j : ℕ) : ℚ) - 2 / ((j + j : ℕ) : ℚ) ^ 2 : ℚ)
        = ((4 * (j : ℤ) - 1 : ℤ) : ℚ) / ((2 * (j : ℤ) ^ 2 : ℤ) : ℚ) := by
      push_cast
      field_simp
      ring
    have hcop : IsCoprime (4 * (j : ℤ) - 1) (2 * (j : ℤ) ^ 2) := by
      have h2 : IsCoprime (4 * (j : ℤ) - 1) 2 := ⟨-1, 2 * j, by ring⟩
      have hj' : IsCoprime (4 * (j : ℤ) - 1) (j : ℤ) := ⟨-1, 4, by ring⟩
      exact h2.mul_right (hj'.pow_right)
    rw [e, num_of_isCoprime (by positivity) hcop]
    unfold a
    rw [if_neg (by omega), show (j + j) / 2 = j by omega]
    push_cast [Nat.cast_sub (by omega : 1 ≤ 4 * j)]
    ring
  · -- `n = 2j + 1`
    have e : (4 / ((2 * j + 1 : ℕ) : ℚ) - 2 / ((2 * j + 1 : ℕ) : ℚ) ^ 2 : ℚ)
        = ((8 * (j : ℤ) + 2 : ℤ) : ℚ) / (((2 * (j : ℤ) + 1) ^ 2 : ℤ) : ℚ) := by
      have hQ : (2 * (j : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    have hcop : IsCoprime (8 * (j : ℤ) + 2) ((2 * (j : ℤ) + 1) ^ 2) := by
      have h1 : IsCoprime (8 * (j : ℤ) + 2) (2 * (j : ℤ) + 1) := ⟨j, 1 - 4 * j, by ring⟩
      exact h1.pow_right
    rw [e, num_of_isCoprime (by positivity) hcop]
    unfold a
    rw [if_pos (by omega), show (2 * j + 1 + 1) / 2 = j + 1 by omega]
    push_cast [Nat.cast_sub (by omega : 6 ≤ 8 * (j + 1))]
    ring
