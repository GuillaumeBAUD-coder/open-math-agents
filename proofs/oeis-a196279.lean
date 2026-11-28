import OMAStatements.S_oeis_a196279

/-!
# A196279: Mathar's order-11 recurrence and its generating function

`a n = ((7n / 10) - 2 * (7n % 10)) / 7`, where `7n / 10` and `7n % 10` are the leading
part and the last digit of `7n`.

Recurrence: `n` enters only through `7n div 10` and `7n mod 10`; adding `10` to `n` adds
`70` to `7n`, raising the leading part by exactly `7` and leaving the digit alone, so
`a (n + 10) = a n + 1`.  Both `a n` and `a (n-1)` are then one more than their
counterparts ten steps back, giving `a n = a (n-1) + a (n-10) - a (n-11)`.

Generating function: the denominator factors as `(X-1)*(X^10-1)`, so multiplying by it
takes the coefficient `a n - a (n-1) - a (n-10) + a (n-11)` at `n`.  That vanishes for
`n >= 11` by the recurrence, and the ten remaining coefficients are finite computations.
-/

namespace OMA

open OMA.S_oeis_a196279
open PowerSeries

/-- Adding ten to the index raises the leading part of `7n` by exactly seven. -/
private lemma div_part (m : ℕ) : 7 * (m + 10) / 10 = 7 * m / 10 + 7 := by
  have h : 7 * (m + 10) = 7 * m + 7 * 10 := by ring
  rw [h, Nat.add_mul_div_right _ _ (by norm_num)]

/-- Adding ten to the index leaves the last digit of `7n` alone. -/
private lemma mod_part (m : ℕ) : 7 * (m + 10) % 10 = 7 * m % 10 := by
  have h : 7 * (m + 10) = 7 * m + 7 * 10 := by ring
  rw [h, Nat.add_mul_mod_self_right]

/-- Raising the numerator by `7` raises the quotient by `1`. -/
private lemma ediv_seven (X R : ℤ) : (X + 7 - 2 * R) / 7 = (X - 2 * R) / 7 + 1 := by
  have h : X + 7 - 2 * R = (X - 2 * R) + 1 * 7 := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by norm_num : (7 : ℤ) ≠ 0)]

/-- Ten steps on, the sequence gains exactly one. -/
private lemma a_add_ten (m : ℕ) : a (m + 10) = a m + 1 := by
  unfold a
  rw [div_part, mod_part, Nat.cast_add]
  simpa using ediv_seven ((7 * m / 10 : ℕ) : ℤ) ((7 * m % 10 : ℕ) : ℤ)

/-- The recurrence of the statement. -/
theorem key : ∀ n : ℕ, 11 ≤ n → a n = a (n - 1) + a (n - 10) - a (n - 11) := by
  intro n hn
  have hn10 : 10 ≤ n := by omega
  have h1 : a n = a (n - 10) + 1 := by
    have h := a_add_ten (n - 10)
    rwa [Nat.sub_add_cancel hn10] at h
  have h2 : a (n - 1) = a (n - 11) + 1 := by
    have h10 : 10 ≤ n - 1 := by omega
    have h := a_add_ten (n - 1 - 10)
    rw [Nat.sub_add_cancel h10, Nat.sub_sub] at h
    exact h
  linarith

/-- The denominator of the claimed generating function is `(1-X)*(1-X^10)`. -/
theorem denom_eq :
    ((1 + X) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) *
        (X - 1) ^ 2 : PowerSeries ℤ) = 1 - X - X ^ 10 + X ^ 11 := by
  ring

/-- The claimed numerator, expanded into monomials (using `X + X` for coefficient two). -/
theorem numer_eq :
    (X * (-2 + X - 2 * X ^ 3 + X ^ 4 - 2 * X ^ 6 + X ^ 7 + X ^ 9 + X ^ 2 + X ^ 5 + X ^ 8) :
        PowerSeries ℤ)
      = -(X + X) + X ^ 2 + X ^ 3 - (X ^ 4 + X ^ 4) + X ^ 5 + X ^ 6 - (X ^ 7 + X ^ 7) +
        X ^ 8 + X ^ 9 + X ^ 10 := by
  ring

/-- `a 0 = 0`, which makes the truncated index shifts below harmless. -/
private lemma a_zero : a 0 = 0 := by
  unfold a
  norm_num

/-- Coefficient of the product with the denominator. -/
theorem coeff_prod (n : ℕ) :
    coeff n (mk a * (1 - X - X ^ 10 + X ^ 11 : PowerSeries ℤ))
      = a n - a (n - 1) - a (n - 10) + a (n - 11) := by
  have hexp : mk a * (1 - X - X ^ 10 + X ^ 11 : PowerSeries ℤ)
      = mk a - mk a * X ^ 1 - mk a * X ^ 10 + mk a * X ^ 11 := by ring
  rw [hexp]
  simp only [map_sub, map_add, coeff_mk, coeff_mul_X_pow']
  have e1 : (if 1 ≤ n then a (n - 1) else 0) = a (n - 1) := by
    split_ifs with h
    · rfl
    · have hn : n = 0 := by omega
      subst hn
      simp [a_zero]
  have e10 : (if 10 ≤ n then a (n - 10) else 0) = a (n - 10) := by
    split_ifs with h
    · rfl
    · have hn : n - 10 = 0 := by omega
      rw [hn, a_zero]
  have e11 : (if 11 ≤ n then a (n - 11) else 0) = a (n - 11) := by
    split_ifs with h
    · rfl
    · have hn : n - 11 = 0 := by omega
      rw [hn, a_zero]
  rw [e1, e10, e11]

end OMA

open OMA.S_oeis_a196279 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a196279.main := by
  constructor
  · exact OMA.key
  · rw [OMA.denom_eq, OMA.numer_eq]
    refine PowerSeries.ext fun n => ?_
    rw [OMA.coeff_prod n]
    rcases lt_or_ge n 11 with hlt | hge
    · interval_cases n <;>
        simp [coeff_X, coeff_X_pow, a] <;> norm_num
    · have hl : a n - a (n - 1) - a (n - 10) + a (n - 11) = 0 := by
        rw [OMA.key n hge]; ring
      rw [hl]
      simp [coeff_X, coeff_X_pow, show n ≠ 1 by omega, show n ≠ 2 by omega,
        show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
        show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega,
        show n ≠ 9 by omega, show n ≠ 10 by omega]
