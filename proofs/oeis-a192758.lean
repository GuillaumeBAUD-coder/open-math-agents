import OMAStatements.S_oeis_a192758
import Mathlib

-- Problem: A192758, the g.f. -x^2/((1+x)(x^2+1)(x^2+x-1)(x-1)^2) for the coefficient of x in the
-- reduction of p(n,x) by x^2 -> x + 1.
-- Upstream: formal-conjectures statements/oeis-a192758.lean (declaration OMA.S_oeis_a192758.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated g.f. holds).
-- Proof: the remainder u(m) + v(m) x of p(m) modulo x^2 - x - 1 satisfies
-- v(m+2) = v(m+1) + v(m) + floor((m+5)/4); the floor term is annihilated by (1-x)(1-x^4).

namespace OMA.P_oeis_a192758

open OMA.S_oeis_a192758 Polynomial

/-- The remainder of p(m) modulo x^2 - x - 1, as the pair (constant term, coefficient of x). -/
def uv : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | m + 1 => ((uv m).2 + ((((m + 1 + 4) / 4 : ℕ) : ℤ)), (uv m).1 + (uv m).2)

theorem rem (m : ℕ) :
    ∃ h : ℤ[X], p m = C (uv m).2 * X + C (uv m).1 + (X ^ 2 - X - 1) * h := by
  induction m with
  | zero =>
    refine ⟨0, ?_⟩
    simp [p, uv]
  | succ m ih =>
    obtain ⟨h, e⟩ := ih
    refine ⟨X * h + C (uv m).2, ?_⟩
    have hp : p (m + 1) = X * p m + C ((((m + 1 + 4) / 4 : ℕ) : ℤ)) := rfl
    have hu : uv (m + 1) = ((uv m).2 + ((((m + 1 + 4) / 4 : ℕ) : ℤ)), (uv m).1 + (uv m).2) := rfl
    rw [hu]
    simp only [map_add]
    linear_combination hp + X * e

theorem monic_g : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + 1) := by ring
  rw [this]
  apply monic_X_pow_sub
  compute_degree!

theorem deg_g : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by
  compute_degree!

theorem b_eq (m : ℕ) : b m = (uv m).2 := by
  obtain ⟨h, e⟩ := rem m
  have hm := (div_modByMonic_unique (f := p m) h (C (uv m).2 * X + C (uv m).1) monic_g
    ⟨e.symm, by rw [deg_g]; exact degree_linear_lt⟩).2
  simp only [b, hm, coeff_add, coeff_C_mul_X, coeff_C]
  simp

theorem v_rec (m : ℕ) :
    (uv (m + 2)).2 = (uv (m + 1)).2 + (uv m).2 + ((((m + 1 + 4) / 4 : ℕ) : ℤ)) := by
  have e1 : (uv (m + 2)).2 = (uv (m + 1)).1 + (uv (m + 1)).2 := rfl
  have e2 : (uv (m + 1)).1 = (uv m).2 + ((((m + 1 + 4) / 4 : ℕ) : ℤ)) := rfl
  linear_combination e1 + e2

theorem key (f : PowerSeries ℤ) :
    (PowerSeries.X * f)
        * ((1 + PowerSeries.X) * (PowerSeries.X ^ 2 + 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1)
          * (PowerSeries.X - 1) ^ 2) =
      PowerSeries.C (-1 : ℤ) * (PowerSeries.X ^ 1 * f) + PowerSeries.C (2 : ℤ) * (PowerSeries.X ^ 2 * f)
        + PowerSeries.C (-1 : ℤ) * (PowerSeries.X ^ 4 * f) + PowerSeries.C (1 : ℤ) * (PowerSeries.X ^ 5 * f)
        + PowerSeries.C (-2 : ℤ) * (PowerSeries.X ^ 6 * f) + PowerSeries.C (1 : ℤ) * (PowerSeries.X ^ 8 * f) := by
  simp only [map_one, map_neg, map_ofNat]
  ring

theorem rhs : -(PowerSeries.X : PowerSeries ℤ) ^ 2 = PowerSeries.C (-1 : ℤ) * PowerSeries.X ^ 2 := by
  simp only [map_neg, map_one]
  ring

theorem main' :
    (PowerSeries.X * PowerSeries.mk b)
        * ((1 + PowerSeries.X) * (PowerSeries.X ^ 2 + 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1)
          * (PowerSeries.X - 1) ^ 2)
      = -(PowerSeries.X : PowerSeries ℤ) ^ 2 := by
  rw [key, rhs]
  ext n
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow, b_eq]
  rcases lt_or_ge n 8 with h | h
  · interval_cases n <;> simp [uv]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [show 1 ≤ m + 8 by omega, show 2 ≤ m + 8 by omega, show 4 ≤ m + 8 by omega,
      show 5 ≤ m + 8 by omega, show 6 ≤ m + 8 by omega, show 8 ≤ m + 8 by omega,
      show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
      show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega,
      show m + 8 - 6 = m + 2 by omega, show m + 8 - 8 = m by omega, show m + 8 ≠ 2 by omega,
      if_true, if_false]
    have e0 : (uv (m + 2)).2 = (uv (m + 1)).2 + (uv m).2 + ((((m + 1 + 4) / 4 : ℕ) : ℤ)) := v_rec m
    have e1 : (uv (m + 3)).2 = (uv (m + 2)).2 + (uv (m + 1)).2
        + ((((m + 2 + 4) / 4 : ℕ) : ℤ)) := v_rec (m + 1)
    have e4 : (uv (m + 6)).2 = (uv (m + 5)).2 + (uv (m + 4)).2
        + ((((m + 5 + 4) / 4 : ℕ) : ℤ)) := v_rec (m + 4)
    have e5 : (uv (m + 7)).2 = (uv (m + 6)).2 + (uv (m + 5)).2
        + ((((m + 6 + 4) / 4 : ℕ) : ℤ)) := v_rec (m + 5)
    have hc : ((((m + 6 + 4) / 4 : ℕ) : ℤ)) - ((((m + 5 + 4) / 4 : ℕ) : ℤ))
        - ((((m + 2 + 4) / 4 : ℕ) : ℤ)) + ((((m + 1 + 4) / 4 : ℕ) : ℤ)) = 0 := by
      omega
    linear_combination -e5 + e4 + e1 - e0 - hc

end OMA.P_oeis_a192758

theorem OMA.solution : type_of% @OMA.S_oeis_a192758.main := OMA.P_oeis_a192758.main'
