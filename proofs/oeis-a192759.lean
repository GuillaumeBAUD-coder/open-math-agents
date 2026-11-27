import OMAStatements.S_oeis_a192759
import Mathlib

/-!
Modulo q = x^2 - x - 1: if p(n) = v + u x (mod q) then p(n+1) = x p(n) + c(n+1) = (u + v) x + u + c(n+1),
with c(m) = floor((m+5)/5). So a = u satisfies a(n+2) = a(n+1) + a(n) + c(n+1), a(0) = 0, a(1) = 1,
and v(n) = A124502(n+1) (both satisfy the same order-2 recurrence, since c(n+2) - c(n+1) = [5 | n+2]),
giving the partial sums. For the g.f.: (1 - x - x^2) A = x C with C = Sum c(m) x^m, and
C (1 - x^5) = 1/(1 - x); the denominator is -(1 - x - x^2)(1 - x^5)(1 - x).
-/

namespace R192759
open OMA.S_oeis_a192759

def c (m : ℕ) : ℤ := (((m + 5) / 5 : ℕ) : ℤ)

def uv : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | n + 1 => ((uv n).1 + (uv n).2, (uv n).1 + c (n + 1))

section poly
open Polynomial

theorem hq : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!

theorem pdvd (n : ℕ) : (X ^ 2 - X - 1 : ℤ[X]) ∣ p n - (C (uv n).2 + C (uv n).1 * X) := by
  induction n with
  | zero => simp [p, uv]
  | succ n ih =>
    have e : p (n + 1) - (C (uv (n + 1)).2 + C (uv (n + 1)).1 * X) =
        X * (p n - (C (uv n).2 + C (uv n).1 * X)) + C (uv n).1 * (X ^ 2 - X - 1) := by
      simp only [p, uv, c, map_add]
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_left _ _)

theorem rem (n : ℕ) : p n %ₘ (X ^ 2 - X - 1) = C (uv n).2 + C (uv n).1 * X := by
  rw [modByMonic_eq_of_dvd_sub hq (pdvd n), (modByMonic_eq_self_iff hq).mpr]
  apply degree_lt_degree
  have h2 : (X ^ 2 - X - 1 : ℤ[X]).natDegree = 2 := by compute_degree!
  have h1 : (C (uv n).2 + C (uv n).1 * X).natDegree ≤ 1 := by compute_degree
  omega

theorem a_eq (n : ℕ) : a n = (uv n).1 := by
  rw [a, rem, coeff_add, coeff_C, coeff_C_mul_X]
  simp

end poly

theorem hc (n : ℕ) : c (n + 2) = c (n + 1) + if (n + 2) % 5 = 0 then 1 else 0 := by
  unfold c
  split_ifs with h
  · have e : (n + 2 + 5) / 5 = (n + 1 + 5) / 5 + 1 := by omega
    rw [e]
    push_cast
    ring
  · have e : (n + 2 + 5) / 5 = (n + 1 + 5) / 5 := by omega
    rw [e]
    ring

theorem hv (n : ℕ) : (uv n).2 = A124502 (n + 1) ∧ (uv (n + 1)).2 = A124502 (n + 2) := by
  induction n with
  | zero => exact ⟨rfl, by norm_num [uv, c, A124502]⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    show (uv (n + 2)).2 = A124502 (n + 3)
    have e1 : (uv (n + 2)).2 = (uv (n + 1)).2 + (uv n).2 + if (n + 2) % 5 = 0 then 1 else 0 := by
      simp only [uv, show n + 1 + 1 = n + 2 from rfl]
      rw [hc n]
      ring
    rw [e1, ih.1, ih.2]
    simp only [A124502]

theorem hu (n : ℕ) : (uv n).1 = ∑ k ∈ Finset.Icc 1 n, A124502 k := by
  induction n with
  | zero => simp [uv]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih, ← (hv n).1]
    rfl

section ps
open PowerSeries

theorem a_zero : a 0 = 0 := by rw [a_eq]; rfl

theorem a_one : a 1 = 1 := by rw [a_eq]; rfl

theorem a_rec (n : ℕ) : a (n + 2) = a (n + 1) + a n + c (n + 1) := by
  rw [a_eq, a_eq, a_eq]
  show (uv (n + 1)).1 + (uv (n + 1)).2 = _
  show (uv (n + 1)).1 + ((uv n).1 + c (n + 1)) = _
  ring

theorem hA : (mk a : PowerSeries ℤ) * (1 - X ^ 1 - X ^ 2) = X ^ 1 * mk c := by
  ext n
  simp only [mul_sub, mul_one, map_sub, coeff_mk, coeff_mul_X_pow', coeff_X_pow_mul']
  rcases n with _ | _ | n
  · simp [a_zero]
  · simp [a_zero, a_one, c]
  · have h1 : 1 ≤ n + 1 + 1 := by omega
    have h2 : 2 ≤ n + 1 + 1 := by omega
    simp only [h1, h2, ↓reduceIte, show n + 1 + 1 - 1 = n + 1 by omega,
      show n + 1 + 1 - 2 = n by omega]
    rw [show n + 1 + 1 = n + 2 from rfl, a_rec n]
    ring

theorem hB : (mk c : PowerSeries ℤ) * (1 - X ^ 5) = mk 1 := by
  ext n
  simp only [mul_sub, mul_one, map_sub, coeff_mk, coeff_mul_X_pow', Pi.one_apply]
  split_ifs with h
  · unfold c
    have e : (n + 5) / 5 = (n - 5 + 5) / 5 + 1 := by omega
    rw [e]
    push_cast
    ring
  · unfold c
    have e : (n + 5) / 5 = 1 := by omega
    rw [e]
    simp

theorem gf : (mk a : PowerSeries ℤ) * ((X ^ 2 + X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) *
    (X - 1) ^ 2) = -X := by
  calc (mk a : PowerSeries ℤ) * ((X ^ 2 + X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X - 1) ^ 2)
      = -((mk a * (1 - X ^ 1 - X ^ 2)) * ((1 - X ^ 5) * (1 - X))) := by ring
    _ = -((X ^ 1 * mk c) * ((1 - X ^ 5) * (1 - X))) := by rw [hA]
    _ = -(X ^ 1 * ((mk c * (1 - X ^ 5)) * (1 - X))) := by ring
    _ = -X := by rw [hB, mk_one_mul_one_sub_eq_one]; ring

end ps

theorem solve :
    (PowerSeries.mk a *
        ((PowerSeries.X ^ 2 + PowerSeries.X - 1) *
          (PowerSeries.X ^ 4 + PowerSeries.X ^ 3 + PowerSeries.X ^ 2 + PowerSeries.X + 1) *
          (PowerSeries.X - 1) ^ 2) = -PowerSeries.X) ∧
    ∀ n : ℕ, a n = ∑ k ∈ Finset.Icc 1 n, A124502 k :=
  ⟨gf, fun n => by rw [a_eq, hu]⟩

end R192759

theorem OMA.solution : type_of% @OMA.S_oeis_a192759.main := R192759.solve
