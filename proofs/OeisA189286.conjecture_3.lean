import FormalConjectures.OEIS.«189286»

/-!
Proof of `OeisA189286.conjecture_3`:
For every `n > 0`, `a n = (∑ k ∈ range (n + 1), T k * T (n - k)) / ((2n - 1) * C(3n, n))`
is an integer divisible by 8, and `a n / 8` is odd iff `n` is a power of 2.

Proof outline:
1. Using the Euler operator `θ = X d/dX` on `PowerSeries ℤ` and the 2nd-order ODE for
   `y(X) = ∑ T_k X^k`, deduce the 3rd-order ODE for `Y = y^2`, giving the 3-term linear
   recurrence for `S n = ∑_{k=0}^n T_k T_{n-k}`.
2. By an explicit Zeilberger telescoping certificate `G(n, m) = -(n + 1) m^2 F(n + 1, m)`,
   prove that `R n = ∑_{m=0}^n T_m C(2m, m) C(m, n - m) (-432)^{n - m}` satisfies the exact
   same recurrence and initial values, hence `S n = R n` for all `n`.
3. By Legendre's formula and an elementary floor inequality, prove that `(2n - 1) * C(3n, n)`
   divides every term `F n m` individually, establishing that `a n` is an integer.
4. Using `padicValNat 2 (k!) = k - s_2(k)`, show `v_2(F n n) = 3 s_2(n)` while every `m < n`
   term has `v_2(F n m) ≥ 3 s_2(n) + 1`, so `v_2(S n) = 3 s_2(n)`. Since `v_2(C(3n, n)) =
   2 s_2(n) - s_2(3n)` and `2n - 1` is odd, `v_2(a n) = s_2(n) + s_2(3n) ≥ 3`, with equality
   iff `s_2(n) = 1`, i.e., `n = 2^k`.
-/

namespace OeisA189286Proof

open Finset PowerSeries

/- ### Part 1: Clausen identity S n = R n -/

private def T (k : ℕ) : ℕ :=
  (6 * k).choose (3 * k) * (3 * k).choose k

private def S (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (T k : ℤ) * (T (n - k) : ℤ)

private def F (n m : ℕ) : ℤ :=
  if m ≤ n then
    (T m : ℤ) * ((2 * m).choose m : ℤ) * (m.choose (n - m) : ℤ) * (-432 : ℤ) ^ (n - m)
  else 0

private def R (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n + 1), F n m

private def aCoef (n : ℤ) : ℤ :=
  24 * (2 * n + 1) * (18 * n ^ 2 + 18 * n + 5)

private def bCoef (n : ℤ) : ℤ :=
  20736 * n * (9 * n ^ 2 - 4)

private lemma T_mul_factorials (k : ℕ) :
    T k * ((3 * k).factorial * (2 * k).factorial * k.factorial) = (6 * k).factorial := by
  unfold T
  have h1 : (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial = (6 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show 3 * k ≤ 6 * k by omega)
    simpa [show 6 * k - 3 * k = 3 * k by omega] using this
  have h2 : (3 * k).choose k * k.factorial * (2 * k).factorial = (3 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 3 * k by omega)
    simpa [show 3 * k - k = 2 * k by omega] using this
  calc (6 * k).choose (3 * k) * (3 * k).choose k *
        ((3 * k).factorial * (2 * k).factorial * k.factorial)
      = (6 * k).choose (3 * k) * (3 * k).factorial *
        ((3 * k).choose k * k.factorial * (2 * k).factorial) := by ring
    _ = (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial := by rw [h2]
    _ = (6 * k).factorial := h1

private lemma T_succ (k : ℕ) :
    (k + 1) ^ 2 * T (k + 1) = 12 * (6 * k + 1) * (6 * k + 5) * T k := by
  have hpos : 0 < (3 * k).factorial * (2 * k).factorial * k.factorial := by
    exact mul_pos (mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) (Nat.factorial_pos _)
  have hpos' : 0 < (3 * (k + 1)).factorial * (2 * (k + 1)).factorial * (k + 1).factorial := by
    exact mul_pos (mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) (Nat.factorial_pos _)
  have hfac6 : (6 * (k + 1)).factorial =
      (6 * k + 6) * (6 * k + 5) * (6 * k + 4) * (6 * k + 3) * (6 * k + 2) * (6 * k + 1) *
        (6 * k).factorial := by
    have : 6 * (k + 1) = 6 * k + 6 := by omega
    rw [this]
    simp only [Nat.factorial_succ]
    ring
  have hfac3 : (3 * (k + 1)).factorial =
      (3 * k + 3) * (3 * k + 2) * (3 * k + 1) * (3 * k).factorial := by
    have : 3 * (k + 1) = 3 * k + 3 := by omega
    rw [this]
    simp only [Nat.factorial_succ]
    ring
  have hfac2 : (2 * (k + 1)).factorial =
      (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
    have : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [this]
    simp only [Nat.factorial_succ]
    ring
  have hfac1 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
  have hmul : (k + 1) ^ 2 * T (k + 1) *
      ((3 * (k + 1)).factorial * (2 * (k + 1)).factorial * (k + 1).factorial) =
      12 * (6 * k + 1) * (6 * k + 5) * T k *
      ((3 * (k + 1)).factorial * (2 * (k + 1)).factorial * (k + 1).factorial) := by
    have hT1 := T_mul_factorials (k + 1)
    have hT0 := T_mul_factorials k
    calc (k + 1) ^ 2 * T (k + 1) *
          ((3 * (k + 1)).factorial * (2 * (k + 1)).factorial * (k + 1).factorial)
        = (k + 1) ^ 2 * (T (k + 1) *
          ((3 * (k + 1)).factorial * (2 * (k + 1)).factorial * (k + 1).factorial)) := by ring
      _ = (k + 1) ^ 2 * (6 * (k + 1)).factorial := by rw [hT1]
      _ = (k + 1) ^ 2 * ((6 * k + 6) * (6 * k + 5) * (6 * k + 4) * (6 * k + 3) * (6 * k + 2) *
            (6 * k + 1) * (6 * k).factorial) := by rw [hfac6]
      _ = (k + 1) ^ 2 * ((6 * k + 6) * (6 * k + 5) * (6 * k + 4) * (6 * k + 3) * (6 * k + 2) *
            (6 * k + 1) * (T k * ((3 * k).factorial * (2 * k).factorial * k.factorial))) := by
          rw [← hT0]
      _ = 12 * (6 * k + 1) * (6 * k + 5) * T k *
          (((3 * k + 3) * (3 * k + 2) * (3 * k + 1) * (3 * k).factorial) *
           ((2 * k + 2) * (2 * k + 1) * (2 * k).factorial) *
           ((k + 1) * k.factorial)) := by ring
      _ = 12 * (6 * k + 1) * (6 * k + 5) * T k *
          ((3 * (k + 1)).factorial * (2 * (k + 1)).factorial * (k + 1).factorial) := by
          rw [← hfac3, ← hfac2, ← hfac1]
  exact Nat.eq_of_mul_eq_mul_right hpos' hmul

private lemma central_binom_succ (m : ℕ) :
    (m + 1) * (2 * (m + 1)).choose (m + 1) = 2 * (2 * m + 1) * (2 * m).choose m := by
  have h1 : (2 * (m + 1)).choose (m + 1) * (m + 1).factorial * (m + 1).factorial =
      (2 * (m + 1)).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ 2 * (m + 1) by omega)
    simpa [show 2 * (m + 1) - (m + 1) = m + 1 by omega] using this
  have h0 : (2 * m).choose m * m.factorial * m.factorial = (2 * m).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    simpa [show 2 * m - m = m by omega] using this
  have hfac2 : (2 * (m + 1)).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
    have : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [this]; simp only [Nat.factorial_succ]; ring
  have hpos : 0 < (m + 1).factorial * (m + 1).factorial :=
    mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc (m + 1) * (2 * (m + 1)).choose (m + 1) * ((m + 1).factorial * (m + 1).factorial)
      = (m + 1) * ((2 * (m + 1)).choose (m + 1) * (m + 1).factorial * (m + 1).factorial) := by ring
    _ = (m + 1) * (2 * (m + 1)).factorial := by rw [h1]
    _ = (m + 1) * ((2 * m + 2) * (2 * m + 1) * ((2 * m).choose m * m.factorial * m.factorial)) := by
        rw [hfac2, ← h0]
    _ = 2 * (2 * m + 1) * (2 * m).choose m * (((m + 1) * m.factorial) * ((m + 1) * m.factorial)) := by
        ring
    _ = 2 * (2 * m + 1) * (2 * m).choose m * ((m + 1).factorial * (m + 1).factorial) := by
        rw [← Nat.factorial_succ]

/- Euler operator θ on PowerSeries ℤ -/

private noncomputable def theta (f : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (n : ℤ) * PowerSeries.coeff n f

private lemma coeff_theta (n : ℕ) (f : PowerSeries ℤ) :
    PowerSeries.coeff n (theta f) = (n : ℤ) * PowerSeries.coeff n f := by
  simp [theta]

private lemma theta_add (f g : PowerSeries ℤ) : theta (f + g) = theta f + theta g := by
  ext n; simp [coeff_theta]; ring

private lemma theta_sub (f g : PowerSeries ℤ) : theta (f - g) = theta f - theta g := by
  ext n; simp [coeff_theta]; ring

private lemma theta_C_mul (c : ℤ) (f : PowerSeries ℤ) :
    theta (PowerSeries.C c * f) = PowerSeries.C c * theta f := by
  ext n
  rw [coeff_theta, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, coeff_theta]
  ring

private lemma theta_X : theta (PowerSeries.X : PowerSeries ℤ) = PowerSeries.X := by
  ext n
  simp only [coeff_theta, PowerSeries.coeff_X]
  split_ifs with h
  · subst h; simp
  · simp

private lemma theta_mul (f g : PowerSeries ℤ) :
    theta (f * g) = theta f * g + f * theta g := by
  ext n
  simp only [coeff_theta, map_add, PowerSeries.coeff_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hsum : x.1 + x.2 = n := by simpa using hx
  have hcast : (n : ℤ) = (x.1 : ℤ) + (x.2 : ℤ) := by exact_mod_cast hsum.symm
  rw [hcast]
  ring

private lemma coeff_X_mul_succ (n : ℕ) (f : PowerSeries ℤ) :
    PowerSeries.coeff (n + 1) (PowerSeries.X * f) = PowerSeries.coeff n f := by
  simp

private lemma coeff_X_sq_mul_succ2 (n : ℕ) (f : PowerSeries ℤ) :
    PowerSeries.coeff (n + 2) (PowerSeries.X ^ 2 * f) = PowerSeries.coeff n f := by
  simp

private lemma S_rec (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℤ) ^ 3) * S (n + 1) = aCoef n * S n - bCoef n * S (n - 1) := by
  set y : PowerSeries ℤ := PowerSeries.mk fun k => (T k : ℤ)
  set X : PowerSeries ℤ := PowerSeries.X
  set c432 : PowerSeries ℤ := PowerSeries.C 432
  set c60 : PowerSeries ℤ := PowerSeries.C 60
  set u : PowerSeries ℤ := 1 - c432 * X
  have hy_coeff : ∀ k, PowerSeries.coeff k y = (T k : ℤ) := fun k => by simp [y]
  -- 2nd-order ODE: (1 - 432 X) θ² y = 432 X θ y + 60 X y
  have hODE2 : u * theta (theta y) = c432 * X * theta y + c60 * X * y := by
    ext k
    cases k with
    | zero =>
      simp only [u, X, c432, c60, sub_mul, one_mul, map_sub, map_add, PowerSeries.coeff_zero_eq_constantCoeff]
      have h0 : PowerSeries.constantCoeff (theta (theta y)) = 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_theta]; simp
      simp [h0]
    | succ k =>
      have hT : ((k + 1 : ℤ) ^ 2) * (T (k + 1) : ℤ) =
          12 * (6 * (k : ℤ) + 1) * (6 * (k : ℤ) + 5) * (T k : ℤ) := by
        exact_mod_cast T_succ k
      have hX1 : PowerSeries.coeff (k + 1) (X * theta (theta y)) = (k : ℤ) ^ 2 * (T k : ℤ) := by
        rw [coeff_X_mul_succ, coeff_theta, coeff_theta, hy_coeff]; ring
      have hX2 : PowerSeries.coeff (k + 1) (X * theta y) = (k : ℤ) * (T k : ℤ) := by
        rw [coeff_X_mul_succ, coeff_theta, hy_coeff]
      have hX3 : PowerSeries.coeff (k + 1) (X * y) = (T k : ℤ) := by
        rw [coeff_X_mul_succ, hy_coeff]
      have hlhs : PowerSeries.coeff (k + 1) (u * theta (theta y)) =
          ((k + 1 : ℤ) ^ 2) * (T (k + 1) : ℤ) - 432 * ((k : ℤ) ^ 2 * (T k : ℤ)) := by
        have : u * theta (theta y) = theta (theta y) - c432 * (X * theta (theta y)) := by
          simp only [u]; ring
        rw [this, map_sub, PowerSeries.coeff_C_mul, hX1, coeff_theta, coeff_theta, hy_coeff]
        push_cast; ring
      have hrhs : PowerSeries.coeff (k + 1) (c432 * X * theta y + c60 * X * y) =
          432 * ((k : ℤ) * (T k : ℤ)) + 60 * (T k : ℤ) := by
        have : c432 * X * theta y + c60 * X * y = c432 * (X * theta y) + c60 * (X * y) := by ring
        rw [this, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, hX2, hX3]
      rw [hlhs, hrhs, hT]
      ring
  set Y : PowerSeries ℤ := y * y
  have hY_coeff : ∀ k, PowerSeries.coeff k Y = S k := by
    intro k
    rw [show Y = y * y from rfl, PowerSeries.coeff_mul]
    simp only [hy_coeff]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (T i : ℤ) * (T j : ℤ)) k
  have hC2 : (PowerSeries.C 2 : PowerSeries ℤ) = 1 + 1 := by
    rw [show (2 : ℤ) = 1 + 1 by norm_num, map_add, map_one]
  have hθY : theta Y = PowerSeries.C 2 * (y * theta y) := by
    have : theta (y * y) = theta y * y + y * theta y := theta_mul y y
    rw [show Y = y * y from rfl, this, hC2]; ring
  have hθ2Y : theta (theta Y) =
      PowerSeries.C 2 * (theta y * theta y) + PowerSeries.C 2 * (y * theta (theta y)) := by
    rw [hθY, theta_C_mul, theta_mul]; ring
  have hstep2 : u * theta (theta Y) =
      PowerSeries.C 2 * (u * (theta y * theta y)) + c432 * X * theta Y + PowerSeries.C 120 * X * Y := by
    have hc120 : (PowerSeries.C 120 : PowerSeries ℤ) = PowerSeries.C 2 * c60 := by
      simp only [c60, ← map_mul]; norm_num
    calc u * theta (theta Y)
        = PowerSeries.C 2 * (u * (theta y * theta y)) +
          PowerSeries.C 2 * (y * (u * theta (theta y))) := by rw [hθ2Y]; ring
      _ = PowerSeries.C 2 * (u * (theta y * theta y)) +
          PowerSeries.C 2 * (y * (c432 * X * theta y + c60 * X * y)) := by rw [hODE2]
      _ = PowerSeries.C 2 * (u * (theta y * theta y)) +
          c432 * X * (PowerSeries.C 2 * (y * theta y)) +
          (PowerSeries.C 2 * c60) * X * (y * y) := by ring
      _ = PowerSeries.C 2 * (u * (theta y * theta y)) + c432 * X * theta Y + PowerSeries.C 120 * X * Y := by
          rw [← hθY, ← hc120]
  have hθu : theta u = -(c432 * X) := by
    have h1 : theta (1 : PowerSeries ℤ) = 0 := by
      ext k; simp [coeff_theta, PowerSeries.coeff_one]
    rw [show u = 1 - c432 * X from rfl, theta_sub, h1, zero_sub, theta_C_mul, theta_X]
  -- Apply θ to hstep2
  have hθstep2 :
      -(c432 * X) * theta (theta Y) + u * theta (theta (theta Y)) =
      PowerSeries.C 864 * X * (theta y * theta y) +
      c432 * X * theta (theta Y) + PowerSeries.C 672 * X * theta Y + PowerSeries.C 120 * X * Y := by
    have hA : theta (u * theta (theta Y)) =
        -(c432 * X) * theta (theta Y) + u * theta (theta (theta Y)) := by
      rw [theta_mul, hθu]
    have hB1 : theta (PowerSeries.C 2 * (u * (theta y * theta y))) =
        PowerSeries.C 864 * X * (theta y * theta y) + PowerSeries.C 120 * X * theta Y := by
      rw [theta_C_mul, theta_mul, hθu, theta_mul]
      have hC1 : PowerSeries.C 2 * (-(c432 * X) * (theta y * theta y) +
            u * (theta (theta y) * theta y + theta y * theta (theta y))) =
          -(PowerSeries.C 2 * c432) * X * (theta y * theta y) +
          PowerSeries.C 4 * theta y * (u * theta (theta y)) := by
        have h4 : (PowerSeries.C 4 : PowerSeries ℤ) = PowerSeries.C 2 * PowerSeries.C 2 := by
          rw [← map_mul]; norm_num
        rw [h4, hC2]; ring
      rw [hC1, hODE2]
      have h864 : (PowerSeries.C 864 : PowerSeries ℤ) =
          -(PowerSeries.C 2 * c432) + PowerSeries.C 4 * c432 := by
        simp only [c432, ← map_mul, ← map_neg, ← map_add]; norm_num
      have h120 : (PowerSeries.C 120 : PowerSeries ℤ) * PowerSeries.C 2 =
          PowerSeries.C 4 * c60 := by
        simp only [c60, ← map_mul]; norm_num
      calc -(PowerSeries.C 2 * c432) * X * (theta y * theta y) +
              PowerSeries.C 4 * theta y * (c432 * X * theta y + c60 * X * y)
          = (-(PowerSeries.C 2 * c432) + PowerSeries.C 4 * c432) * X * (theta y * theta y) +
            (PowerSeries.C 4 * c60) * X * (y * theta y) := by ring
        _ = PowerSeries.C 864 * X * (theta y * theta y) +
            PowerSeries.C 120 * X * (PowerSeries.C 2 * (y * theta y)) := by
            rw [← h864, ← h120]; ring
        _ = PowerSeries.C 864 * X * (theta y * theta y) + PowerSeries.C 120 * X * theta Y := by
            rw [← hθY]
    have hB2 : theta (c432 * X * theta Y) = c432 * X * theta Y + c432 * X * theta (theta Y) := by
      have : c432 * X * theta Y = c432 * (X * theta Y) := by ring
      rw [this, theta_C_mul, theta_mul, theta_X]; ring
    have hB3 : theta (PowerSeries.C 120 * X * Y) =
        PowerSeries.C 120 * X * Y + PowerSeries.C 120 * X * theta Y := by
      have : PowerSeries.C 120 * X * Y = PowerSeries.C 120 * (X * Y) := by ring
      rw [this, theta_C_mul, theta_mul, theta_X]; ring
    have h672 : (PowerSeries.C 672 : PowerSeries ℤ) =
        PowerSeries.C 120 + c432 + PowerSeries.C 120 := by
      simp only [c432, ← map_add]; norm_num
    have h := congrArg theta hstep2
    rw [hA, theta_add, theta_add, hB1, hB2, hB3] at h
    rw [h, h672]; ring
  -- Eliminate (theta y)^2 by multiplying hθstep2 by u and substituting hstep2
  have hODE3 :
      theta (theta (theta Y)) -
      X * (PowerSeries.C 864 * theta (theta (theta Y)) + PowerSeries.C 1296 * theta (theta Y) +
           PowerSeries.C 672 * theta Y + PowerSeries.C 120 * Y) +
      X ^ 2 * (PowerSeries.C 186624 * theta (theta (theta Y)) +
               PowerSeries.C 559872 * theta (theta Y) +
               PowerSeries.C 476928 * theta Y +
               PowerSeries.C 103680 * Y) = 0 := by
    have hsub_y2 : PowerSeries.C 2 * (u * (theta y * theta y)) =
        u * theta (theta Y) - c432 * X * theta Y - PowerSeries.C 120 * X * Y := by
      linear_combination -hstep2
    have h864_eq : (PowerSeries.C 864 : PowerSeries ℤ) = c432 * PowerSeries.C 2 := by
      simp only [c432, ← map_mul]; norm_num
    have hcomb : u * (-(c432 * X) * theta (theta Y) + u * theta (theta (theta Y))) =
        c432 * X * (u * theta (theta Y) - c432 * X * theta Y - PowerSeries.C 120 * X * Y) +
        u * (c432 * X * theta (theta Y) + PowerSeries.C 672 * X * theta Y + PowerSeries.C 120 * X * Y) := by
      calc u * (-(c432 * X) * theta (theta Y) + u * theta (theta (theta Y)))
          = u * (PowerSeries.C 864 * X * (theta y * theta y) +
              c432 * X * theta (theta Y) + PowerSeries.C 672 * X * theta Y + PowerSeries.C 120 * X * Y) := by
            rw [hθstep2]
        _ = c432 * X * (PowerSeries.C 2 * (u * (theta y * theta y))) +
            u * (c432 * X * theta (theta Y) + PowerSeries.C 672 * X * theta Y + PowerSeries.C 120 * X * Y) := by
            rw [h864_eq]; ring
        _ = c432 * X * (u * theta (theta Y) - c432 * X * theta Y - PowerSeries.C 120 * X * Y) +
            u * (c432 * X * theta (theta Y) + PowerSeries.C 672 * X * theta Y + PowerSeries.C 120 * X * Y) := by
            rw [hsub_y2]
    have hc_864 : (PowerSeries.C 864 : PowerSeries ℤ) = PowerSeries.C 2 * c432 := by
      simp only [c432, ← map_mul]; norm_num
    have hc_1296 : (PowerSeries.C 1296 : PowerSeries ℤ) = PowerSeries.C 3 * c432 := by
      simp only [c432, ← map_mul]; norm_num
    have hc_186624 : (PowerSeries.C 186624 : PowerSeries ℤ) = c432 * c432 := by
      simp only [c432, ← map_mul]; norm_num
    have hc_559872 : (PowerSeries.C 559872 : PowerSeries ℤ) = PowerSeries.C 3 * c432 * c432 := by
      simp only [c432, ← map_mul]; norm_num
    have hc_476928 : (PowerSeries.C 476928 : PowerSeries ℤ) =
        c432 * c432 + c432 * PowerSeries.C 672 := by
      simp only [c432, ← map_mul, ← map_add]; norm_num
    have hc_103680 : (PowerSeries.C 103680 : PowerSeries ℤ) =
        PowerSeries.C 2 * c432 * PowerSeries.C 120 := by
      simp only [c432, ← map_mul]; norm_num
    have h3 : (PowerSeries.C 3 : PowerSeries ℤ) = 1 + 1 + 1 := by
      rw [show (3 : ℤ) = 1 + 1 + 1 by norm_num, map_add, map_add, map_one]
    rw [hc_864, hc_1296, hc_186624, hc_559872, hc_476928, hc_103680, hC2, h3]
    simp only [u] at hcomb
    linear_combination hcomb
  -- Extract coefficient n + 1 from hODE3
  have hm_eq : n - 1 + 2 = n + 1 := by omega
  have hc := congrArg (PowerSeries.coeff (n + 1)) hODE3
  simp only [map_add, map_sub, map_zero] at hc
  have h0 : PowerSeries.coeff (n + 1) (theta (theta (theta Y))) = ((n + 1 : ℤ) ^ 3) * S (n + 1) := by
    simp only [coeff_theta, hY_coeff]; push_cast; ring
  have h1 : PowerSeries.coeff (n + 1)
      (X * (PowerSeries.C 864 * theta (theta (theta Y)) + PowerSeries.C 1296 * theta (theta Y) +
            PowerSeries.C 672 * theta Y + PowerSeries.C 120 * Y)) =
      aCoef n * S n := by
    rw [coeff_X_mul_succ]
    simp only [map_add, PowerSeries.coeff_C_mul, coeff_theta, hY_coeff, aCoef]
    ring
  have h2 : PowerSeries.coeff (n + 1)
      (X ^ 2 * (PowerSeries.C 186624 * theta (theta (theta Y)) +
                PowerSeries.C 559872 * theta (theta Y) +
                PowerSeries.C 476928 * theta Y +
                PowerSeries.C 103680 * Y)) =
      bCoef n * S (n - 1) := by
    rw [← hm_eq, coeff_X_sq_mul_succ2]
    simp only [map_add, PowerSeries.coeff_C_mul, coeff_theta, hY_coeff, bCoef]
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rw [hcast]
    ring
  rw [h0, h1, h2] at hc
  linarith

/- Zeilberger telescoping for R n -/

private def G (n m : ℕ) : ℤ :=
  -((n + 1 : ℤ)) * (m : ℤ) ^ 2 * F (n + 1) m

private lemma choose_step_int (m r : ℕ) :
    ((r + 1 : ℤ)) * (m.choose (r + 1) : ℤ) = ((m : ℤ) - (r : ℤ)) * (m.choose r : ℤ) := by
  by_cases h : r ≤ m
  · have hnat : m.choose (r + 1) * (r + 1) = m.choose r * (m - r) := by
      have := Nat.choose_succ_right_eq m r
      linarith
    have hcast : ((m - r : ℕ) : ℤ) = (m : ℤ) - (r : ℤ) := by omega
    have hz : (m.choose (r + 1) : ℤ) * (r + 1 : ℤ) = (m.choose r : ℤ) * ((m - r : ℕ) : ℤ) := by
      exact_mod_cast hnat
    rw [hcast] at hz
    linarith
  · have h1 : m.choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : m.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h2]

private lemma choose_succ_left_int (m r : ℕ) :
    ((m + 1 - r : ℤ)) * ((m + 1).choose r : ℤ) = ((m + 1 : ℤ)) * (m.choose r : ℤ) := by
  by_cases h : r ≤ m
  · have hnat : (m + 1).choose r * (m + 1 - r) = (m + 1) * m.choose r := by
      have h1 : (m + 1).choose r * r.factorial * (m + 1 - r).factorial = (m + 1).factorial :=
        Nat.choose_mul_factorial_mul_factorial (by omega)
      have h0 : m.choose r * r.factorial * (m - r).factorial = m.factorial :=
        Nat.choose_mul_factorial_mul_factorial h
      have hpos : 0 < r.factorial * (m - r).factorial :=
        mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
      have hsub : m + 1 - r = (m - r) + 1 := by omega
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      calc (m + 1).choose r * (m + 1 - r) * (r.factorial * (m - r).factorial)
          = (m + 1).choose r * r.factorial * ((m + 1 - r) * (m - r).factorial) := by ring
        _ = (m + 1).choose r * r.factorial * (m + 1 - r).factorial := by
            rw [hsub, Nat.factorial_succ]
        _ = (m + 1).factorial := h1
        _ = (m + 1) * m.factorial := Nat.factorial_succ m
        _ = (m + 1) * (m.choose r * r.factorial * (m - r).factorial) := by rw [← h0]
        _ = (m + 1) * m.choose r * (r.factorial * (m - r).factorial) := by ring
    have hcast : ((m + 1 - r : ℕ) : ℤ) = (m + 1 : ℤ) - (r : ℤ) := by omega
    have hz : ((m + 1).choose r : ℤ) * ((m + 1 - r : ℕ) : ℤ) = ((m + 1 : ℤ)) * (m.choose r : ℤ) := by
      exact_mod_cast hnat
    rw [hcast] at hz
    linarith
  · by_cases heq : r = m + 1
    · subst heq
      simp
    · have h1 : (m + 1).choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have h0 : m.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h1, h0]

private lemma F_telescope (n m : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℤ) ^ 3) * F (n + 1) m - aCoef n * F n m + bCoef n * F (n - 1) m =
    G n (m + 1) - G n m := by
  -- Express all terms in terms of C_m := T m * C(2m, m) and binomials of m
  set Cm : ℤ := (T m : ℤ) * ((2 * m).choose m : ℤ)
  have hCsucc : ((m + 1 : ℤ) ^ 3) * ((T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ)) =
      24 * (2 * (m : ℤ) + 1) * (6 * (m : ℤ) + 1) * (6 * (m : ℤ) + 5) * Cm := by
    have hT : ((m + 1 : ℤ) ^ 2) * (T (m + 1) : ℤ) =
        12 * (6 * (m : ℤ) + 1) * (6 * (m : ℤ) + 5) * (T m : ℤ) := by exact_mod_cast T_succ m
    have hB : ((m + 1 : ℤ)) * ((2 * (m + 1)).choose (m + 1) : ℤ) =
        2 * (2 * (m : ℤ) + 1) * ((2 * m).choose m : ℤ) := by exact_mod_cast central_binom_succ m
    calc ((m + 1 : ℤ) ^ 3) * ((T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ))
        = (((m + 1 : ℤ) ^ 2) * (T (m + 1) : ℤ)) *
          (((m + 1 : ℤ)) * ((2 * (m + 1)).choose (m + 1) : ℤ)) := by ring
      _ = (12 * (6 * (m : ℤ) + 1) * (6 * (m : ℤ) + 5) * (T m : ℤ)) *
          (2 * (2 * (m : ℤ) + 1) * ((2 * m).choose m : ℤ)) := by rw [hT, hB]
      _ = 24 * (2 * (m : ℤ) + 1) * (6 * (m : ℤ) + 1) * (6 * (m : ℤ) + 5) * Cm := by
          simp only [Cm]; ring
  -- Split into regions of m relative to n
  by_cases hm_gt : n + 1 < m
  · have h1 : F (n + 1) m = 0 := by simp [F, show ¬ m ≤ n + 1 by omega]
    have h2 : F n m = 0 := by simp [F, show ¬ m ≤ n by omega]
    have h3 : F (n - 1) m = 0 := by simp [F, show ¬ m ≤ n - 1 by omega]
    have h4 : F (n + 1) (m + 1) = 0 := by simp [F, show ¬ m + 1 ≤ n + 1 by omega]
    simp [G, h1, h2, h3, h4]
  · by_cases hm_eq1 : m = n + 1
    · subst hm_eq1
      have h1 : F (n + 1) (n + 1) = Cm := by simp [F, Cm]
      have h2 : F n (n + 1) = 0 := by simp [F]
      have h3 : F (n - 1) (n + 1) = 0 := by simp [F, show ¬ n + 1 ≤ n - 1 by omega]
      have h4 : F (n + 1) (n + 2) = 0 := by simp [F]
      simp [G, h1, h2, h3, h4]
      ring
    · by_cases hm_eq0 : m = n
      · subst hm_eq0
        have h1 : F (m + 1) m = Cm * (m : ℤ) * (-432 : ℤ) := by
          simp only [F, Cm, show m ≤ m + 1 by omega, ite_true,
            show m + 1 - m = 1 by omega, Nat.choose_one_right, pow_one]
        have h2 : F m m = Cm := by simp [F, Cm]
        have h3 : F (m - 1) m = 0 := by simp [F, show ¬ m ≤ m - 1 by omega]
        have h4 : F (m + 1) (m + 1) =
            (T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ) := by simp [F]
        have hG1 : G m (m + 1) = -((m + 1 : ℤ) ^ 3) *
            ((T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ)) := by
          simp only [G, h4]; push_cast; ring
        have hG0 : G m m = -((m + 1 : ℤ)) * (m : ℤ) ^ 2 * F (m + 1) m := rfl
        rw [hG1, hG0, h1, h2, h3]
        have hneg : -((m + 1 : ℤ) ^ 3) * ((T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ)) =
            -(24 * (2 * (m : ℤ) + 1) * (6 * (m : ℤ) + 1) * (6 * (m : ℤ) + 5) * Cm) := by
          linear_combination -hCsucc
        rw [hneg]
        simp only [aCoef, bCoef]
        ring
      · -- General case: m ≤ n - 1
        have hm_le : m ≤ n - 1 := by omega
        set r : ℕ := n - 1 - m
        have hr1 : n - m = r + 1 := by omega
        have hr2 : n + 1 - m = r + 2 := by omega
        have hr3 : n + 1 - (m + 1) = r + 1 := by omega
        have hF_nm1 : F (n - 1) m = Cm * (m.choose r : ℤ) * (-432 : ℤ) ^ r := by
          simp only [F, Cm, hm_le, ite_true, r]
        have hF_n : F n m = Cm * (m.choose (r + 1) : ℤ) * (-432 : ℤ) ^ (r + 1) := by
          simp only [F, Cm, show m ≤ n by omega, ite_true, hr1]
        have hF_np1 : F (n + 1) m = Cm * (m.choose (r + 2) : ℤ) * (-432 : ℤ) ^ (r + 2) := by
          simp only [F, Cm, show m ≤ n + 1 by omega, ite_true, hr2]
        have hF_mp1 : F (n + 1) (m + 1) =
            ((T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ)) *
            ((m + 1).choose (r + 1) : ℤ) * (-432 : ℤ) ^ (r + 1) := by
          simp only [F, show m + 1 ≤ n + 1 by omega, ite_true, hr3]
        -- Clear positive integer factor (m + 1) * (r + 1) * (r + 2) * (m - r)
        by_cases hrm : m < r
        · have hc0 : m.choose r = 0 := Nat.choose_eq_zero_of_lt hrm
          have hc1 : m.choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          have hc2 : m.choose (r + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          have hc3 : (m + 1).choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          simp [G, hF_nm1, hF_n, hF_np1, hF_mp1, hc0, hc1, hc2, hc3]
        · by_cases hreq : m = r
          · -- Boundary case r = m (so n = 2m + 1): m.choose (m+1) = m.choose (m+2) = 0, (m+1).choose (m+1) = 1
            have hc0 : m.choose r = 1 := by rw [← hreq, Nat.choose_self]
            have hc1 : m.choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
            have hc2 : m.choose (r + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
            have hc3 : (m + 1).choose (r + 1) = 1 := by rw [← hreq, Nat.choose_self]
            have hn_eq : (n : ℤ) = 2 * (m : ℤ) + 1 := by omega
            simp only [G, hF_nm1, hF_n, hF_np1, hF_mp1, hc0, hc1, hc2, hc3,
              Nat.cast_one, Nat.cast_zero, mul_zero, zero_mul, mul_one, sub_zero]
            push_cast
            have hneg : -((n + 1 : ℤ)) * ((m + 1 : ℤ) ^ 2) *
                ((T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ) * (-432 : ℤ) ^ (r + 1)) =
                -2 * (24 * (2 * (m : ℤ) + 1) * (6 * (m : ℤ) + 1) * (6 * (m : ℤ) + 5) * Cm) *
                  (-432 : ℤ) ^ (r + 1) := by
              calc -((n + 1 : ℤ)) * ((m + 1 : ℤ) ^ 2) *
                    ((T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ) * (-432 : ℤ) ^ (r + 1))
                  = -2 * (((m + 1 : ℤ) ^ 3) *
                      ((T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ))) * (-432 : ℤ) ^ (r + 1) := by
                    rw [hn_eq]; ring
                _ = -2 * (24 * (2 * (m : ℤ) + 1) * (6 * (m : ℤ) + 1) * (6 * (m : ℤ) + 5) * Cm) *
                      (-432 : ℤ) ^ (r + 1) := by rw [hCsucc]
            rw [hneg, pow_succ, hn_eq]
            simp only [bCoef]
            ring
          · -- Interior case r < m (so m - r ≥ 1)
            have hr_lt : r < m := by omega
            have hmul_ne : ((m + 1 : ℤ) * ((r + 1 : ℤ)) * ((r + 2 : ℤ)) * ((m : ℤ) - (r : ℤ))) ≠ 0 := by
              have h1 : (m + 1 : ℤ) ≠ 0 := by omega
              have h2 : (r + 1 : ℤ) ≠ 0 := by omega
              have h3 : (r + 2 : ℤ) ≠ 0 := by omega
              have h4 : (m : ℤ) - (r : ℤ) ≠ 0 := by omega
              exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4
            refine mul_left_cancel₀ hmul_ne ?_
            have hch1 := choose_step_int m r
            have hch2 := choose_step_int m (r + 1)
            push_cast at hch2
            have hch3 := choose_succ_left_int m (r + 1)
            have hn_eq : (n : ℤ) = (m : ℤ) + (r : ℤ) + 1 := by omega
            -- Express all binomials in terms of (m.choose r : ℤ) after multiplying by the denominator
            have hB1 : ((r + 1 : ℤ)) * (m.choose (r + 1) : ℤ) = ((m : ℤ) - (r : ℤ)) * (m.choose r : ℤ) := hch1
            have hB2 : ((r + 1 : ℤ)) * ((r + 2 : ℤ)) * (m.choose (r + 2) : ℤ) =
                ((m : ℤ) - (r : ℤ)) * ((m : ℤ) - (r : ℤ) - 1) * (m.choose r : ℤ) := by
              calc ((r + 1 : ℤ)) * ((r + 2 : ℤ)) * (m.choose (r + 2) : ℤ)
                  = ((r + 1 : ℤ)) * (((r + 1 + 1 : ℤ)) * (m.choose (r + 1 + 1) : ℤ)) := by ring
                _ = ((r + 1 : ℤ)) * (((m : ℤ) - ((r : ℤ) + 1)) * (m.choose (r + 1) : ℤ)) := by
                    rw [hch2]
                _ = ((m : ℤ) - (r : ℤ) - 1) * (((r + 1 : ℤ)) * (m.choose (r + 1) : ℤ)) := by
                    ring
                _ = ((m : ℤ) - (r : ℤ)) * ((m : ℤ) - (r : ℤ) - 1) * (m.choose r : ℤ) := by
                    rw [hB1]; ring
            have hB3 : ((r + 1 : ℤ)) * ((m : ℤ) - (r : ℤ)) * ((m + 1).choose (r + 1) : ℤ) =
                ((m + 1 : ℤ)) * ((m : ℤ) - (r : ℤ)) * (m.choose r : ℤ) := by
              have hch3' : ((m : ℤ) - (r : ℤ)) * ((m + 1).choose (r + 1) : ℤ) =
                  ((m + 1 : ℤ)) * (m.choose (r + 1) : ℤ) := by
                have := hch3
                push_cast at this
                linarith
              calc ((r + 1 : ℤ)) * ((m : ℤ) - (r : ℤ)) * ((m + 1).choose (r + 1) : ℤ)
                  = ((r + 1 : ℤ)) * (((m : ℤ) - (r : ℤ)) * ((m + 1).choose (r + 1) : ℤ)) := by ring
                _ = ((m + 1 : ℤ)) * (((r + 1 : ℤ)) * (m.choose (r + 1) : ℤ)) := by
                    rw [hch3']; ring
                _ = ((m + 1 : ℤ)) * ((m : ℤ) - (r : ℤ)) * (m.choose r : ℤ) := by rw [hB1]; ring
            simp only [G, hF_nm1, hF_n, hF_np1, hF_mp1]
            have hpow1 : (-432 : ℤ) ^ (r + 1) = (-432 : ℤ) * (-432 : ℤ) ^ r := by rw [pow_succ]; ring
            have hpow2 : (-432 : ℤ) ^ (r + 2) = (-432 : ℤ) ^ 2 * (-432 : ℤ) ^ r := by
              rw [pow_succ, pow_succ]; ring
            rw [hpow1, hpow2]
            -- Replace the G(n, m+1) term using hCsucc and hB3
            have hG_mp1 :
                ((m + 1 : ℤ) * (r + 1 : ℤ) * (r + 2 : ℤ) * ((m : ℤ) - (r : ℤ))) *
                (-((n + 1 : ℤ)) * ((m + 1 : ℤ) ^ 2) *
                  ((T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ) *
                   ((m + 1).choose (r + 1) : ℤ) * (-432 * (-432 : ℤ) ^ r))) =
                -((n + 1 : ℤ)) * (r + 2 : ℤ) *
                  (24 * (2 * (m : ℤ) + 1) * (6 * (m : ℤ) + 1) * (6 * (m : ℤ) + 5) * Cm) *
                  (((m + 1 : ℤ)) * ((m : ℤ) - (r : ℤ)) * (m.choose r : ℤ)) *
                  (-432 * (-432 : ℤ) ^ r) := by
              calc ((m + 1 : ℤ) * (r + 1 : ℤ) * (r + 2 : ℤ) * ((m : ℤ) - (r : ℤ))) *
                    (-((n + 1 : ℤ)) * ((m + 1 : ℤ) ^ 2) *
                      ((T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ) *
                       ((m + 1).choose (r + 1) : ℤ) * (-432 * (-432 : ℤ) ^ r)))
                  = -((n + 1 : ℤ)) * (r + 2 : ℤ) *
                    (((m + 1 : ℤ) ^ 3) * ((T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ))) *
                    (((r + 1 : ℤ)) * ((m : ℤ) - (r : ℤ)) * ((m + 1).choose (r + 1) : ℤ)) *
                    (-432 * (-432 : ℤ) ^ r) := by ring
                _ = -((n + 1 : ℤ)) * (r + 2 : ℤ) *
                    (24 * (2 * (m : ℤ) + 1) * (6 * (m : ℤ) + 1) * (6 * (m : ℤ) + 5) * Cm) *
                    (((m + 1 : ℤ)) * ((m : ℤ) - (r : ℤ)) * (m.choose r : ℤ)) *
                    (-432 * (-432 : ℤ) ^ r) := by rw [hCsucc, hB3]
            have hT_np1 :
                ((m + 1 : ℤ) * (r + 1 : ℤ) * (r + 2 : ℤ) * ((m : ℤ) - (r : ℤ))) *
                (Cm * (m.choose (r + 2) : ℤ) * ((-432 : ℤ) ^ 2 * (-432 : ℤ) ^ r)) =
                (m + 1 : ℤ) * ((m : ℤ) - (r : ℤ)) * Cm *
                (((m : ℤ) - (r : ℤ)) * ((m : ℤ) - (r : ℤ) - 1) * (m.choose r : ℤ)) *
                ((-432 : ℤ) ^ 2 * (-432 : ℤ) ^ r) := by
              calc ((m + 1 : ℤ) * (r + 1 : ℤ) * (r + 2 : ℤ) * ((m : ℤ) - (r : ℤ))) *
                    (Cm * (m.choose (r + 2) : ℤ) * ((-432 : ℤ) ^ 2 * (-432 : ℤ) ^ r))
                  = (m + 1 : ℤ) * ((m : ℤ) - (r : ℤ)) * Cm *
                    (((r + 1 : ℤ)) * ((r + 2 : ℤ)) * (m.choose (r + 2) : ℤ)) *
                    ((-432 : ℤ) ^ 2 * (-432 : ℤ) ^ r) := by ring
                _ = _ := by rw [hB2]
            have hT_n :
                ((m + 1 : ℤ) * (r + 1 : ℤ) * (r + 2 : ℤ) * ((m : ℤ) - (r : ℤ))) *
                (Cm * (m.choose (r + 1) : ℤ) * (-432 * (-432 : ℤ) ^ r)) =
                (m + 1 : ℤ) * (r + 2 : ℤ) * ((m : ℤ) - (r : ℤ)) * Cm *
                (((m : ℤ) - (r : ℤ)) * (m.choose r : ℤ)) *
                (-432 * (-432 : ℤ) ^ r) := by
              calc ((m + 1 : ℤ) * (r + 1 : ℤ) * (r + 2 : ℤ) * ((m : ℤ) - (r : ℤ))) *
                    (Cm * (m.choose (r + 1) : ℤ) * (-432 * (-432 : ℤ) ^ r))
                  = (m + 1 : ℤ) * (r + 2 : ℤ) * ((m : ℤ) - (r : ℤ)) * Cm *
                    (((r + 1 : ℤ)) * (m.choose (r + 1) : ℤ)) *
                    (-432 * (-432 : ℤ) ^ r) := by ring
                _ = _ := by rw [hB1]
            set M : ℤ := (m + 1 : ℤ) * (r + 1 : ℤ) * (r + 2 : ℤ) * ((m : ℤ) - (r : ℤ))
            have hL1 : M *
                (((n + 1 : ℤ) ^ 3) * (Cm * (m.choose (r + 2) : ℤ) * ((-432 : ℤ) ^ 2 * (-432 : ℤ) ^ r))) =
                ((n + 1 : ℤ) ^ 3) *
                ((m + 1 : ℤ) * ((m : ℤ) - (r : ℤ)) * Cm *
                 (((m : ℤ) - (r : ℤ)) * ((m : ℤ) - (r : ℤ) - 1) * (m.choose r : ℤ)) *
                 ((-432 : ℤ) ^ 2 * (-432 : ℤ) ^ r)) := by
              rw [← hT_np1]; ring
            have hL2 : M *
                (aCoef n * (Cm * (m.choose (r + 1) : ℤ) * (-432 * (-432 : ℤ) ^ r))) =
                aCoef n *
                ((m + 1 : ℤ) * (r + 2 : ℤ) * ((m : ℤ) - (r : ℤ)) * Cm *
                 (((m : ℤ) - (r : ℤ)) * (m.choose r : ℤ)) *
                 (-432 * (-432 : ℤ) ^ r)) := by
              rw [← hT_n]; ring
            have hR2 : M *
                (-((n + 1 : ℤ)) * (m : ℤ) ^ 2 * (Cm * (m.choose (r + 2) : ℤ) * ((-432 : ℤ) ^ 2 * (-432 : ℤ) ^ r))) =
                -((n + 1 : ℤ)) * (m : ℤ) ^ 2 *
                ((m + 1 : ℤ) * ((m : ℤ) - (r : ℤ)) * Cm *
                 (((m : ℤ) - (r : ℤ)) * ((m : ℤ) - (r : ℤ) - 1) * (m.choose r : ℤ)) *
                 ((-432 : ℤ) ^ 2 * (-432 : ℤ) ^ r)) := by
              rw [← hT_np1]; ring
            have hG_mp1' : M *
                (-((n + 1 : ℤ)) * (((m + 1 : ℕ) : ℤ) ^ 2) *
                  ((T (m + 1) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ) *
                   ((m + 1).choose (r + 1) : ℤ) * (-432 * (-432 : ℤ) ^ r))) =
                -((n + 1 : ℤ)) * (r + 2 : ℤ) *
                  (24 * (2 * (m : ℤ) + 1) * (6 * (m : ℤ) + 1) * (6 * (m : ℤ) + 5) * Cm) *
                  (((m + 1 : ℤ)) * ((m : ℤ) - (r : ℤ)) * (m.choose r : ℤ)) *
                  (-432 * (-432 : ℤ) ^ r) := by
              rw [Nat.cast_add, Nat.cast_one]
              exact hG_mp1
            change M * _ = M * _
            rw [mul_add, mul_sub, mul_sub, hL1, hL2, hG_mp1', hR2, hn_eq]
            simp only [M, aCoef, bCoef]
            ring

private lemma R_rec (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℤ) ^ 3) * R (n + 1) = aCoef n * R n - bCoef n * R (n - 1) := by
  have hsum : ∑ m ∈ Finset.range (n + 2),
      (((n + 1 : ℤ) ^ 3) * F (n + 1) m - aCoef n * F n m + bCoef n * F (n - 1) m) =
      G n (n + 2) - G n 0 := by
    calc ∑ m ∈ Finset.range (n + 2),
          (((n + 1 : ℤ) ^ 3) * F (n + 1) m - aCoef n * F n m + bCoef n * F (n - 1) m)
        = ∑ m ∈ Finset.range (n + 2), (G n (m + 1) - G n m) :=
          Finset.sum_congr rfl fun m _ => F_telescope n m hn
      _ = G n (n + 2) - G n 0 := Finset.sum_range_sub (G n) (n + 2)
  have hG0 : G n 0 = 0 := by simp [G]
  have hGtop : G n (n + 2) = 0 := by simp [G, F]
  rw [hG0, hGtop, sub_zero] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hR1 : ∑ m ∈ Finset.range (n + 2), F (n + 1) m = R (n + 1) := rfl
  have hR0 : ∑ m ∈ Finset.range (n + 2), F n m = R n := by
    rw [Finset.sum_range_succ]
    have : F n (n + 1) = 0 := by simp [F]
    rw [this, add_zero]; rfl
  have hRm1 : ∑ m ∈ Finset.range (n + 2), F (n - 1) m = R (n - 1) := by
    have h1 : n + 2 = (n - 1 + 1) + 2 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ]
    have ha : F (n - 1) (n - 1 + 1) = 0 := by simp [F]
    have hb : F (n - 1) (n - 1 + 1 + 1) = 0 := by simp [F]
    rw [ha, hb, add_zero, add_zero]; rfl
  rw [hR1, hR0, hRm1] at hsum
  linarith

private lemma S_eq_R (n : ℕ) : S n = R n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | k + 2 =>
      have hk1 : 1 ≤ k + 1 := by omega
      have hS := S_rec (k + 1) hk1
      have hR := R_rec (k + 1) hk1
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have hsub : k + 1 - 1 = k := by omega
      rw [hsub] at hS hR
      have heq : ((k + 1 + 1 : ℤ) ^ 3) * S (k + 2) = ((k + 1 + 1 : ℤ) ^ 3) * R (k + 2) := by
        have : k + 1 + 1 = k + 2 := by omega
        push_cast at hS hR ⊢
        rw [hS, hR, h1, h0]
      exact mul_left_cancel₀ (by positivity : ((k + 1 + 1 : ℤ) ^ 3) ≠ 0) heq

/- ### Part 2: Floor inequalities and termwise integrality -/

private lemma floor_ineq (q m r : ℕ) (hq : 2 ≤ q) (hrm : r ≤ m) :
    3 * m / q + 2 * (m / q) + r / q + (m - r) / q + 3 * (m + r) / q ≤
    6 * m / q + (m + r) / q + 2 * (m + r) / q := by
  set u := m / q
  set a := m % q
  set v := r / q
  set b := r % q
  have hm : m = q * u + a := (Nat.div_add_mod m q).symm
  have hr : r = q * v + b := (Nat.div_add_mod r q).symm
  have ha : a < q := Nat.mod_lt m (by omega)
  have hb : b < q := Nat.mod_lt r (by omega)
  have h3m : 3 * m / q = 3 * u + 3 * a / q := by
    have : 3 * m = q * (3 * u) + 3 * a := by rw [hm]; ring
    rw [this, Nat.mul_add_div (by omega)]
  have h6m : 6 * m / q = 6 * u + 6 * a / q := by
    have : 6 * m = q * (6 * u) + 6 * a := by rw [hm]; ring
    rw [this, Nat.mul_add_div (by omega)]
  have hmr1 : (m + r) / q = u + v + (a + b) / q := by
    have : m + r = q * (u + v) + (a + b) := by rw [hm, hr]; ring
    rw [this, Nat.mul_add_div (by omega)]
  have hmr2 : 2 * (m + r) / q = 2 * (u + v) + 2 * (a + b) / q := by
    have : 2 * (m + r) = q * (2 * (u + v)) + 2 * (a + b) := by rw [hm, hr]; ring
    rw [this, Nat.mul_add_div (by omega)]
  have hmr3 : 3 * (m + r) / q = 3 * (u + v) + 3 * (a + b) / q := by
    have : 3 * (m + r) = q * (3 * (u + v)) + 3 * (a + b) := by rw [hm, hr]; ring
    rw [this, Nat.mul_add_div (by omega)]
  have hsub : (m - r) / q + (if a < b then 1 else 0) = u - v := by
    by_cases hab : a < b
    · have huv : v + 1 ≤ u := by nlinarith
      have hdiff : m - r = q * (u - v - 1) + (q + a - b) := by
        have h1 : q * (u - v - 1) + q = q * (u - v) := by
          have : u - v - 1 + 1 = u - v := by omega
          calc q * (u - v - 1) + q = q * (u - v - 1 + 1) := by ring
            _ = q * (u - v) := by rw [this]
        have h2 : q * (u - v) + q * v = q * u := by
          rw [← mul_add, Nat.sub_add_cancel (by omega)]
        omega
      rw [if_pos hab, hdiff, Nat.mul_add_div (by omega)]
      have hdiv0 : (q + a - b) / q = 0 := Nat.div_eq_of_lt (by omega)
      omega
    · have huv : v ≤ u := by nlinarith
      have hdiff : m - r = q * (u - v) + (a - b) := by
        have h2 : q * (u - v) + q * v = q * u := by
          rw [← mul_add, Nat.sub_add_cancel huv]
        omega
      rw [if_neg hab, add_zero, hdiff, Nat.mul_add_div (by omega)]
      have hdiv0 : (a - b) / q = 0 := Nat.div_eq_of_lt (by omega)
      omega
  have huv : v ≤ u := by nlinarith
  -- Introduce bounded quotients for omega
  set q6 := 6 * a / q; have hq6 := Nat.div_add_mod (6 * a) q; have hq6m := Nat.mod_lt (6 * a) (by omega : 0 < q)
  set q3 := 3 * a / q; have hq3 := Nat.div_add_mod (3 * a) q; have hq3m := Nat.mod_lt (3 * a) (by omega : 0 < q)
  set q1 := (a + b) / q; have hq1 := Nat.div_add_mod (a + b) q; have hq1m := Nat.mod_lt (a + b) (by omega : 0 < q)
  set q2 := 2 * (a + b) / q; have hq2 := Nat.div_add_mod (2 * (a + b)) q; have hq2m := Nat.mod_lt (2 * (a + b)) (by omega : 0 < q)
  set qab3 := 3 * (a + b) / q; have hqab3 := Nat.div_add_mod (3 * (a + b)) q; have hqab3m := Nat.mod_lt (3 * (a + b)) (by omega : 0 < q)
  have hq6_bnd : q6 ≤ 5 := by
    have : 6 * a / q < 6 := Nat.div_lt_of_lt_mul (by omega)
    omega
  have hq3_bnd : q3 ≤ 2 := by
    have : 3 * a / q < 3 := Nat.div_lt_of_lt_mul (by omega)
    omega
  have hq1_bnd : q1 ≤ 1 := by
    have : (a + b) / q < 2 := Nat.div_lt_of_lt_mul (by omega)
    omega
  have hq2_bnd : q2 ≤ 3 := by
    have : 2 * (a + b) / q < 4 := Nat.div_lt_of_lt_mul (by omega)
    omega
  have hqab3_bnd : qab3 ≤ 5 := by
    have : 3 * (a + b) / q < 6 := Nat.div_lt_of_lt_mul (by omega)
    omega
  -- Reduce to pure linear inequality on a, b, q with bounded integer quotients!
  suffices hred : q3 + qab3 ≤ q6 + q1 + q2 + (if a < b then 1 else 0) by
    have : m / q = u := rfl
    have : r / q = v := rfl
    omega
  -- Check by splitting on the small values of q6, q3, q1, q2, qab3!
  have hq3_2 : 2 * q3 ≤ q6 ∧ q6 ≤ 2 * q3 + 1 := by
    have h2 : 3 * a = q * q3 + (3 * a) % q := hq3.symm
    have h3 : 6 * a = q * (2 * q3) + 2 * ((3 * a) % q) := by
      calc 6 * a = 2 * (3 * a) := by ring
        _ = 2 * (q * q3 + (3 * a) % q) := congrArg (2 * ·) h2
        _ = q * (2 * q3) + 2 * ((3 * a) % q) := by ring
    have h4 : q6 = 2 * q3 + (2 * ((3 * a) % q)) / q := by
      show 6 * a / q = _
      rw [h3, Nat.mul_add_div (by omega)]
    have h5 : (2 * ((3 * a) % q)) / q ≤ 1 := by
      have : 2 * ((3 * a) % q) / q < 2 := Nat.div_lt_of_lt_mul (by omega)
      omega
    exact ⟨by rw [h4]; exact Nat.le_add_right _ _, by rw [h4]; exact Nat.add_le_add_left h5 _⟩
  have hqab3_le : qab3 ≤ q1 + q2 + 1 := by
    have hle : q * qab3 ≤ 3 * (a + b) := Nat.mul_div_le (3 * (a + b)) q
    have h1 : a + b < q * (q1 + 1) := by
      rw [mul_add q q1 1, mul_one]
      have : q * q1 + (a + b) % q = a + b := hq1
      omega
    have h2 : 2 * (a + b) < q * (q2 + 1) := by
      rw [mul_add q q2 1, mul_one]
      have : q * q2 + 2 * (a + b) % q = 2 * (a + b) := hq2
      omega
    have hlt : q * qab3 < q * (q1 + q2 + 2) := by
      calc q * qab3 ≤ 3 * (a + b) := hle
        _ = (a + b) + 2 * (a + b) := by ring
        _ < q * (q1 + 1) + q * (q2 + 1) := by omega
        _ = q * (q1 + q2 + 2) := by ring
    have : qab3 < q1 + q2 + 2 := Nat.lt_of_mul_lt_mul_left hlt
    omega
  by_cases hab : a < b
  · rw [if_pos hab]
    linarith
  · rw [if_neg hab]
    have hqab3_le_q6 : qab3 ≤ q6 := Nat.div_le_div_right (by omega : 3 * (a + b) ≤ 6 * a)
    by_cases hq3_lt : q3 + 1 ≤ q6
    · linarith
    · have hq6_0 : q6 = 0 := by linarith
      have hq3_0 : q3 = 0 := by linarith
      have hqab3_0 : qab3 = 0 := by linarith
      linarith

private lemma floor_ineq_odd_dvd (q m r : ℕ) (hq : 5 ≤ q) (hq_odd : q % 2 = 1) (hrm : r ≤ m)
    (hdvd : q ∣ 2 * (m + r) - 1) (hpos : 1 ≤ m + r) :
    1 + 3 * m / q + 2 * (m / q) + r / q + (m - r) / q + 3 * (m + r) / q ≤
    6 * m / q + (m + r) / q + 2 * (m + r) / q := by
  set u := m / q
  set a := m % q
  set v := r / q
  set b := r % q
  have hm : m = q * u + a := (Nat.div_add_mod m q).symm
  have hr : r = q * v + b := (Nat.div_add_mod r q).symm
  have ha : a < q := Nat.mod_lt m (by omega)
  have hb : b < q := Nat.mod_lt r (by omega)
  have h3m : 3 * m / q = 3 * u + 3 * a / q := by
    have : 3 * m = q * (3 * u) + 3 * a := by rw [hm]; ring
    rw [this, Nat.mul_add_div (by omega)]
  have h6m : 6 * m / q = 6 * u + 6 * a / q := by
    have : 6 * m = q * (6 * u) + 6 * a := by rw [hm]; ring
    rw [this, Nat.mul_add_div (by omega)]
  have hmr1 : (m + r) / q = u + v + (a + b) / q := by
    have : m + r = q * (u + v) + (a + b) := by rw [hm, hr]; ring
    rw [this, Nat.mul_add_div (by omega)]
  have hmr2 : 2 * (m + r) / q = 2 * (u + v) + 2 * (a + b) / q := by
    have : 2 * (m + r) = q * (2 * (u + v)) + 2 * (a + b) := by rw [hm, hr]; ring
    rw [this, Nat.mul_add_div (by omega)]
  have hmr3 : 3 * (m + r) / q = 3 * (u + v) + 3 * (a + b) / q := by
    have : 3 * (m + r) = q * (3 * (u + v)) + 3 * (a + b) := by rw [hm, hr]; ring
    rw [this, Nat.mul_add_div (by omega)]
  have huv : v ≤ u := by nlinarith
  have hsub : (m - r) / q + (if a < b then 1 else 0) = u - v := by
    by_cases hab : a < b
    · have huv1 : v + 1 ≤ u := by nlinarith
      have hdiff : m - r = q * (u - v - 1) + (q + a - b) := by
        have h1 : q * (u - v - 1) + q = q * (u - v) := by
          have : u - v - 1 + 1 = u - v := by omega
          calc q * (u - v - 1) + q = q * (u - v - 1 + 1) := by ring
            _ = q * (u - v) := by rw [this]
        have h2 : q * (u - v) + q * v = q * u := by
          rw [← mul_add, Nat.sub_add_cancel huv]
        omega
      rw [if_pos hab, hdiff, Nat.mul_add_div (by omega)]
      have hdiv0 : (q + a - b) / q = 0 := Nat.div_eq_of_lt (by omega)
      omega
    · have hdiff : m - r = q * (u - v) + (a - b) := by
        have h2 : q * (u - v) + q * v = q * u := by
          rw [← mul_add, Nat.sub_add_cancel huv]
        omega
      rw [if_neg hab, add_zero, hdiff, Nat.mul_add_div (by omega)]
      have hdiv0 : (a - b) / q = 0 := Nat.div_eq_of_lt (by omega)
      omega
  -- From q ∣ 2(m+r) - 1, we get 2(a + b) ≡ 1 (mod q), so a + b = (q + 1)/2 or (3q + 1)/2!
  have hab_cases : 2 * (a + b) = q + 1 ∨ 2 * (a + b) = 3 * q + 1 := by
    have ⟨t, ht⟩ := hdvd
    have h2ab : 2 * (a + b) < 4 * q := by omega
    have h2mr_eq : 2 * (m + r) = q * (2 * (u + v)) + 2 * (a + b) := by rw [hm, hr]; ring
    have hpos_ab : 1 ≤ 2 * (a + b) := by
      by_contra h0
      have hab0 : 2 * (a + b) = 0 := by omega
      have h2mr : 2 * (m + r) = q * (2 * (u + v)) := by omega
      have h1dvd : q ∣ 1 := by
        have := (Nat.dvd_add_right hdvd).mp (show q ∣ (2 * (m + r) - 1) + 1 by
          rw [Nat.sub_add_cancel (by omega)]; exact ⟨2 * (u + v), h2mr⟩)
        exact this
      have := Nat.le_of_dvd one_pos h1dvd
      omega
    have hdiv_ab : q ∣ 2 * (a + b) - 1 := by
      have h1 : 2 * (m + r) - 1 = q * (2 * (u + v)) + (2 * (a + b) - 1) := by omega
      refine ⟨t - 2 * (u + v), ?_⟩
      have hle_mul : q * (2 * (u + v)) ≤ q * t := by omega
      have hle : 2 * (u + v) ≤ t := Nat.le_of_mul_le_mul_left hle_mul (by omega)
      have hm_sub : q * (t - 2 * (u + v)) + q * (2 * (u + v)) = q * t := by
        rw [← mul_add, Nat.sub_add_cancel hle]
      omega
    obtain ⟨k, hk⟩ := hdiv_ab
    have hk_lt : k ≤ 3 := by
      by_contra h
      have h4 : 4 ≤ k := by omega
      have h4q : q * 4 ≤ q * k := Nat.mul_le_mul_left q h4
      omega
    have hk_odd : k % 2 = 1 := by
      have h1 : (q * k) % 2 = 1 := by rw [← hk]; omega
      rw [Nat.mul_mod, hq_odd] at h1
      omega
    have hk_cases : k = 1 ∨ k = 3 := by omega
    rcases hk_cases with rfl | rfl <;> omega
  set q6 := 6 * a / q
  set q3 := 3 * a / q
  set q1 := (a + b) / q
  set q2 := 2 * (a + b) / q
  set qab3 := 3 * (a + b) / q
  suffices hred : 1 + q3 + qab3 ≤ q6 + q1 + q2 + (if a < b then 1 else 0) by
    have : m / q = u := rfl
    have : r / q = v := rfl
    omega
  have hq3_le_q6 : q3 ≤ q6 := Nat.div_le_div_right (by omega : 3 * a ≤ 6 * a)
  rcases hab_cases with hab1 | hab3
  · -- Case 2(a + b) = q + 1: q1 = 0, q2 = 1, qab3 = 1
    have hq1_0 : q1 = 0 := Nat.div_eq_of_lt (by omega)
    have hq2_1 : q2 = 1 := by
      have : 2 * (a + b) = q * 1 + 1 := by omega
      show 2 * (a + b) / q = 1
      rw [this, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
    have hqab3_1 : qab3 = 1 := by
      have : 3 * (a + b) = q * 1 + (3 * (a + b) - q) := by omega
      show 3 * (a + b) / q = 1
      rw [this, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
    rw [hq1_0, hq2_1, hqab3_1]
    by_cases hab : a < b
    · rw [if_pos hab]; omega
    · rw [if_neg hab]
      have hq3_le1 : q3 ≤ 1 := by
        have : 3 * a / q < 2 := Nat.div_lt_of_lt_mul (by omega)
        omega
      have hq6_ge : q3 + 1 ≤ q6 := by
        by_cases h0 : q3 = 0
        · have hge1 : 1 ≤ 6 * a / q := Nat.le_div_iff_mul_le (by omega) |>.mpr (by omega)
          rw [h0]; exact hge1
        · have h1 : q3 = 1 := le_antisymm hq3_le1 (Nat.pos_of_ne_zero h0)
          have h3a : q ≤ 3 * a := by
            have := Nat.mul_div_le (3 * a) q
            change q * q3 ≤ 3 * a at this
            rw [h1, mul_one] at this
            exact this
          have hge2 : 2 ≤ 6 * a / q := Nat.le_div_iff_mul_le (by omega) |>.mpr (by omega)
          rw [h1]; exact hge2
      omega
  · -- Case 2(a + b) = 3q + 1: q1 = 1, q2 = 3, qab3 = 4
    have hq1_1 : q1 = 1 := by
      have : a + b = q * 1 + (a + b - q) := by omega
      show (a + b) / q = 1
      rw [this, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
    have hq2_3 : q2 = 3 := by
      have : 2 * (a + b) = q * 3 + 1 := by omega
      show 2 * (a + b) / q = 3
      rw [this, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
    have hqab3_4 : qab3 = 4 := by
      have : 3 * (a + b) = q * 4 + (3 * (a + b) - 4 * q) := by omega
      show 3 * (a + b) / q = 4
      rw [this, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
    rw [hq1_1, hq2_3, hqab3_4]
    by_cases hab : a < b
    · rw [if_pos hab]; omega
    · rw [if_neg hab]
      have hq3_le2 : q3 ≤ 2 := by
        have : 3 * a / q < 3 := Nat.div_lt_of_lt_mul (by omega)
        omega
      have hq6_ge4 : 4 ≤ q6 := Nat.le_div_iff_mul_le (by omega) |>.mpr (by omega)
      omega

private lemma padicValNat_eq_sum_pow_dvd {p y b : ℕ} [hp : Fact p.Prime] (hy : 0 < y)
    (hb : Nat.log p y < b) :
    padicValNat p y = ∑ k ∈ Finset.Ico 1 b, if p ^ k ∣ y then 1 else 0 := by
  set v := padicValNat p y
  have hv_lt : v < b := by
    have hle : p ^ v ≤ y := Nat.le_of_dvd hy pow_padicValNat_dvd
    have hlog : v ≤ Nat.log p y := Nat.le_log_of_pow_le hp.out.one_lt hle
    omega
  have hiff : ∀ k, p ^ k ∣ y ↔ k ≤ v := fun k => padicValNat_dvd_iff_le hy.ne'
  calc v = (Finset.Ico 1 (v + 1)).card := by simp
    _ = ∑ _k ∈ Finset.Ico 1 (v + 1), (1 : ℕ) := by simp
    _ = ∑ k ∈ Finset.Ico 1 b, if k ≤ v then 1 else 0 := by
        rw [← Finset.sum_filter]
        have hfilt : (Finset.Ico 1 b).filter (· ≤ v) = Finset.Ico 1 (v + 1) := by
          ext k; simp only [mem_filter, mem_Ico]; omega
        rw [hfilt]
    _ = ∑ k ∈ Finset.Ico 1 b, if p ^ k ∣ y then 1 else 0 := by
        refine Finset.sum_congr rfl fun k _ => by simp [hiff k]

private lemma term_dvd (n m : ℕ) (hn : 1 ≤ n) :
    (((2 * n - 1) * (3 * n).choose n : ℕ) : ℤ) ∣ F n m := by
  by_cases hmn : m ≤ n
  · set r := n - m
    by_cases hrm : r ≤ m
    · have hnmr : n = m + r := by omega
      have hF : F n m = ((T m * (2 * m).choose m * m.choose r * 432 ^ r : ℕ) : ℤ) * (-1 : ℤ) ^ r := by
        simp only [F, hmn, ite_true, r]
        have h432 : (-432 : ℤ) ^ (n - m) = ((432 ^ (n - m) : ℕ) : ℤ) * (-1 : ℤ) ^ (n - m) := by
          rw [show (-432 : ℤ) = (432 : ℤ) * (-1 : ℤ) by ring, mul_pow]
          push_cast; rfl
        rw [h432]
        push_cast; ring
      rw [hF]
      refine dvd_mul_of_dvd_left ?_ _
      exact_mod_cast (show (2 * n - 1) * (3 * n).choose n ∣
          T m * (2 * m).choose m * m.choose r * 432 ^ r by
        set D := (2 * n - 1) * (3 * n).choose n
        set N := T m * (2 * m).choose m * m.choose r * 432 ^ r
        have hD_pos : 0 < D :=
          mul_pos (by omega) (Nat.choose_pos (by omega))
        have hN_pos : 0 < N := by
          have hT : 0 < T m := mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
          exact mul_pos (mul_pos (mul_pos hT (Nat.choose_pos (by omega))) (Nat.choose_pos hrm))
            (pow_pos (by norm_num) r)
        rw [← Nat.factorization_le_iff_dvd hD_pos.ne' hN_pos.ne']
        intro p
        by_cases hpp : p.Prime
        · have : Fact p.Prime := ⟨hpp⟩
          rw [Nat.factorization_def _ hpp, Nat.factorization_def _ hpp]
          -- Relate N and D to factorials
          have hN_fac : N * ((3 * m).factorial * m.factorial * m.factorial * r.factorial * (m - r).factorial) =
              (6 * m).factorial * 432 ^ r := by
            have hT := T_mul_factorials m
            have hC2 : (2 * m).choose m * m.factorial * m.factorial = (2 * m).factorial := by
              have := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
              simpa [show 2 * m - m = m by omega] using this
            have hCr : m.choose r * r.factorial * (m - r).factorial = m.factorial :=
              Nat.choose_mul_factorial_mul_factorial hrm
            calc N * ((3 * m).factorial * m.factorial * m.factorial * r.factorial * (m - r).factorial)
                = (T m * ((3 * m).factorial * (2 * m).factorial * m.factorial)) * 432 ^ r := by
                  have : (2 * m).choose m * m.factorial * m.factorial = (2 * m).factorial := hC2
                  calc N * ((3 * m).factorial * m.factorial * m.factorial * r.factorial * (m - r).factorial)
                      = T m * (3 * m).factorial * ((2 * m).choose m * m.factorial * m.factorial) *
                        (m.choose r * r.factorial * (m - r).factorial) * 432 ^ r := by simp only [N]; ring
                    _ = T m * (3 * m).factorial * (2 * m).factorial * m.factorial * 432 ^ r := by
                        rw [hC2, hCr]
                    _ = (T m * ((3 * m).factorial * (2 * m).factorial * m.factorial)) * 432 ^ r := by ring
              _ = (6 * m).factorial * 432 ^ r := by rw [hT]
          have hD_fac : D * (n.factorial * (2 * n).factorial) = (2 * n - 1) * (3 * n).factorial := by
            have hC3 : (3 * n).choose n * n.factorial * (2 * n).factorial = (3 * n).factorial := by
              have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
              simpa [show 3 * n - n = 2 * n by omega] using this
            calc D * (n.factorial * (2 * n).factorial)
                = (2 * n - 1) * ((3 * n).choose n * n.factorial * (2 * n).factorial) := by
                  simp only [D]; ring
              _ = (2 * n - 1) * (3 * n).factorial := by rw [hC3]
          have hvN : padicValNat p N + padicValNat p (3 * m).factorial + 2 * padicValNat p m.factorial +
              padicValNat p r.factorial + padicValNat p (m - r).factorial =
              padicValNat p (6 * m).factorial + r * padicValNat p 432 := by
            have h := congrArg (padicValNat p) hN_fac
            simp only [padicValNat.mul, padicValNat.pow, hN_pos.ne', Nat.factorial_ne_zero,
              mul_ne_zero_iff, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
              not_false_eq_true, and_self] at h
            omega
          have hvD : padicValNat p D + padicValNat p n.factorial + padicValNat p (2 * n).factorial =
              padicValNat p (2 * n - 1) + padicValNat p (3 * n).factorial := by
            have h := congrArg (padicValNat p) hD_fac
            have h2n1_ne : 2 * n - 1 ≠ 0 := by omega
            simp only [padicValNat.mul, hD_pos.ne', h2n1_ne, Nat.factorial_ne_zero,
              mul_ne_zero_iff, ne_eq, not_false_eq_true, and_self] at h
            omega
          -- Choose common upper bound b for Legendre's formula
          set b := Nat.log p (6 * m) + Nat.log p (3 * n) + 2
          have hb6m : Nat.log p (6 * m) < b := by omega
          have hb3m : Nat.log p (3 * m) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6m
          have hbm : Nat.log p m < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6m
          have hbr : Nat.log p r < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6m
          have hbmr : Nat.log p (m - r) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6m
          have hb3n : Nat.log p (3 * n) < b := by omega
          have hb2n : Nat.log p (2 * n) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb3n
          have hbn : Nat.log p n < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb3n
          have hb2n1 : Nat.log p (2 * n - 1) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb3n
          rw [padicValNat_factorial hb6m, padicValNat_factorial hb3m, padicValNat_factorial hbm,
            padicValNat_factorial hbr, padicValNat_factorial hbmr] at hvN
          rw [padicValNat_factorial hb3n, padicValNat_factorial hb2n, padicValNat_factorial hbn,
            padicValNat_eq_sum_pow_dvd (by omega) hb2n1] at hvD
          suffices hineq :
              (∑ k ∈ Finset.Ico 1 b, if p ^ k ∣ 2 * n - 1 then 1 else 0) +
              (∑ k ∈ Finset.Ico 1 b, 3 * n / p ^ k) +
              (∑ k ∈ Finset.Ico 1 b, 3 * m / p ^ k) +
              2 * (∑ k ∈ Finset.Ico 1 b, m / p ^ k) +
              (∑ k ∈ Finset.Ico 1 b, r / p ^ k) +
              (∑ k ∈ Finset.Ico 1 b, (m - r) / p ^ k) ≤
              (∑ k ∈ Finset.Ico 1 b, 6 * m / p ^ k) +
              (∑ k ∈ Finset.Ico 1 b, n / p ^ k) +
              (∑ k ∈ Finset.Ico 1 b, 2 * n / p ^ k) +
              r * padicValNat p 432 by omega
          rw [Finset.mul_sum]
          simp only [← Finset.sum_add_distrib]
          -- Case split on p = 2, p = 3, p ≥ 5
          by_cases hp2 : p = 2
          · subst hp2
            have hterm : ∀ k ∈ Finset.Ico 1 b,
                (if 2 ^ k ∣ 2 * n - 1 then 1 else 0) + 3 * n / 2 ^ k + 3 * m / 2 ^ k +
                2 * (m / 2 ^ k) + r / 2 ^ k + (m - r) / 2 ^ k ≤
                6 * m / 2 ^ k + n / 2 ^ k + 2 * n / 2 ^ k := by
              intro k hk
              simp only [mem_Ico] at hk
              have hnot : ¬ 2 ^ k ∣ 2 * n - 1 := by
                intro hd
                have h2d : 2 ∣ 2 * n - 1 := dvd_trans (dvd_pow_self 2 (by omega)) hd
                omega
              rw [if_neg hnot, zero_add, hnmr]
              have hq : 2 ≤ 2 ^ k := by
                calc 2 = 2 ^ 1 := (pow_one 2).symm
                  _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
              have := floor_ineq (2 ^ k) m r hq hrm
              omega
            exact (Finset.sum_le_sum hterm).trans (Nat.le_add_right _ _)
          · by_cases hp3 : p = 3
            · subst hp3
              have hv3 : padicValNat 3 432 = 3 := by
                have h432 : (432 : ℕ) = 3 ^ 3 * 16 := by norm_num
                rw [h432, padicValNat.mul (by norm_num) (by norm_num),
                  padicValNat.prime_pow 3]
                have h16 : padicValNat 3 16 = 0 :=
                  padicValNat.eq_zero_of_not_dvd (by decide)
                omega
              -- Split k = 1 from k ≥ 2
              have h1_in : 1 ∈ Finset.Ico 1 b := by simp only [mem_Ico]; omega
              have hrest : ∀ k ∈ (Finset.Ico 1 b).erase 1,
                  (if 3 ^ k ∣ 2 * n - 1 then 1 else 0) + 3 * n / 3 ^ k + 3 * m / 3 ^ k +
                  2 * (m / 3 ^ k) + r / 3 ^ k + (m - r) / 3 ^ k ≤
                  6 * m / 3 ^ k + n / 3 ^ k + 2 * n / 3 ^ k := by
                intro k hk
                simp only [mem_erase, mem_Ico] at hk
                have hk2 : 2 ≤ k := by omega
                have hq5 : 5 ≤ 3 ^ k := by
                  calc 5 ≤ 3 ^ 2 := by norm_num
                    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
                have hq_odd : 3 ^ k % 2 = 1 := by
                  have : Odd (3 ^ k) := Odd.pow (by decide)
                  exact Nat.odd_iff.mp this
                rw [hnmr]
                by_cases hd : 3 ^ k ∣ 2 * (m + r) - 1
                · rw [if_pos hd]
                  have := floor_ineq_odd_dvd (3 ^ k) m r hq5 hq_odd hrm hd (by omega)
                  omega
                · rw [if_neg hd, zero_add]
                  have := floor_ineq (3 ^ k) m r (by omega) hrm
                  omega
              have hk1 :
                  (if 3 ^ 1 ∣ 2 * n - 1 then 1 else 0) + 3 * n / 3 ^ 1 + 3 * m / 3 ^ 1 +
                  2 * (m / 3 ^ 1) + r / 3 ^ 1 + (m - r) / 3 ^ 1 ≤
                  6 * m / 3 ^ 1 + n / 3 ^ 1 + 2 * n / 3 ^ 1 + r * padicValNat 3 432 := by
                rw [hv3, pow_one, hnmr]
                by_cases hr0 : r = 0
                · rw [hr0]
                  simp only [add_zero, Nat.sub_zero, Nat.zero_div, zero_mul]
                  by_cases hd : 3 ∣ 2 * m - 1
                  · rw [if_pos hd]; omega
                  · rw [if_neg hd]; omega
                · have hr1 : 1 ≤ r := by omega
                  have := floor_ineq 3 m r (by norm_num) hrm
                  split_ifs <;> omega
              rw [← Finset.add_sum_erase _ _ h1_in, ← Finset.add_sum_erase _ _ h1_in]
              have hsum_rest := Finset.sum_le_sum hrest
              omega
            · -- p ≥ 5: every q = p^k ≥ 5 is odd!
              have hp5 : 5 ≤ p := by
                have := hpp.two_le
                have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hp2
                omega
              have hterm : ∀ k ∈ Finset.Ico 1 b,
                  (if p ^ k ∣ 2 * n - 1 then 1 else 0) + 3 * n / p ^ k + 3 * m / p ^ k +
                  2 * (m / p ^ k) + r / p ^ k + (m - r) / p ^ k ≤
                  6 * m / p ^ k + n / p ^ k + 2 * n / p ^ k := by
                intro k hk
                simp only [mem_Ico] at hk
                have hq5 : 5 ≤ p ^ k := by
                  calc 5 ≤ p := hp5
                    _ = p ^ 1 := (pow_one p).symm
                    _ ≤ p ^ k := Nat.pow_le_pow_right hpp.pos hk.1
                have hq_odd : p ^ k % 2 = 1 := by
                  have hp_odd : Odd p := Nat.odd_iff.mpr (hpp.eq_two_or_odd.resolve_left hp2)
                  exact Nat.odd_iff.mp (Odd.pow hp_odd)
                rw [hnmr]
                by_cases hd : p ^ k ∣ 2 * (m + r) - 1
                · rw [if_pos hd]
                  have := floor_ineq_odd_dvd (p ^ k) m r hq5 hq_odd hrm hd (by omega)
                  omega
                · rw [if_neg hd, zero_add]
                  have := floor_ineq (p ^ k) m r (by omega) hrm
                  omega
              exact (Finset.sum_le_sum hterm).trans (Nat.le_add_right _ _)
        · simp [Nat.factorization_eq_zero_of_not_prime _ hpp])
    · have hc : m.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [F, hmn, r, hc]
  · simp [F, hmn]

private lemma S_dvd_den (n : ℕ) (hn : 1 ≤ n) :
    (((2 * n - 1) * (3 * n).choose n : ℕ) : ℤ) ∣ S n := by
  rw [S_eq_R]
  unfold R
  exact Finset.dvd_sum fun m _ => term_dvd n m hn

/- ### Part 3: Exact 2-adic valuation and proof of OeisA189286.conjecture_3 -/

private def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

private lemma padicValNat_two_fac (n : ℕ) : padicValNat 2 n.factorial = n - s2 n := by
  have := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [s2] using this

private lemma s2_le_self (n : ℕ) : s2 n ≤ n := by
  exact Nat.digit_sum_le 2 n

private lemma s2_add_le (a b : ℕ) : s2 (a + b) ≤ s2 a + s2 b := by
  have h1 : padicValNat 2 (a + b).factorial = a + b - s2 (a + b) := padicValNat_two_fac (a + b)
  have h2 : padicValNat 2 a.factorial = a - s2 a := padicValNat_two_fac a
  have h3 : padicValNat 2 b.factorial = b - s2 b := padicValNat_two_fac b
  have hcho : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
    simpa [Nat.add_sub_cancel_left] using this
  have hval := congrArg (padicValNat 2) hcho
  have hc_pos : 0 < (a + b).choose a := Nat.choose_pos (by omega)
  simp only [padicValNat.mul, hc_pos.ne', Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self] at hval
  have ha := s2_le_self a
  have hb := s2_le_self b
  have hab := s2_le_self (a + b)
  omega

private lemma s2_mul_two (n : ℕ) : s2 (2 * n) = s2 n := by
  by_cases hn : n = 0
  · subst hn; simp [s2]
  · unfold s2
    rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * n)]
    have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n) / 2 = n := by omega
    simp [h1, h2]

private lemma s2_pow_two (k : ℕ) : s2 (2 ^ k) = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ', s2_mul_two, ih]

private lemma s2_eq_zero_iff (n : ℕ) : s2 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hne
    have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hne
    have hpos : 0 < (Nat.digits 2 n).sum := by
      have hlast : (Nat.digits 2 n).getLast hnil ≠ 0 := Nat.getLast_digit_ne_zero 2 hne
      have hmem : (Nat.digits 2 n).getLast hnil ∈ Nat.digits 2 n := List.getLast_mem hnil
      exact List.sum_pos_iff_exists_pos_nat.mpr ⟨_, hmem, Nat.pos_of_ne_zero hlast⟩
    unfold s2 at h
    omega
  · rintro rfl; simp [s2]

private lemma s2_eq_one_iff (n : ℕ) : s2 n = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  constructor
  · induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hs1
      have hn0 : n ≠ 0 := fun h => by subst h; simp [s2] at hs1
      have hdef : Nat.digits 2 n = n % 2 :: Nat.digits 2 (n / 2) :=
        Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hn0)
      unfold s2 at hs1
      rw [hdef, List.sum_cons] at hs1
      by_cases hpar : n % 2 = 0
      · have hhalf : s2 (n / 2) = 1 := by unfold s2; omega
        obtain ⟨k, hk⟩ := ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by norm_num)) hhalf
        refine ⟨k + 1, ?_⟩
        rw [pow_succ']
        omega
      · have hmod1 : n % 2 = 1 := by omega
        have hhalf0 : s2 (n / 2) = 0 := by unfold s2; omega
        have hdiv0 : n / 2 = 0 := (s2_eq_zero_iff _).mp hhalf0
        refine ⟨0, ?_⟩
        omega
  · rintro ⟨k, rfl⟩
    exact s2_pow_two k

private lemma s2_three_mul_ge_two {n : ℕ} (hn : 0 < n) : 2 ≤ s2 (3 * n) := by
  by_contra hlt
  have hcases : s2 (3 * n) = 0 ∨ s2 (3 * n) = 1 := by omega
  rcases hcases with h0 | h1
  · have := (s2_eq_zero_iff (3 * n)).mp h0
    omega
  · obtain ⟨k, hk⟩ := (s2_eq_one_iff (3 * n)).mp h1
    have h3dvd : 3 ∣ 2 ^ k := ⟨n, hk.symm⟩
    have h3_dvd_2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h3dvd
    omega

private lemma s2_three_mul_pow_two (k : ℕ) : s2 (3 * 2 ^ k) = 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have : 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by ring
    rw [this, s2_mul_two, ih]

private lemma padicValNat_two_T (k : ℕ) : padicValNat 2 (T k) = 2 * s2 k := by
  have hfac := T_mul_factorials k
  have hT_pos : 0 < T k := mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hv := congrArg (padicValNat 2) hfac
  simp only [padicValNat.mul, hT_pos.ne', Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self, padicValNat_two_fac] at hv
  have h6 : s2 (6 * k) = s2 (3 * k) := by rw [show 6 * k = 2 * (3 * k) by ring, s2_mul_two]
  have h2 : s2 (2 * k) = s2 k := s2_mul_two k
  have hle6 := s2_le_self (6 * k)
  have hle3 := s2_le_self (3 * k)
  have hle2 := s2_le_self (2 * k)
  have hle1 := s2_le_self k
  omega

private lemma padicValNat_two_central (k : ℕ) : padicValNat 2 ((2 * k).choose k) = s2 k := by
  have hfac : (2 * k).choose k * k.factorial * k.factorial = (2 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    simpa [show 2 * k - k = k by omega] using this
  have hc_pos : 0 < (2 * k).choose k := Nat.choose_pos (by omega)
  have hv := congrArg (padicValNat 2) hfac
  simp only [padicValNat.mul, hc_pos.ne', Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self, padicValNat_two_fac, s2_mul_two] at hv
  have hle2 := s2_le_self (2 * k)
  have hle1 := s2_le_self k
  omega

private lemma padicValNat_two_choose3 (n : ℕ) :
    padicValNat 2 ((3 * n).choose n) = 2 * s2 n - s2 (3 * n) := by
  have hfac : (3 * n).choose n * n.factorial * (2 * n).factorial = (3 * n).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
    simpa [show 3 * n - n = 2 * n by omega] using this
  have hc_pos : 0 < (3 * n).choose n := Nat.choose_pos (by omega)
  have hv := congrArg (padicValNat 2) hfac
  simp only [padicValNat.mul, hc_pos.ne', Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self, padicValNat_two_fac, s2_mul_two] at hv
  have hle3 := s2_le_self (3 * n)
  have hle2 := s2_le_self (2 * n)
  have hle1 := s2_le_self n
  omega

private lemma two_pow_dvd_S (n : ℕ) :
    ((2 : ℤ) ^ (3 * s2 n)) ∣ S n ∧ ¬ ((2 : ℤ) ^ (3 * s2 n + 1)) ∣ S n := by
  rw [S_eq_R]
  unfold R
  rw [Finset.sum_range_succ]
  -- Main term F n n = T n * C(2n, n)
  have hmain_eq : F n n = ((T n * (2 * n).choose n : ℕ) : ℤ) := by
    simp [F]
  have hmain_pos : 0 < T n * (2 * n).choose n :=
    mul_pos (mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
      (Nat.choose_pos (by omega))
  have hmain_v2 : padicValNat 2 (T n * (2 * n).choose n) = 3 * s2 n := by
    have hTn_ne : T n ≠ 0 :=
      (mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))).ne'
    have hCn_ne : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
    rw [padicValNat.mul hTn_ne hCn_ne, padicValNat_two_T, padicValNat_two_central]
    ring
  have hmain_dvd : ((2 : ℤ) ^ (3 * s2 n)) ∣ F n n := by
    rw [hmain_eq]
    have hnat : 2 ^ (3 * s2 n) ∣ T n * (2 * n).choose n := by
      rw [← hmain_v2]
      exact pow_padicValNat_dvd
    exact_mod_cast hnat
  have hmain_ndvd : ¬ ((2 : ℤ) ^ (3 * s2 n + 1)) ∣ F n n := by
    rw [hmain_eq]
    intro hd
    have hnat : 2 ^ (3 * s2 n + 1) ∣ T n * (2 * n).choose n := by exact_mod_cast hd
    have hle : 3 * s2 n + 1 ≤ padicValNat 2 (T n * (2 * n).choose n) :=
      (padicValNat_dvd_iff_le hmain_pos.ne').mp hnat
    omega
  -- Every lower term m < n is divisible by 2^(3 * s2 n + 1)
  have hlower_dvd : ((2 : ℤ) ^ (3 * s2 n + 1)) ∣ ∑ m ∈ Finset.range n, F n m := by
    refine Finset.dvd_sum fun m hm => ?_
    simp only [mem_range] at hm
    set r := n - m
    have hr_pos : 1 ≤ r := by omega
    by_cases hrm : r ≤ m
    · have hF_eq : F n m = ((T m * (2 * m).choose m : ℕ) : ℤ) * (m.choose r : ℤ) *
          ((2 : ℤ) ^ (4 * r)) * ((-27 : ℤ) ^ r) := by
        simp only [F, show m ≤ n by omega, ite_true, r]
        have h432 : (-432 : ℤ) ^ (n - m) = (2 : ℤ) ^ (4 * (n - m)) * (-27 : ℤ) ^ (n - m) := by
          rw [show (-432 : ℤ) = (2 : ℤ) ^ 4 * (-27 : ℤ) by ring, mul_pow, ← pow_mul]
        rw [h432]
        push_cast; ring
      rw [hF_eq]
      have hTm_v2 : padicValNat 2 (T m * (2 * m).choose m) = 3 * s2 m := by
        have hTm_ne : T m ≠ 0 :=
          (mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))).ne'
        have hCm_ne : (2 * m).choose m ≠ 0 := (Nat.choose_pos (by omega)).ne'
        rw [padicValNat.mul hTm_ne hCm_ne, padicValNat_two_T, padicValNat_two_central]
        ring
      have hTm_dvd : ((2 : ℤ) ^ (3 * s2 m)) ∣ ((T m * (2 * m).choose m : ℕ) : ℤ) := by
        have : 2 ^ (3 * s2 m) ∣ T m * (2 * m).choose m := by
          rw [← hTm_v2]; exact pow_padicValNat_dvd
        exact_mod_cast this
      have hexp : 3 * s2 n + 1 ≤ 3 * s2 m + 4 * r := by
        have h1 : s2 n ≤ s2 m + s2 r := by
          have : n = m + r := by omega
          rw [this]; exact s2_add_le m r
        have h2 : s2 r ≤ r := s2_le_self r
        omega
      have hdvd_prod : ((2 : ℤ) ^ (3 * s2 m + 4 * r)) ∣
          ((T m * (2 * m).choose m : ℕ) : ℤ) * (m.choose r : ℤ) *
          ((2 : ℤ) ^ (4 * r)) * ((-27 : ℤ) ^ r) := by
        obtain ⟨c, hc⟩ := hTm_dvd
        refine ⟨c * (m.choose r : ℤ) * (-27 : ℤ) ^ r, ?_⟩
        rw [hc, pow_add]
        ring
      exact dvd_trans (pow_dvd_pow (2 : ℤ) hexp) hdvd_prod
    · have hc : m.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [F, show m ≤ n by omega, r, hc]
  constructor
  · exact dvd_add (dvd_trans (pow_dvd_pow (2 : ℤ) (Nat.le_succ _)) hlower_dvd) hmain_dvd
  · intro hsum
    exact hmain_ndvd ((dvd_add_right hlower_dvd).mp hsum)

private lemma main_theorem (n : ℕ) (hn : 0 < n) :
    ∃ m : ℤ, OeisA189286.a n = 8 * m ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k) := by
  set D : ℕ := (2 * n - 1) * (3 * n).choose n
  have hD_pos : 0 < D := mul_pos (by omega) (Nat.choose_pos (by omega))
  obtain ⟨A, hA⟩ := S_dvd_den n hn
  -- Relate OeisA189286.a n to A
  have ha_eq : OeisA189286.a n = (A : ℚ) := by
    unfold OeisA189286.a OeisA189286.tTerm
    have hnum : (∑ k ∈ Finset.range (n + 1),
        (((6 * k).choose (3 * k) * (3 * k).choose k : ℕ) : ℚ) *
        (((6 * (n - k)).choose (3 * (n - k)) * (3 * (n - k)).choose (n - k) : ℕ) : ℚ)) =
        (S n : ℚ) := by
      unfold S T
      push_cast
      rfl
    have hden : ((2 * (n : ℚ) - 1) * ((3 * n).choose n : ℚ)) = (D : ℚ) := by
      simp only [D, Nat.cast_mul]
      have hcast : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        push_cast; rfl
      rw [hcast]
    rw [hnum, hden]
    have hAq : (S n : ℚ) = (D : ℚ) * (A : ℚ) := by exact_mod_cast hA
    rw [hAq, mul_div_cancel_left₀ _ (by exact_mod_cast hD_pos.ne')]
  -- Compute exact 2-adic valuation of D and A
  have h2n1_odd : padicValNat 2 (2 * n - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by omega)
  have hD_v2 : padicValNat 2 D = 2 * s2 n - s2 (3 * n) := by
    simp only [D]
    rw [padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne', h2n1_odd, zero_add,
      padicValNat_two_choose3]
  have hA_ne : A ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hA
    exact (two_pow_dvd_S n).2 (hA ▸ dvd_zero _)
  have hS_natAbs : (S n).natAbs = D * A.natAbs := by
    have := congrArg Int.natAbs hA
    simpa [Int.natAbs_mul] using this
  have hS_v2 : padicValNat 2 (S n).natAbs = 3 * s2 n := by
    have hS_ne : (S n).natAbs ≠ 0 := by
      rw [hS_natAbs]
      exact mul_ne_zero hD_pos.ne' (Int.natAbs_ne_zero.mpr hA_ne)
    have h1 : 2 ^ (3 * s2 n) ∣ (S n).natAbs := by
      obtain ⟨c, hc⟩ := (two_pow_dvd_S n).1
      refine ⟨c.natAbs, ?_⟩
      have := congrArg Int.natAbs hc
      simpa [Int.natAbs_mul] using this
    have h2 : ¬ 2 ^ (3 * s2 n + 1) ∣ (S n).natAbs := by
      intro hd
      apply (two_pow_dvd_S n).2
      have h1z : ((2 ^ (3 * s2 n + 1) : ℕ) : ℤ) ∣ ((S n).natAbs : ℤ) := by exact_mod_cast hd
      have h2z : ((2 : ℤ) ^ (3 * s2 n + 1)) ∣ (S n).natAbs := by simpa using h1z
      exact Int.dvd_natAbs.mp h2z
    have hge : 3 * s2 n ≤ padicValNat 2 (S n).natAbs :=
      (padicValNat_dvd_iff_le hS_ne).mp h1
    have hlt : ¬ 3 * s2 n + 1 ≤ padicValNat 2 (S n).natAbs := fun hle =>
      h2 ((padicValNat_dvd_iff_le hS_ne).mpr hle)
    omega
  have hA_v2 : padicValNat 2 A.natAbs = s2 n + s2 (3 * n) := by
    have hv := congrArg (padicValNat 2) hS_natAbs
    rw [padicValNat.mul hD_pos.ne' (Int.natAbs_ne_zero.mpr hA_ne), hS_v2, hD_v2] at hv
    have hs3_le : s2 (3 * n) ≤ 2 * s2 n := by
      have h1 : 3 * n = n + 2 * n := by ring
      rw [h1]
      calc s2 (n + 2 * n) ≤ s2 n + s2 (2 * n) := s2_add_le n (2 * n)
        _ = 2 * s2 n := by rw [s2_mul_two]; ring
    omega
  have hs2_ge1 : 1 ≤ s2 n := by
    by_contra h0
    have : s2 n = 0 := by omega
    have := (s2_eq_zero_iff n).mp this
    omega
  have hs3_ge2 : 2 ≤ s2 (3 * n) := s2_three_mul_ge_two hn
  have hA_v2_ge3 : 3 ≤ padicValNat 2 A.natAbs := by omega
  have h8_dvd_nat : 8 ∣ A.natAbs := by
    have : 2 ^ 3 ∣ A.natAbs := (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hA_ne)).mpr hA_v2_ge3
    simpa using this
  have h8_dvd : (8 : ℤ) ∣ A := Int.dvd_natAbs.mp (by exact_mod_cast h8_dvd_nat)
  obtain ⟨m, hm⟩ := h8_dvd
  refine ⟨m, ?_, ?_⟩
  · rw [ha_eq, hm]
    push_cast; rfl
  · -- Odd m ↔ padicValNat 2 A.natAbs = 3 ↔ s2 n = 1 ↔ ∃ k, n = 2^k
    have hm_ne : m ≠ 0 := fun h0 => hA_ne (by rw [hm, h0, mul_zero])
    have hA_abs : A.natAbs = 8 * m.natAbs := by
      have := congrArg Int.natAbs hm
      simpa [Int.natAbs_mul] using this
    have hm_v2 : padicValNat 2 A.natAbs = 3 + padicValNat 2 m.natAbs := by
      rw [hA_abs, padicValNat.mul (by norm_num) (Int.natAbs_ne_zero.mpr hm_ne)]
      have h8v : padicValNat 2 8 = 3 := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow 3]
      rw [h8v]
    have hodd_iff : Odd m ↔ padicValNat 2 m.natAbs = 0 := by
      constructor
      · intro hodd
        apply padicValNat.eq_zero_of_not_dvd
        intro h2
        have h2z : (2 : ℤ) ∣ m := Int.dvd_natAbs.mp (by exact_mod_cast h2)
        obtain ⟨t, ht⟩ := h2z
        obtain ⟨u, hu⟩ := hodd
        omega
      · intro hv0
        have hndvd : ¬ 2 ∣ m.natAbs := by
          intro h2
          have hge1 : 1 ≤ padicValNat 2 m.natAbs :=
            (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hm_ne)).mp (by simpa using h2)
          omega
        have hndvdz : ¬ (2 : ℤ) ∣ m := fun h2 => hndvd (by exact_mod_cast Int.dvd_natAbs.mpr h2)
        rcases Int.even_or_odd m with hev | hodd
        · obtain ⟨t, ht⟩ := hev
          exact (hndvdz ⟨t, by omega⟩).elim
        · exact hodd
    rw [hodd_iff]
    constructor
    · intro hv0
      have hs1 : s2 n = 1 := by omega
      exact (s2_eq_one_iff n).mp hs1
    · rintro ⟨k, rfl⟩
      have hs1 : s2 (2 ^ k) = 1 := s2_pow_two k
      have hs3 : s2 (3 * 2 ^ k) = 2 := s2_three_mul_pow_two k
      omega

end OeisA189286Proof

theorem OMA.solution : type_of% @OeisA189286.conjecture_3 :=
  OeisA189286Proof.main_theorem
