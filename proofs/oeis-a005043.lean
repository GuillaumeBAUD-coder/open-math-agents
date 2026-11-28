import OMAStatements.S_oeis_a005043

-- Problem: A005043: Riordan numbers: a(n) = (n-1)*(2*a(n-1) + 3*a(n-2))/(n+1).
-- Upstream: statements/oeis-a005043.lean (declaration OMA.S_oeis_a005043.main)
-- Credit: @brinderjaswal-eng (the owner of the agent is credited as the solver)
--
-- Idea. Write t n k for the coefficient of X^k in (1 + X + X^2)^n.
--   * Multiplying by 1 + X + X^2 gives  t (n+1) (k+2) = t n (k+2) + t n (k+1) + t n k.
--   * Differentiating gives, inside one row,
--       (k+2) t n (k+2) + (k+1) t n (k+1) + k t n k = n (t n (k+1) + 2 t n k).
-- At the centre of a row these two facts give, for a n = t n n and b n = t n (n+1),
--       a (n+1) = a n + 2 b n      and      (n+2) b (n+1) = (2n+2) a n + (n+1) b n,
-- and the row relation also gives the symmetry t n (n-1) = t n (n+1). The Riordan recurrence for
-- a n - b n follows by linear algebra, and both sides start at 1, 0.

open Polynomial

namespace OMA.A005043

/-- Coefficient of `X ^ k` in `(1 + X + X ^ 2) ^ n`. -/
noncomputable def t (n k : ℕ) : ℤ := ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff k

lemma t_succ (n k : ℕ) : t (n + 1) (k + 2) = t n (k + 2) + t n (k + 1) + t n k := by
  have h : (1 + X + X ^ 2 : ℤ[X]) ^ (n + 1) = (1 + X + X ^ 2 : ℤ[X]) ^ n
      + (1 + X + X ^ 2 : ℤ[X]) ^ n * X + (1 + X + X ^ 2 : ℤ[X]) ^ n * X ^ 2 := by ring
  unfold t
  rw [h, coeff_add, coeff_add, coeff_mul_X_pow, show k + 2 = k + 1 + 1 from rfl, coeff_mul_X]

lemma deriv_base : derivative (1 + X + X ^ 2 : ℤ[X]) = 1 + C 2 * X := by
  rw [derivative_add, derivative_add, derivative_one, derivative_X, derivative_X_sq, zero_add]

lemma deriv_pow (n : ℕ) : derivative ((1 + X + X ^ 2 : ℤ[X]) ^ n) * (1 + X + X ^ 2)
    = C (n : ℤ) * ((1 + X + X ^ 2 : ℤ[X]) ^ n * (1 + C 2 * X)) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [derivative_pow, deriv_base, Nat.add_sub_cancel]
    ring

lemma coeff_deriv_mul_X (n j : ℕ) :
    (derivative ((1 + X + X ^ 2 : ℤ[X]) ^ n) * X).coeff j = (j : ℤ) * t n j := by
  cases j with
  | zero => simp
  | succ i =>
    rw [coeff_mul_X, coeff_derivative]
    unfold t
    push_cast
    ring

lemma t_deriv (n k : ℕ) :
    ((k : ℤ) + 2) * t n (k + 2) + ((k : ℤ) + 1) * t n (k + 1) + (k : ℤ) * t n k
      = (n : ℤ) * (t n (k + 1) + 2 * t n k) := by
  have key : derivative ((1 + X + X ^ 2 : ℤ[X]) ^ n) * X
      + derivative ((1 + X + X ^ 2 : ℤ[X]) ^ n) * X * X
      + derivative ((1 + X + X ^ 2 : ℤ[X]) ^ n) * X * X ^ 2
      = C (n : ℤ) * ((1 + X + X ^ 2 : ℤ[X]) ^ n * X)
        + C (n : ℤ) * (C 2 * ((1 + X + X ^ 2 : ℤ[X]) ^ n * X ^ 2)) := by
    linear_combination (X : ℤ[X]) * deriv_pow n
  have hE := coeff_deriv_mul_X n
  generalize derivative ((1 + X + X ^ 2 : ℤ[X]) ^ n) * X = E at key hE
  have h := congrArg (fun q : ℤ[X] => q.coeff (k + 2)) key
  simp only [coeff_add, coeff_C_mul, coeff_mul_X_pow] at h
  rw [show k + 2 = k + 1 + 1 from rfl, coeff_mul_X, coeff_mul_X, hE, hE, hE] at h
  rw [show k + 1 + 1 = k + 2 from rfl] at h
  have e1 : ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff (k + 1) = t n (k + 1) := rfl
  have e0 : ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff k = t n k := rfl
  rw [e1, e0] at h
  push_cast at h
  linear_combination h

lemma t_sym (m : ℕ) : t (m + 1) m = t (m + 1) (m + 2) := by
  have h := t_deriv (m + 1) m
  push_cast at h
  have h2 : ((m : ℤ) + 2) * (t (m + 1) m - t (m + 1) (m + 2)) = 0 := by
    linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by positivity)
  · exact sub_eq_zero.mp h3

lemma t_zero_zero : t 0 0 = 1 := by simp [t]

lemma t_zero_one : t 0 1 = 0 := by simp [t, coeff_one]

lemma t_one_one : t 1 1 = 1 := by simp [t, coeff_one, coeff_X, coeff_X_pow]

lemma t_one_two : t 1 2 = 1 := by simp [t, coeff_one, coeff_X, coeff_X_pow]

lemma rel_a (n : ℕ) : t (n + 1) (n + 1) = t n n + 2 * t n (n + 1) := by
  cases n with
  | zero =>
    show t 1 1 = t 0 0 + 2 * t 0 1
    simp [t_zero_zero, t_zero_one, t_one_one]
  | succ m =>
    show t (m + 2) (m + 2) = t (m + 1) (m + 1) + 2 * t (m + 1) (m + 2)
    have h : t (m + 2) (m + 2) = t (m + 1) (m + 2) + t (m + 1) (m + 1) + t (m + 1) m :=
      t_succ (m + 1) m
    rw [h, t_sym m]
    ring

lemma rel_b (n : ℕ) :
    ((n : ℤ) + 2) * t (n + 1) (n + 2) = (2 * (n : ℤ) + 2) * t n n + ((n : ℤ) + 1) * t n (n + 1) := by
  have h := t_succ n n
  have hd := t_deriv n n
  linear_combination ((n : ℤ) + 2) * h + hd

lemma riordan_eq (n : ℕ) :
    OMA.S_oeis_a005043.riordan n = ((t n n - t n (n + 1) : ℤ) : ℚ) ∧
    OMA.S_oeis_a005043.riordan (n + 1) = ((t (n + 1) (n + 1) - t (n + 1) (n + 2) : ℤ) : ℚ) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show OMA.S_oeis_a005043.riordan 0 = ((t 0 0 - t 0 1 : ℤ) : ℚ)
      simp [t_zero_zero, t_zero_one, OMA.S_oeis_a005043.riordan]
    · show OMA.S_oeis_a005043.riordan 1 = ((t 1 1 - t 1 2 : ℤ) : ℚ)
      simp [t_one_one, t_one_two, OMA.S_oeis_a005043.riordan]
  | succ n ih =>
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨ih1, ?_⟩
    have h1 : ((t (n + 1) (n + 1) : ℤ) : ℚ) = t n n + 2 * t n (n + 1) := by
      exact_mod_cast rel_a n
    have h2 : ((n : ℚ) + 2) * t (n + 1) (n + 2)
        = (2 * (n : ℚ) + 2) * t n n + ((n : ℚ) + 1) * t n (n + 1) := by
      exact_mod_cast rel_b n
    have h3 : ((t (n + 2) (n + 2) : ℤ) : ℚ) = t (n + 1) (n + 1) + 2 * t (n + 1) (n + 2) := by
      have h : t (n + 2) (n + 2) = t (n + 1) (n + 1) + 2 * t (n + 1) (n + 2) := rel_a (n + 1)
      exact_mod_cast h
    have h4 : ((n : ℚ) + 3) * t (n + 2) (n + 3)
        = (2 * (n : ℚ) + 4) * t (n + 1) (n + 1) + ((n : ℚ) + 2) * t (n + 1) (n + 2) := by
      have h : (((n + 1 : ℕ) : ℤ) + 2) * t (n + 2) (n + 3)
          = (2 * ((n + 1 : ℕ) : ℤ) + 2) * t (n + 1) (n + 1)
            + (((n + 1 : ℕ) : ℤ) + 1) * t (n + 1) (n + 2) := rel_b (n + 1)
      push_cast at h
      have h' : ((n : ℤ) + 3) * t (n + 2) (n + 3)
          = (2 * (n : ℤ) + 4) * t (n + 1) (n + 1) + ((n : ℤ) + 2) * t (n + 1) (n + 2) := by
        linear_combination h
      exact_mod_cast h'
    show OMA.S_oeis_a005043.riordan (n + 2) = ((t (n + 2) (n + 2) - t (n + 2) (n + 3) : ℤ) : ℚ)
    rw [OMA.S_oeis_a005043.riordan, ih0, ih1]
    push_cast
    have hn : ((n : ℚ) + 3) ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, div_eq_iff hn]
    linear_combination (-((n : ℚ) + 3)) * h3 + h4 - 3 * h2 + (3 * (n : ℚ) + 3) * h1

end OMA.A005043

theorem OMA.solution : type_of% @OMA.S_oeis_a005043.main := by
  intro n hn
  cases n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ m =>
    have h : OMA.S_oeis_a005043.riordan (m + 1)
        = ((OMA.A005043.t (m + 1) (m + 1) - OMA.A005043.t (m + 1) (m + 2) : ℤ) : ℚ) :=
      (OMA.A005043.riordan_eq (m + 1)).1
    rw [h, ← OMA.A005043.t_sym m]
    rfl
