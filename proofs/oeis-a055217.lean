import OMAStatements.S_oeis_a055217
import Mathlib

namespace OMA.P055217

open Polynomial Finset

/-- The trinomial 1 + x + x^2. -/
noncomputable def Q : ℤ[X] := 1 + X + X ^ 2

/-- The trinomial coefficients. -/
noncomputable def c (n k : ℕ) : ℤ := (Q ^ n).coeff k

lemma Qc (j : ℕ) : Q.coeff j = if j ≤ 2 then 1 else 0 := by
  unfold Q
  rcases j with _ | _ | _ | j <;> simp [coeff_one, coeff_X, coeff_X_pow]

lemma Q_natDegree : Q.natDegree = 2 := by
  unfold Q
  compute_degree!

lemma Q_reverse : Q.reverse = Q := by
  ext k
  rw [coeff_reverse, Q_natDegree, Qc, Qc]
  by_cases h : k ≤ 2
  · rw [revAt_le h, if_pos h, if_pos (by omega)]
  · rw [revAt_eq_self_of_lt (by omega)]

lemma Qpow_reverse (n : ℕ) : (Q ^ n).reverse = Q ^ n := by
  induction n with
  | zero => rw [pow_zero, ← C_1, reverse_C]
  | succ n ih => rw [pow_succ, reverse_mul_of_domain, ih, Q_reverse]

lemma Qpow_natDegree (n : ℕ) : (Q ^ n).natDegree = 2 * n := by
  rw [natDegree_pow, Q_natDegree]
  ring

lemma c_symm (n k : ℕ) (hk : k ≤ 2 * n) : c n k = c n (2 * n - k) := by
  unfold c
  conv_lhs => rw [← Qpow_reverse n]
  rw [coeff_reverse, Qpow_natDegree, revAt_le hk]

/-- The sum of all coefficients. -/
lemma total (n : ℕ) : ∑ k ∈ range (2 * n + 1), c n k = 3 ^ n := by
  have h := eval_eq_sum_range' (p := Q ^ n) (n := 2 * n + 1) (by rw [Qpow_natDegree]; omega) 1
  have he : (Q ^ n).eval 1 = 3 ^ n := by
    rw [eval_pow]
    unfold Q
    simp
  rw [he] at h
  rw [h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [c]

/-- 2 a(n) + T(n) = 3^n. -/
lemma two_a (n : ℕ) : 2 * (∑ k ∈ range n, c n k) + c n n = 3 ^ n := by
  have h := total n
  rw [show 2 * n + 1 = n + (n + 1) by ring, Finset.sum_range_add, Finset.sum_range_succ'] at h
  have hs : ∑ k ∈ range n, c n (n + (k + 1)) = ∑ k ∈ range n, c n k := by
    rw [← Finset.sum_range_reflect (fun k => c n k) n]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_range] at hk
    rw [c_symm n (n + (k + 1)) (by omega)]
    congr 1
    omega
  rw [hs, add_zero] at h
  linarith

lemma prod (n k : ℕ) : c (n + 1) (k + 2) = c n (k + 2) + c n (k + 1) + c n k := by
  unfold c
  have e : Q ^ (n + 1) = Q ^ n + X * Q ^ n + X ^ 2 * Q ^ n := by
    rw [pow_succ]
    unfold Q
    ring
  rw [e, coeff_add, coeff_add, show k + 2 = (k + 1) + 1 from rfl, coeff_X_mul,
    show k + 1 + 1 = k + 2 from rfl, coeff_X_pow_mul]

lemma dQ : derivative Q = 1 + 2 * X := by
  unfold Q
  simp

/-- The coefficientwise form of Q * (Q^(M+1))' = (M+1) (1 + 2x) Q^(M+1). -/
lemma G (M j : ℕ) :
    c (M + 1) (j + 3) * ((j : ℤ) + 3) + c (M + 1) (j + 2) * ((j : ℤ) + 2)
      + c (M + 1) (j + 1) * ((j : ℤ) + 1)
      = ((M : ℤ) + 1) * (c (M + 1) (j + 2) + 2 * c (M + 1) (j + 1)) := by
  have H : derivative (Q ^ (M + 1)) + X * derivative (Q ^ (M + 1)) + X ^ 2 * derivative (Q ^ (M + 1))
      = C ((M : ℤ) + 1) * (Q ^ (M + 1) + 2 * (X * Q ^ (M + 1))) := by
    rw [derivative_pow_succ, dQ, pow_succ]
    unfold Q
    ring
  have h := congrArg (fun p : ℤ[X] => p.coeff (j + 2)) H
  simp only [coeff_add, coeff_C_mul, coeff_ofNat_mul] at h
  rw [show j + 2 = (j + 1) + 1 from rfl, coeff_X_mul, coeff_X_mul,
    show j + 1 + 1 = j + 2 from rfl, coeff_X_pow_mul, coeff_derivative, coeff_derivative,
    coeff_derivative] at h
  unfold c
  push_cast at h ⊢
  linear_combination h

/-- The central trinomial coefficients. -/
noncomputable def T (n : ℕ) : ℤ := c n n

/-- (N+2) T(N+2) = (2N+3) T(N+1) + 3(N+1) T(N) for N ≥ 1. -/
lemma T_rec (M : ℕ) :
    ((M : ℤ) + 3) * T (M + 3) = (2 * (M : ℤ) + 5) * T (M + 2) + 3 * ((M : ℤ) + 2) * T (M + 1) := by
  -- N = M + 1
  have r1 := G M M
  have r2 : T (M + 2) = c (M + 1) (M + 2) + T (M + 1) + c (M + 1) (M + 2) := by
    have h := prod (M + 1) M
    have hs := c_symm (M + 1) M (by omega)
    rw [show 2 * (M + 1) - M = M + 2 by omega] at hs
    unfold T
    rw [h, hs]
  have r2' : T (M + 3) = c (M + 2) (M + 3) + T (M + 2) + c (M + 2) (M + 3) := by
    have h := prod (M + 2) (M + 1)
    have hs := c_symm (M + 2) (M + 1) (by omega)
    rw [show 2 * (M + 2) - (M + 1) = M + 3 by omega] at hs
    unfold T
    rw [show M + 3 = M + 1 + 2 from rfl, h, hs]
  have r3 : c (M + 2) (M + 3) = c (M + 1) (M + 3) + c (M + 1) (M + 2) + T (M + 1) := by
    have h := prod (M + 1) (M + 1)
    unfold T
    rw [show M + 3 = M + 1 + 2 from rfl, h]
  unfold T at r2 r2' r3 ⊢
  linear_combination (2 : ℤ) * r1 + ((M : ℤ) + 3) * r2' + (2 * (M : ℤ) + 6) * r3
    + (-((M : ℤ) + 2)) * r2

end OMA.P055217

theorem OMA.solution : type_of% @OMA.S_oeis_a055217.main := by
  intro n hn
  dsimp only
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  have e1 : N + 3 - 1 = N + 2 := by omega
  have e2 : N + 3 - 2 = N + 1 := by omega
  have e3 : N + 3 - 3 = N := by omega
  rw [e1, e2, e3]
  have ha : ∀ j : ℕ, 2 * OMA.S_oeis_a055217.b j = 3 ^ (j + 1) - OMA.P055217.T (j + 1) := by
    intro j
    have h := OMA.P055217.two_a (j + 1)
    unfold OMA.S_oeis_a055217.b OMA.S_oeis_a055217.a OMA.P055217.T
    unfold OMA.P055217.c OMA.P055217.Q at h ⊢
    linarith
  have h3 := ha (N + 3)
  have h2 := ha (N + 2)
  have h1 := ha (N + 1)
  have h0 := ha N
  have t1 := OMA.P055217.T_rec (N + 1)
  have t0 := OMA.P055217.T_rec N
  push_cast at t1 t0 ⊢
  have key : 2 * ((((N : ℤ) + 3) + 1) * OMA.S_oeis_a055217.b (N + 3)
      - (5 * ((N : ℤ) + 3) + 1) * OMA.S_oeis_a055217.b (N + 2)
      + 3 * (((N : ℤ) + 3) - 1) * OMA.S_oeis_a055217.b (N + 1)
      + 9 * (((N : ℤ) + 3) - 1) * OMA.S_oeis_a055217.b N) = 0 := by
    linear_combination (((N : ℤ) + 3) + 1) * h3 - (5 * ((N : ℤ) + 3) + 1) * h2
      + 3 * (((N : ℤ) + 3) - 1) * h1 + 9 * (((N : ℤ) + 3) - 1) * h0 - t1 + 3 * t0
  linarith
