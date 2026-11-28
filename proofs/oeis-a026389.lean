import OMAStatements.S_oeis_a026389
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
The even rows of the triangle are coefficients of
(1 + X)^2 (1 + 3X + X^2)^m. The polynomial derivative identity below
has zero coefficient at the central exponent. Reversing the row
polynomials pairs the two coefficients at distance two from their centers.
-/

namespace OMA.S_oeis_a026389

open Polynomial

private abbrev R := ℤ[X]

private noncomputable def J : R := 1 + X
private noncomputable def P : R := 1 + C 3 * X + X^2
private noncomputable def E (n : ℕ) : R := J^2 * P^n
private noncomputable def O (n : ℕ) : R := J * P^n

private theorem T_zero (n : ℕ) : T n 0 = 1 := by
  cases n with
  | zero => simp [T]
  | succ n => cases n <;> simp [T]

private theorem T_diag (n : ℕ) : T n n = 1 := by
  cases n with
  | zero => simp [T]
  | succ n => cases n <;> simp [T]

private theorem T_out (n k : ℕ) (h : n < k) : T n k = 0 := by
  cases n with
  | zero => simp [T, show k ≠ 0 by omega]
  | succ n =>
    cases n with
    | zero => simp [T, show ¬ k ≤ 1 by omega]
    | succ n => simp [T, show k ≠ 0 by omega, show k ≠ n+1+1 by omega, h]

private theorem T_step (n k : ℕ) :
    T (n+2) (k+1) = T (n+1) k + T (n+1) (k+1) +
      (if (n+2)%2 = 0 then 0 else T n k) := by
  by_cases hd : k = n+1
  · subst k
    rw [T_diag, T_diag, T_out _ _ (by omega), T_out n _ (by omega)]
    simp
  · by_cases ho : n+2 < k+1
    · rw [T_out _ _ ho, T_out _ _ (by omega), T_out _ _ (by omega), T_out n _ (by omega)]
      simp
    · rw [T]
      simp only [show k+1 ≠ 0 by omega, show k+1 ≠ n+2 by omega, false_or, if_false,
        ho, Nat.add_sub_cancel]
      split <;> simp_all

private theorem odd_step (n k : ℕ) :
    T (2*n+3) (k+1) = T (2*n+2) k + T (2*n+2) (k+1) + T (2*n+1) k := by
  have h := T_step (2*n+1) k
  simpa only [show (2*n+1+2)%2 ≠ 0 by omega, if_false,
    show 2*n+1+2 = 2*n+3 by omega, show 2*n+1+1 = 2*n+2 by omega] using h

private theorem even_step (n k : ℕ) :
    T (2*n+4) (k+1) = T (2*n+3) k + T (2*n+3) (k+1) := by
  have h := T_step (2*n+2) k
  simpa only [show (2*n+2+2)%2 = 0 by omega, if_true, add_zero,
    show 2*n+2+2 = 2*n+4 by omega, show 2*n+2+1 = 2*n+3 by omega] using h

private theorem O_step (n : ℕ) : O (n+1) = J * E n + X * O n := by
  simp only [O, E, pow_succ P]
  unfold J P
  rw [show C (3 : ℤ) = 3 by exact map_ofNat C 3]
  ring

private theorem E_as_O (n : ℕ) : E n = J * O n := by
  unfold E O
  ring

private theorem coeff_J (p : R) (k : ℕ) :
    (J * p).coeff (k+1) = p.coeff k + p.coeff (k+1) := by
  rw [J, add_mul, one_mul, coeff_add, coeff_X_mul, add_comm]

private theorem coeff_O_zero (n : ℕ) : (O n).coeff 0 = 1 := by
  have hJ : constantCoeff J = 1 := by simp [J]
  have hP : constantCoeff P = 1 := by simp [P]
  change constantCoeff (O n) = 1
  rw [O, map_mul, map_pow, hJ, hP, one_pow, one_mul]

private theorem coeff_E_zero (n : ℕ) : (E n).coeff 0 = 1 := by
  rw [E_as_O, mul_coeff_zero, coeff_O_zero]
  simp [J]

private theorem row_coeff (n : ℕ) :
    (∀ k, T (2*n+1) k = (O n).coeff k) ∧
    (∀ k, T (2*n+2) k = (E n).coeff k) := by
  induction n with
  | zero =>
    constructor <;> intro k
    · change T 1 k = (O 0).coeff k
      by_cases hk : k ≤ 1
      · interval_cases k <;> norm_num [T, O, J, coeff_one, coeff_X]
      · simp [T, O, J, coeff_one, coeff_X, hk, show k ≠ 0 by omega, show 1 ≠ k by omega]
    · change T 2 k = (E 0).coeff k
      rw [show E 0 = J^2 by simp [E]]
      rw [J, coeff_one_add_X_pow]
      by_cases hk : k ≤ 2
      · interval_cases k <;> decide
      · rw [T_out 2 k (by omega), Nat.choose_eq_zero_of_lt (by omega)]
        simp
  | succ n ih =>
    obtain ⟨ho, he⟩ := ih
    have ho' : ∀ k, T (2*n+3) k = (O (n+1)).coeff k := by
      intro k
      cases k with
      | zero => rw [T_zero, coeff_O_zero]
      | succ k => rw [odd_step, he, he, ho, O_step, coeff_add, coeff_J, coeff_X_mul]
    refine ⟨fun k => ?_, fun k => ?_⟩
    · have hr : 2*(n+1)+1 = 2*n+3 := by omega
      rw [hr, ho']
    · have hr : 2*(n+1)+2 = 2*n+4 := by omega
      rw [hr]
      cases k with
      | zero => rw [T_zero, coeff_E_zero]
      | succ k => rw [even_step, ho', ho', E_as_O, coeff_J]

private theorem a_coeff (n : ℕ) : a (n+2) = (E (n+1)).coeff n := by
  unfold a
  simpa only [show 2*(n+2)=2*(n+1)+2 by omega, Nat.add_sub_cancel] using
    (row_coeff (n+1)).2 n


private theorem J_degree : J.natDegree = 1 := by
  rw [J, add_comm]
  exact natDegree_X_add_C (1 : ℤ)

private theorem P_degree : P.natDegree = 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold P
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · simp
      · rw [natDegree_C_mul_X (3 : ℤ) (by decide)]
        decide
    · simp
  · norm_num [P, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow]

private theorem J_ne : J ≠ 0 := by
  intro h
  have he := J_degree
  rw [h, natDegree_zero] at he
  omega

private theorem P_ne : P ≠ 0 := by
  intro h
  have he := P_degree
  rw [h, natDegree_zero] at he
  omega

private theorem J_reverse : J.reverse = J := by
  ext k
  rw [coeff_reverse, J_degree]
  by_cases h : k ≤ 1
  · interval_cases k <;> norm_num [J, coeff_one, coeff_X]
  · rw [revAt_eq_self_of_lt (by omega)]

private theorem P_reverse : P.reverse = P := by
  ext k
  rw [coeff_reverse, P_degree]
  by_cases h : k ≤ 2
  · interval_cases k <;> norm_num [P, coeff_one, coeff_X, coeff_C_mul, coeff_X_pow]
  · rw [revAt_eq_self_of_lt (by omega)]

private theorem P_pow_reverse (n : ℕ) : (P^n).reverse = P^n := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using (reverse_C (1 : ℤ))
  | succ n ih => rw [pow_succ, reverse_mul_of_domain, ih, P_reverse]

private theorem E_reverse (n : ℕ) : (E n).reverse = E n := by
  simp only [E, pow_two J, reverse_mul_of_domain, J_reverse, P_pow_reverse]

private theorem E_degree (n : ℕ) : (E n).natDegree = 2*n+2 := by
  rw [E, natDegree_mul (pow_ne_zero _ J_ne) (pow_ne_zero _ P_ne),
    natDegree_pow, natDegree_pow, J_degree, P_degree]
  omega

private theorem E_symmetric (n : ℕ) (hn : 1 ≤ n) :
    (E n).coeff (n+3) = (E n).coeff (n-1) := by
  conv_lhs => rw [← E_reverse n]
  rw [coeff_reverse, E_degree, revAt_le (by omega), show 2*n+2-(n+3)=n-1 by omega]

private noncomputable def H : R := (X^2-1) * J^2 * (X^4+1)^2

private noncomputable def W (m : ℕ) : R :=
  let n := (m : ℤ)+5
  C (n+2) * P^4 + C (4*(-3*n-2)) * X * P^3 + C (2*(24*n-19)) * X^2 * P^2 +
    C (4*(-18*n+43)) * X^3 * P + C (35*(n-4)) * X^4

private theorem certificate (m : ℕ) :
    X * derivative (H * P^(m+1)) - C ((m : ℤ)+7) * (H * P^(m+1)) =
      P^m * ((X^4+1)*J^2*W m) := by
  calc
    _ = P^m * (X * derivative H * P + X * H * C ((m : ℤ)+1) * derivative P -
        C ((m : ℤ)+7)*H*P) := by
      rw [derivative_mul, derivative_pow_succ, pow_succ P m]
      ring
    _ = _ := by
      congr 1
      simp only [H, P, J, W, derivative_mul, derivative_pow, map_add, map_sub, map_mul,
        map_neg, map_one, map_ofNat, derivative_X, derivative_one, derivative_C, derivative_ofNat,
        Nat.cast_ofNat]
      ring

private theorem coeff_derivative_center (f : R) (k : ℕ) :
    (X * derivative f - C (k : ℤ) * f).coeff k = 0 := by
  cases k with
  | zero => simp [coeff_X_mul_zero]
  | succ k =>
    rw [coeff_sub, coeff_X_mul, coeff_derivative, coeff_C_mul]
    push_cast
    ring

private theorem central_term (k d : ℕ) (hk : 1 ≤ k) :
    ((X^4+1) * (X^d * E k)).coeff (k+d+3) = 2 * a (k+1) := by
  rw [add_mul, one_mul, coeff_add, ← mul_assoc, ← pow_add,
    coeff_X_pow_mul', if_pos (by omega), coeff_X_pow_mul', if_pos (by omega),
    show k+d+3-(4+d)=k-1 by omega, show k+d+3-d=k+3 by omega, E_symmetric k hk]
  have ha := a_coeff (k-1)
  rw [show k-1+2=k+1 by omega, show k-1+1=k by omega] at ha
  rw [← ha, two_mul]


private theorem recurrence (m : ℕ) (hm : 1 ≤ m) :
    let n := (m : ℤ)+5
    (n+2) * a (m+5) + (4*(-3*n-2)) * a (m+4) + (2*(24*n-19)) * a (m+3) +
      (4*(-18*n+43)) * a (m+2) + (35*(n-4)) * a (m+1) = 0 := by
  let n : ℤ := (m : ℤ)+5
  let B (k d : ℕ) : R := (X^4+1) * (X^d * E k)
  have hb (d : ℕ) (hd : 1 ≤ m+4-d) (he : d ≤ 4) :
      (B (m+4-d) d).coeff (m+7) = 2*a (m+5-d) := by
    have hh := central_term (m+4-d) d hd
    rw [show m+4-d+d+3=m+7 by omega, show m+4-d+1=m+5-d by omega] at hh
    exact hh
  have hb0 : (B (m+4) 0).coeff (m+7) = 2*a (m+5) := by
    simpa only [Nat.sub_zero] using hb 0 (by omega) (by omega)
  have hb1 : (B (m+3) 1).coeff (m+7) = 2*a (m+4) := by
    simpa only [show m+4-1=m+3 by omega, show m+5-1=m+4 by omega] using hb 1 (by omega) (by omega)
  have hb2 : (B (m+2) 2).coeff (m+7) = 2*a (m+3) := by
    simpa only [show m+4-2=m+2 by omega, show m+5-2=m+3 by omega] using hb 2 (by omega) (by omega)
  have hb3 : (B (m+1) 3).coeff (m+7) = 2*a (m+2) := by
    simpa only [show m+4-3=m+1 by omega, show m+5-3=m+2 by omega] using hb 3 (by omega) (by omega)
  have hb4 : (B m 4).coeff (m+7) = 2*a (m+1) := by
    simpa only [show m+4-4=m by omega, show m+5-4=m+1 by omega] using hb 4 (by omega) (by omega)
  have he : P^m * ((X^4+1)*J^2*W m) =
      C (n+2) * B (m+4) 0 + C (4*(-3*n-2)) * B (m+3) 1 +
        C (2*(24*n-19)) * B (m+2) 2 + C (4*(-18*n+43)) * B (m+1) 3 +
        C (35*(n-4)) * B m 4 := by
    dsimp only [B, E, W, n]
    rw [pow_add P m 4, pow_add P m 3, pow_add P m 2, pow_add P m 1]
    ring
  have hc : (P^m * ((X^4+1)*J^2*W m)).coeff (m+7) = 0 := by
    rw [← certificate]
    have hh := coeff_derivative_center (H*P^(m+1)) (m+7)
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hh
  rw [he] at hc
  simp only [coeff_add, coeff_C_mul, hb0, hb1, hb2, hb3, hb4] at hc
  apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide)
  dsimp [n] at hc
  linear_combination hc

end OMA.S_oeis_a026389

open OMA.S_oeis_a026389 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026389.main := by
  intro n hn
  let m := n-5
  have hm : 1 ≤ m := by omega
  have he : n = m+5 := by omega
  rw [he]
  have h := recurrence m hm
  simpa only [Nat.cast_add, Nat.cast_ofNat, show m+5-1=m+4 by omega,
    show m+5-2=m+3 by omega, show m+5-3=m+2 by omega, show m+5-4=m+1 by omega] using h
