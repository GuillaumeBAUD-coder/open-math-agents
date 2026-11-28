import OMAStatements.S_oeis_a133306

/-! Mathar's recurrence for the weighted binomial sum of OEIS A133306. -/
-- Credit: @STARDUSTLC666

namespace WeightedBinomial

open Polynomial Finset

private noncomputable def quad (b c : ℚ) : ℚ[X] := C c + C b * X + X^2

private noncomputable def diagonal (b c : ℚ) (k : ℕ) : ℚ :=
  ((quad b c)^(k+1)).coeff k

-- Index k represents the positive sequence index k+1.
private def weight (u v : ℚ) (k : ℕ) : ℚ :=
  (∑ i ∈ range (k+1), ((k+1).choose i : ℚ) * ((k+1).choose (i+1) : ℚ) *
    u^i * v^(k+1-i)) / ((k : ℚ)+1)

private lemma encode (u v : ℚ) (k : ℕ) :
    diagonal (u+v) (u*v) k = u * ((k : ℚ)+1) * weight u v k := by
  have factor : quad (u+v) (u*v) = (X + C v) * (X + C u) := by
    simp only [quad,map_add,map_mul]
    ring
  have raw : diagonal (u+v) (u*v) k =
      u * ∑ i ∈ range (k+1), ((k+1).choose i : ℚ) * ((k+1).choose (i+1) : ℚ) *
        u^i * v^(k+1-i) := by
    rw [diagonal,factor,mul_pow,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.mul_sum]
    apply sum_congr rfl
    intro i hi
    have bound := mem_range.mp hi
    rw [coeff_X_add_C_pow,coeff_X_add_C_pow,show k+1-(k-i) = i+1 by omega,
      Nat.choose_symm_of_eq_add (show k+1 = (k-i)+(i+1) by omega),pow_succ u i]
    ring
  rw [raw,weight]
  field_simp

-- The auxiliary factor makes the three neighboring coefficients a single derivative identity.
private noncomputable def aux (b c : ℚ) (k : ℕ) : ℚ[X] :=
  -C (((k : ℚ)+4)*c) - C b * X + C ((k : ℚ)+2) * X^2

private lemma polynomial_identity (b c : ℚ) (k : ℕ) :
    C (((k : ℚ)+3)^2-1) * quad b c ^ (k+3) -
      C (((k : ℚ)+3)*(2*((k : ℚ)+3)-1)*b) * (quad b c ^ (k+2) * X) +
      C (((k : ℚ)+3)*((k : ℚ)+2)*(b^2-4*c)) * (quad b c ^ (k+1) * X^2) =
    (quad b c ^ (k+2) * aux b c k).derivative * X -
      C ((k : ℚ)+2) * (quad b c ^ (k+2) * aux b c k) := by
  have dq : (quad b c).derivative = C b + 2*X := by
    simp [quad,derivative_pow,derivative_mul,C_ofNat]
  have dh : (aux b c k).derivative = -C b + 2*C ((k : ℚ)+2)*X := by
    simp [aux,derivative_pow,derivative_mul,C_ofNat]
    ring
  rw [derivative_mul,derivative_pow_succ (quad b c) (k+1),dq,dh]
  rw [show quad b c ^ (k+3) = quad b c ^ (k+1) * quad b c ^ 2 by
    rw [← pow_add]]
  rw [show quad b c ^ (k+2) = quad b c ^ (k+1) * quad b c by rw [pow_succ]]
  generalize quad b c ^ (k+1) = R
  simp only [quad,aux,Nat.cast_add,Nat.cast_one,map_add,map_sub,map_mul,map_pow,
    map_ofNat,map_one]
  ring

private lemma diagonal_relation (b c : ℚ) (k : ℕ) :
    (((k : ℚ)+3)^2-1)*diagonal b c (k+2) -
      ((k : ℚ)+3)*(2*((k : ℚ)+3)-1)*b*diagonal b c (k+1) +
      ((k : ℚ)+3)*((k : ℚ)+2)*(b^2-4*c)*diagonal b c k = 0 := by
  have h := congrArg (fun p : ℚ[X] => p.coeff (k+2)) (polynomial_identity b c k)
  simp only [coeff_add,coeff_sub,coeff_C_mul,coeff_mul_X,coeff_mul_X_pow,coeff_derivative,
    Nat.cast_add,Nat.cast_one] at h
  unfold diagonal
  linear_combination h

private lemma recurrence (u v : ℚ) (hu : 0 < u) (k : ℕ) :
    ((k : ℚ)+4)*weight u v (k+2) -
      (u+v)*(2*((k : ℚ)+3)-1)*weight u v (k+1) +
      ((k : ℚ)+1)*((u+v)^2 - 4*(u*v))*weight u v k = 0 := by
  have h := diagonal_relation (u+v) (u*v) k
  rw [encode,encode,encode] at h
  push_cast at h
  apply mul_left_cancel₀ (show u*((k : ℚ)+2)*((k : ℚ)+3) ≠ 0 by positivity)
  rw [mul_zero]
  linear_combination h

end WeightedBinomial

open WeightedBinomial OMA.S_oeis_a133306

theorem OMA.solution : type_of% @OMA.S_oeis_a133306.main := by
  intro n hn
  match n with
  | 0 | 1 => omega
  | 2 => norm_num [a,Finset.sum_range_succ,Nat.choose]
  | k+3 =>
    have entry (j : ℕ) : a (j+1) = weight 5 6 j := by simp [a,weight]
    change (((k+3 : ℕ) : ℚ)+1) * a (k+3) +
      11 * (-2*((k+3 : ℕ) : ℚ)+1) * a (k+2) + (((k+3 : ℕ) : ℚ)-2) * a (k+1) = 0
    rw [entry (k+2),entry (k+1),entry k]
    push_cast
    have h := recurrence 5 6 (by norm_num) k
    linear_combination h
