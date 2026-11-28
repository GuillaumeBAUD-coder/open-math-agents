import OMAStatements.S_oeis_a008287
import Mathlib

/-! Werner Schulte's formula follows by expanding the quadrinomial as a sum
of a cube and a correction term. -/
namespace Deldor14.Quadrinomial
open Polynomial Finset OMA.S_oeis_a008287

private theorem expansion (n : ℕ) :
    (1+X+X^2+X^3 : ℤ[X])^n =
      ∑ j ∈ range (n+1), C ((-2:ℤ)^j * n.choose j) * (X^j * (1+X)^(3*n-2*j)) := by
  let b : ℤ[X] := 1+X
  have e : (1+X+X^2+X^3 : ℤ[X]) = (C (-2)*X*b)+b^3 := by
    dsimp [b]
    rw [show (C (-2:ℤ) : ℤ[X]) = -2 from by norm_num]
    ring
  rw [e,add_pow]
  apply sum_congr rfl
  intro j hj
  have bound := mem_range.mp hj
  have exp : 3*n-2*j=j+3*(n-j) := by omega
  change (C (-2)*X*b)^j*(b^3)^(n-j)*(n.choose j : ℤ[X]) =
    C ((-2:ℤ)^j * n.choose j)*(X^j*b^(3*n-2*j))
  rw [exp,pow_add,pow_mul,mul_pow,mul_pow,map_mul,map_pow,C_eq_natCast]
  ring

theorem full : type_of% @OMA.S_oeis_a008287.main := by
  intro n k _
  unfold T
  rw [expansion,finsetSum_coeff]
  let g (j : ℕ) := (-2:ℤ)^j * n.choose j * ((3*n-2*j).choose (k-j) : ℤ)
  have s : ∀ j : ℕ, (C ((-2:ℤ)^j * n.choose j) *
       (X^j*(1+X)^(3*n-2*j))).coeff k = if j≤k then g j else 0 := by
    intro j
    rw [coeff_C_mul, coeff_X_pow_mul',coeff_one_add_X_pow]
    split_ifs <;> simp [g]
  simp_rw [s]
  rw [← sum_filter]
  have mask : (range (n+1)).filter (·≤k)=(range (k+1)).filter (·≤n) := by
    ext i
    simp only [mem_filter,mem_range]
    omega
  rw [mask,sum_filter]
  apply sum_congr rfl
  intro j hj
  by_cases h : j≤n
  · simp [h,g]
  · simp [h,g,Nat.choose_eq_zero_of_lt (by omega : n<j)]
end Deldor14.Quadrinomial
theorem OMA.solution : type_of% @OMA.S_oeis_a008287.main := Deldor14.Quadrinomial.full
