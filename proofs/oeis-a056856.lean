import OMAStatements.S_oeis_a056856
import Mathlib

namespace OMA.S_oeis_a056856

open Polynomial in
lemma prod_comp (n r : ℕ) :
    (∏ j ∈ Finset.Icc 1 r, (C j + C n * X : ℕ[X])) =
      (∏ j ∈ Finset.Icc 1 r, (C j + X : ℕ[X])).comp (C n * X) := by
  rw [Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp

end OMA.S_oeis_a056856

theorem OMA.solution : type_of% @OMA.S_oeis_a056856.main := by
  intro n k hk hkn
  open OMA.S_oeis_a056856 in
  simp only [a056856, a130534, prod_comp]
  rw [Polynomial.comp_C_mul_X_coeff]
