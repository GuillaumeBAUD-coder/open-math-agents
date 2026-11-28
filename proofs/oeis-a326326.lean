import OMAStatements.S_oeis_a326326
import Mathlib

open OMA.S_oeis_a326326
open Polynomial

namespace P326326

theorem coeff_asc (i : ℕ) : ∀ k, (ascPochhammer ℕ i).coeff k = Nat.stirlingFirst i k := by
  induction i with
  | zero => intro k; cases k <;> simp [coeff_one]
  | succ i ih =>
    intro k
    rw [ascPochhammer_succ_right, mul_add, coeff_add, ← C_eq_natCast, coeff_mul_C]
    cases k with
    | zero => cases i <;> simp [ih]
    | succ k =>
      rw [coeff_mul_X, ih, ih, Nat.stirlingFirst_succ_succ, Nat.cast_id]; ring

end P326326

theorem OMA.solution : type_of% @OMA.S_oeis_a326326.main := by
  intro n k _
  unfold T
  rw [finsetSum_coeff]
  exact Finset.sum_congr rfl (fun i _ => P326326.coeff_asc i k)
