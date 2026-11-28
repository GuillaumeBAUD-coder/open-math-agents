import OMAStatements.S_oeis_a061243
import Mathlib

private theorem prod_modEq (n r : ℕ) : (∏ i ∈ Finset.Icc 1 r, (n + i)) ≡ r.factorial [MOD n] := by
  induction r with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty, Nat.factorial_zero]
  | succ r ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ, mul_comm (r + 1)]
    refine Nat.ModEq.mul ih ?_
    exact Nat.add_mod_left n (r + 1)

open OMA.S_oeis_a061243 in

theorem OMA.solution : type_of% @OMA.S_oeis_a061243.main := by
  intro n _
  unfold a kempner
  congr 2
  ext r
  exact and_congr_right fun _ => (prod_modEq n r).dvd_iff (dvd_refl n)
