import OMAStatements.S_oeis_a289629
import Mathlib

namespace OMA.P_oeis_a289629

set_option maxRecDepth 100000 in
/-- `8^30 + 7^30 = 113 * 3361 * 25741 * 12001921 * 10742679301`, a product of distinct primes. -/
theorem sqf : Squarefree (8 ^ 30 + 7 ^ 30 : ℕ) := by
  have p1 : Nat.Prime 113 := by norm_num
  have p2 : Nat.Prime 3361 := by norm_num
  have p3 : Nat.Prime 25741 := by norm_num
  have p4 : Nat.Prime 12001921 := by norm_num
  have p5 : Nat.Prime 10742679301 := by norm_num
  rw [show (8 ^ 30 + 7 ^ 30 : ℕ) = 113 * 3361 * 25741 * 12001921 * 10742679301 by norm_num]
  refine Nat.squarefree_mul_iff.mpr ⟨by norm_num, ?_, p5.squarefree⟩
  refine Nat.squarefree_mul_iff.mpr ⟨by norm_num, ?_, p4.squarefree⟩
  refine Nat.squarefree_mul_iff.mpr ⟨by norm_num, ?_, p3.squarefree⟩
  exact Nat.squarefree_mul_iff.mpr ⟨by norm_num, p1.squarefree, p2.squarefree⟩

theorem main_proof :
    ¬ (∀ m : ℕ, 1 ≤ m →
      ¬ Squarefree (OMA.S_oeis_a289629.E (22 * m - 11) 2) ∧
      ¬ Squarefree (OMA.S_oeis_a289629.E (20 * m - 6) 3) ∧
      ¬ Squarefree (OMA.S_oeis_a289629.E (20 * m - 2) 3) ∧
      ¬ Squarefree (OMA.S_oeis_a289629.E (3 ^ m) 7) ∧
      ¬ Squarefree (OMA.S_oeis_a289629.E (15 * m) 7) ∧
      ¬ Squarefree (OMA.S_oeis_a289629.E (20 * m - 15) 14) ∧
      ¬ Squarefree (OMA.S_oeis_a289629.E (16 * m - 8) 19) ∧
      ¬ Squarefree (OMA.S_oeis_a289629.E (42 * m - 35) 23) ∧
      ¬ Squarefree (OMA.S_oeis_a289629.E (8 * m - 4) 113)) := by
  intro h
  apply (h 2 (by norm_num)).2.2.2.2.1
  have e : OMA.S_oeis_a289629.E (15 * 2) 7 = ((8 ^ 30 + 7 ^ 30 : ℕ) : ℤ) := by
    unfold OMA.S_oeis_a289629.E
    norm_num
  rw [e, Int.squarefree_natCast]
  exact sqf

end OMA.P_oeis_a289629

open OMA.P_oeis_a289629 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a289629.main) := main_proof
