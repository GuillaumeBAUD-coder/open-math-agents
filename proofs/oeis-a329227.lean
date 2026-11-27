import OMAStatements.S_oeis_a329227
import Mathlib

namespace A329227Proof

open PowerSeries OMA.S_oeis_a329227

lemma P_rec (n : ℕ) : P (n + 3) = P (n + 1) + P n := by
  rw [P]

lemma a_zero : a 0 = 0 := by unfold a; simp [P]
lemma a_one : a 1 = 0 := by unfold a; simp [P]
lemma a_two : a 2 = 0 := by unfold a; simp [P]
lemma a_three : a 3 = 0 := by unfold a; simp [P]
lemma a_four : a 4 = 0 := by unfold a; simp [P]
lemma a_five : a 5 = 1 := by unfold a; simp [P]

lemma rec6 (m : ℕ) :
    a (m + 6) = a (m + 5) + a (m + 4) + a (m + 3) - a (m + 2) + a (m + 1) - a m := by
  unfold a
  have p3 := P_rec m
  have p4 := P_rec (m + 1)
  have p5 := P_rec (m + 2)
  have p6 := P_rec (m + 3)
  have p7 := P_rec (m + 4)
  simp only [Nat.add_assoc, Nat.reduceAdd] at p3 p4 p5 p6 p7 ⊢
  rw [p7, p6, p5, p4, p3]
  ring

end A329227Proof

open A329227Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a329227.main := by
  rw [show ((1 - 2 * PowerSeries.X + PowerSeries.X ^ 2 - PowerSeries.X ^ 3)
      * (1 + PowerSeries.X - PowerSeries.X ^ 3) : PowerSeries ℤ)
      = 1 - PowerSeries.X ^ 1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 4
        - PowerSeries.X ^ 5 + PowerSeries.X ^ 6 by ring]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n)
    with rfl | rfl | rfl | rfl | rfl | rfl | h <;>
    try (simp [a_zero, a_one, a_two, a_three, a_four, a_five]; done)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  simp [rec6 m]
  ring
