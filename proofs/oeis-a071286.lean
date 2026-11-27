import OMAStatements.S_oeis_a071286
import Mathlib

namespace OMA.P_oeis_a071286

open OMA.S_oeis_a071286

theorem peirce_period (k : ℕ) :
    ∀ i, S_oeis_a071286.peirce (k + 1) (i + (k + 1) * (k + 2)) = S_oeis_a071286.peirce (k + 1) i := by
  induction k with
  | zero =>
    intro i
    show (if (i + 2) % 2 = 0 then Symbol.den 1 else Symbol.sep) =
      (if i % 2 = 0 then Symbol.den 1 else Symbol.sep)
    rw [Nat.add_mod_right]
  | succ k ih =>
    intro i
    show expandStream (k + 1) (S_oeis_a071286.peirce (k + 1)) (i + (k + 1 + 1) * (k + 1 + 2)) =
      expandStream (k + 1) (S_oeis_a071286.peirce (k + 1)) i
    have hq : (i + (k + 1 + 1) * (k + 1 + 2)) / (k + 1 + 2) = i / (k + 1 + 2) + (k + 2) := by
      rw [Nat.add_mul_div_right _ _ (by omega)]
    have hr : (i + (k + 1 + 1) * (k + 1 + 2)) % (k + 1 + 2) = i % (k + 1 + 2) := by
      rw [Nat.add_mul_mod_self_right]
    simp only [expandStream, hq, hr]
    generalize i / (k + 1 + 2) = q
    generalize i % (k + 1 + 2) = r
    have hj : (q + (k + 2) + 1) * (k + 1) = (q + 1) * (k + 1) + (k + 1) * (k + 2) := by ring
    have hev : (k + 1) * (k + 2) % 2 = 0 := Nat.even_iff.mp (Nat.even_mul_succ_self (k + 1))
    have hpar : ((q + 1) * (k + 1) + (k + 1) * (k + 2)) % 2 = ((q + 1) * (k + 1)) % 2 := by
      rw [Nat.add_mod, hev, Nat.add_zero, Nat.mod_mod]
    have h1 : 1 ≤ (q + 1) * (k + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hsub : (q + 1) * (k + 1) + (k + 1) * (k + 2) - 1 =
        ((q + 1) * (k + 1) - 1) + (k + 1) * (k + 2) := Nat.sub_add_comm h1
    have hm : (q + (k + 2)) * (k + 1) + r = (q * (k + 1) + r) + (k + 1) * (k + 2) := by ring
    rw [hj, hpar, hsub, hm, ih, ih]

theorem den_period (i : ℕ) : denominatorAt 5 (i + 15) = denominatorAt 5 i := by
  have h : S_oeis_a071286.peirce 5 (2 * i + 30) = S_oeis_a071286.peirce 5 (2 * i) := peirce_period 4 (2 * i)
  unfold denominatorAt
  rw [show 2 * (i + 15) = 2 * i + 30 by ring, h]

theorem base : ∀ i < 15, denominatorAt 5 i =
    ([2, 4, 5, 3, 1, 5, 4, 3, 5, 4, 2, 5, 3, 4, 5] : List ℕ)[i % 15]! := by
  decide

end OMA.P_oeis_a071286

open OMA.S_oeis_a071286 OMA.P_oeis_a071286 in
theorem OMA.solution : type_of% @OMA.S_oeis_a071286.main := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < 15
    · exact base i hi
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 15 := ⟨i - 15, by omega⟩
      rw [den_period, ih j (by omega), Nat.add_mod_right]
