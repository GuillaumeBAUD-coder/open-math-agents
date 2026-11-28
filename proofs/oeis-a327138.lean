import OMAStatements.S_oeis_a327138
import Mathlib

/-!
The first rise occurs at index two. The cosine difference has the sign
of minus the sine of the midpoint angle. The midpoint angles at indices
one and two are three and five, which lie on opposite sides of π.
The proposed lower bound already fails at this first rise.
-/

namespace OMA.A327138

open S_oeis_a327138

/-- The cosine difference is the product of the two midpoint sine factors. -/
lemma cosine_step (k : ℝ) :
    Real.cos (2 * k + 2) - Real.cos (2 * k) =
      -2 * Real.sin (2 * k + 1) * Real.sin 1 := by
  rw [Real.cos_sub_cos]
  rw [show (2 * k + 2 + 2 * k) / 2 = 2 * k + 1 by ring,
    show (2 * k + 2 - 2 * k) / 2 = 1 by ring]

/-- Of the positive indices up to two, only two gives a rise. -/
lemma first_rise : ¬ rise 1 ∧ rise 2 := by
  have hπ₁ := Real.pi_gt_three
  have hπ₂ := Real.pi_lt_four
  have sine_one : 0 < Real.sin 1 :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith)
  have sine_three : 0 < Real.sin 3 :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith)
  have sine_five : Real.sin 5 < 0 := by
    have h : 0 < Real.sin (5 - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at h
    linarith
  constructor
  · intro h
    have hd := cosine_step 1
    have hc := h.2
    norm_num at hc hd
    nlinarith [mul_pos sine_three sine_one]
  · refine ⟨by decide, ?_⟩
    have hd := cosine_step 2
    norm_num at hd ⊢
    nlinarith [mul_neg_of_neg_of_pos sine_five sine_one]

/-- Counting the first three indices gives rank one at index two. -/
lemma first_rank : rank 2 = 1 := by
  classical
  have h0 : ¬ rise 0 := fun h => (Nat.lt_irrefl 0) h.1
  have hRange : Finset.range (2 + 1) = ({0, 1, 2} : Finset ℕ) := by decide
  rw [rank, hRange]
  simp [Finset.filter_insert, Finset.filter_singleton, h0, first_rise.1, first_rise.2]

end OMA.A327138

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a327138.main) := by
  intro h
  have hFirst := h 1 2 (by decide) OMA.A327138.first_rise.2 OMA.A327138.first_rank
  norm_num at hFirst
  linarith [hFirst.1, Real.pi_lt_four]
