import OMAStatements.S_oeis_a369275
import Mathlib

namespace A369275aux

lemma shift (y : ℝ) : Real.sin (y + 2) + Real.sin (y - 2) = 2 * Real.sin y * Real.cos 2 := by
  rw [Real.sin_add, Real.sin_sub]
  ring

lemma key (x : ℝ) (h0 : Real.sin x < Real.sin (x + 1))
    (h2 : Real.sin (x + 2) < Real.sin (x + 3))
    (h4 : Real.sin (x + 4) < Real.sin (x + 5)) : False := by
  have e1 := shift (x + 3)
  have e2 := shift (x + 2)
  rw [show x + 3 + 2 = x + 5 by ring, show x + 3 - 2 = x + 1 by ring] at e1
  rw [show x + 2 + 2 = x + 4 by ring, show x + 2 - 2 = x by ring] at e2
  have c := Real.cos_two_neg
  have d : 0 < Real.sin (x + 3) - Real.sin (x + 2) := by linarith
  have hneg : (Real.sin (x + 3) - Real.sin (x + 2)) * Real.cos 2 < 0 :=
    mul_neg_of_pos_of_neg d c
  nlinarith

end A369275aux

theorem OMA.solution : type_of% @OMA.S_oeis_a369275.main := by
  intro k hk hk1
  obtain ⟨h0, -, h2, -⟩ := hk
  obtain ⟨-, -, -, g3⟩ := hk1
  have g4 : Real.sin ((k : ℝ) + 4) < Real.sin ((k : ℝ) + 5) := by
    rw [show ((k : ℝ) + 4) = ((k + 1 : ℕ) : ℝ) + 3 by push_cast; ring,
      show ((k : ℝ) + 5) = ((k + 1 : ℕ) : ℝ) + 4 by push_cast; ring]
    exact g3
  exact A369275aux.key (k : ℝ) h0 h2 g4
