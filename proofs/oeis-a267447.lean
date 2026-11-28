import OMAStatements.S_oeis_a267447
import Mathlib

namespace OMA.S_oeis_a267447

lemma r1 : ∀ l c r : Bool, ruleOut 129 l c r = !ruleOut 126 l c r := by decide
lemma r2 : ∀ l c r : Bool, ruleOut 126 (!l) (!c) (!r) = ruleOut 126 l c r := by decide

lemma comp : ∀ t : ℕ, ∀ i : ℤ, cell 129 (t + 1) i = !cell 126 (t + 1) i := by
  intro t
  induction t with
  | zero => intro i; simp only [cell, r1]
  | succ t ih =>
    intro i
    show ruleOut 129 (cell 129 (t + 1) (i - 1)) (cell 129 (t + 1) i) (cell 129 (t + 1) (i + 1))
      = !ruleOut 126 (cell 126 (t + 1) (i - 1)) (cell 126 (t + 1) i) (cell 126 (t + 1) (i + 1))
    rw [ih, ih, ih, r1, r2]

end OMA.S_oeis_a267447

theorem OMA.solution : type_of% @OMA.S_oeis_a267447.main := by
  intro n hn
  open OMA.S_oeis_a267447 in
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  unfold a A071051 onCount
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  rw [comp]
  cases cell 126 (t + 1) ((j : ℤ) - ((t + 1 : ℕ) : ℤ)) <;> simp
