import OMAStatements.S_oeis_a038867
namespace OMA.A038867Proof
open OMA.S_oeis_a038867
lemma a_eq (n : ℕ) : a n = 15 * n ^ 2 + 75 * n + 125 := by
  unfold a
  have : (n + 5) ^ 3 = n ^ 3 + (15 * n ^ 2 + 75 * n + 125) := by ring
  omega
abbrev P (x : ZMod 625) : Prop :=
  x.val % 5 = 0 ∧ (x.val % 25 ≠ 0 ∨ (x.val % 125 = 0 ∧ x.val ≠ 0))
set_option maxRecDepth 100000 in
lemma P_values : ∀ x : ZMod 625, P (15 * x ^ 2 + 75 * x + 125) := by decide
set_option maxRecDepth 100000 in
lemma not_P_squares : ∀ y : ZMod 625, ¬ P (y * y) := by decide
end OMA.A038867Proof
open OMA.A038867Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a038867.main := by
  rintro n ⟨k, hk⟩
  rw [a_eq] at hk
  have h := congrArg (fun t : ℕ => (t : ZMod 625)) hk
  push_cast at h
  exact not_P_squares _ (h ▸ P_values n)
