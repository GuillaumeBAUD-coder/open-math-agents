import OMAStatements.S_oeis_a009388

namespace OMA.S_oeis_a009388

lemma inv {x : ℕ} (h : InSeq x) : 2 ≤ x ∧ (x % 3 = 0 ∨ x % 3 = 2) := by
  induction h with
  | base => omega
  | step _ _ iha ihb =>
    rename_i a b _ _
    obtain ⟨ha2, ha⟩ := iha
    obtain ⟨hb2, hb⟩ := ihb
    have hab : 4 ≤ a * b := Nat.mul_le_mul ha2 hb2
    have hmod : a * b % 3 = 0 ∨ a * b % 3 = 1 := by
      rw [Nat.mul_mod]
      rcases ha with h | h <;> rcases hb with h' | h' <;> simp [h, h']
    generalize a * b = c at hab hmod
    omega

end OMA.S_oeis_a009388

open OMA.S_oeis_a009388 in
theorem OMA.solution : type_of% @OMA.S_oeis_a009388.main := by
  refine ⟨fun x hx => (inv hx).2, ?_⟩
  rintro n ⟨h0, h1, h2⟩
  have := (inv h0).2
  have := (inv h1).2
  have := (inv h2).2
  omega
