import OMAStatements.S_oeis_a004395

open OMA.S_oeis_a004395 in
theorem OMA.solution : type_of% @OMA.S_oeis_a004395.main := by
  have r : ∀ k : ℕ, a (3*k+1) = a (3*k) * (2*k+1) ∧ a (3*k+2) = a (3*k+1) * (2*k+1) ∧ a (3*k+3) = a (3*k+2) * (2*k+2) := fun k => by
    refine ⟨?_, ?_, ?_⟩ <;> rw [a] <;> congr 1 <;> norm_cast <;> omega
  intro n hn
  obtain ⟨k, rfl | rfl | rfl⟩ : ∃ k, n = 3*k+4 ∨ n = 3*k+5 ∨ n = 3*k+6 := ⟨(n-4)/3, by omega⟩ <;>
  obtain ⟨a1, a2, a3⟩ := r k <;> obtain ⟨b1, b2, b3⟩ := r (k+1) <;> simp at * <;> ring_nf at * <;> simp [*] <;> ring
