import OMAStatements.S_oeis_a233398

-- Problem: A233398: n^n mod 3^n.
-- Upstream: formal-conjectures statements/oeis-a233398.lean:0 (declaration OMA.S_oeis_a233398.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a233398

open OMA.S_oeis_a233398

lemma solve : ∀ x : ℕ, 3 ∣ x → a x = 0 := by
  rintro x ⟨m, rfl⟩
  unfold a
  apply Nat.mod_eq_zero_of_dvd
  rw [mul_pow]
  exact Dvd.intro _ rfl

end OMA.P_oeis_a233398

theorem OMA.solution : type_of% @OMA.S_oeis_a233398.main := OMA.P_oeis_a233398.solve
