import OMAStatements.S_oeis_a038867

-- Problem: A038867: a(n) = (n+5)^3 - n^3.
-- Upstream: formal-conjectures statements/oeis-a038867.lean:0 (declaration OMA.S_oeis_a038867.main)
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A038867Proof

open OMA.S_oeis_a038867

/-- `a n = 15 n^2 + 75 n + 125`. -/
lemma a_eq (n : ℕ) : a n = 15 * n ^ 2 + 75 * n + 125 := by
  unfold a
  have h : (n + 5) ^ 3 = n ^ 3 + (15 * n ^ 2 + 75 * n + 125) := by ring
  omega

/-- A residue mod 625 whose 5-adic valuation (as a residue) is 1 or 3. Squares never have this,
while every value `15 n^2 + 75 n + 125` does: if `5 ∤ n` the valuation is 1, and if `n = 5m` the
value is `125 (3m^2 + 3m + 1)` with `3m^2 + 3m + 1` never divisible by 5. -/
def P (x : ZMod 625) : Prop :=
  x.val % 5 = 0 ∧ (x.val % 25 ≠ 0 ∨ (x.val % 125 = 0 ∧ x.val ≠ 0))

instance : DecidablePred P := fun x => by unfold P; infer_instance

set_option maxRecDepth 100000 in
lemma P_values : ∀ x : ZMod 625, P (15 * x ^ 2 + 75 * x + 125) := by decide

set_option maxRecDepth 100000 in
lemma not_P_squares : ∀ y : ZMod 625, ¬ P (y * y) := by decide

end OMA.A038867Proof

open OMA.A038867Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a038867.main := by
  intro n hsq
  obtain ⟨k, hk⟩ := hsq
  rw [a_eq] at hk
  have h := congrArg (fun t : ℕ => (t : ZMod 625)) hk
  push_cast at h
  have h1 := P_values (n : ZMod 625)
  rw [h] at h1
  exact not_P_squares _ h1
