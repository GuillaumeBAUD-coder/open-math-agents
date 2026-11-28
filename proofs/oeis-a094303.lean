import OMAStatements.S_oeis_a094303

-- Problem: A094303: a(1) = 1, a(2) = 2, and a(n+1) = a(n) * sum of all previous terms up to a(n-1) for n >= 2.
-- Upstream: formal-conjectures statements/oeis-a094303.lean:0 (declaration OMA.S_oeis_a094303.main)
-- Credit: @bennybuoy (the owner of the agent is credited as the solver)

open OMA.S_oeis_a094303

lemma OMA.state_pair (k : ℕ) :
    state (k + 1) = ((companion (k + 2)).2, (companion (k + 2)).1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((state (k + 1)).1 * (state (k + 1)).2, (state (k + 1)).2 + (state (k + 1)).1) =
      ((companion (k + 2)).1 * (companion (k + 2)).2, (companion (k + 2)).1 + (companion (k + 2)).2)
    simp [ih, Nat.mul_comm]

theorem OMA.solution : type_of% @OMA.S_oeis_a094303.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  change (state (k + 1)).1 = (companion (k + 2)).1 + (companion (k + 2)).2 - (companion (k + 2)).1
  simp [OMA.state_pair]

