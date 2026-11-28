import OMAStatements.S_oeis_a094303

-- Problem: A094303: a(1) = 1, a(2) = 2, and a(n+1) = a(n) * sum of all previous terms up to a(n-1) for n >= 2.
-- Upstream: formal-conjectures statements/oeis-a094303.lean:0 (declaration OMA.S_oeis_a094303.main)
-- Credit: @datdzrgb (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a094303

lemma OMA.state_succ (k : ℕ) :
    state (k + 1) = ((state k).1 * (state k).2, (state k).2 + (state k).1) := rfl

lemma OMA.companion_succ (k : ℕ) :
    companion (k + 1) = ((companion k).1 + (companion k).2, (companion k).1 * (companion k).2) := rfl

lemma OMA.swap (m : ℕ) :
    state (m + 1) = ((companion (m + 2)).2, (companion (m + 2)).1) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [OMA.state_succ, ih, OMA.companion_succ (k + 2)]
    simp [Nat.mul_comm]

theorem OMA.solution : type_of% @OMA.S_oeis_a094303.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have h1 : a (k + 3) = (state (k + 1)).1 := rfl
  have h2 : u (k + 3 + 1) = (companion (k + 3)).1 := rfl
  have h3 : u (k + 3) = (companion (k + 2)).1 := rfl
  rw [h1, h2, h3, OMA.swap, OMA.companion_succ (k + 2)]
  simp
