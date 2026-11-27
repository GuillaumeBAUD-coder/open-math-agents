import OMAStatements.S_oeis_a136433

-- Problem: A136433: a(n+2) = a(n+1)*(n mod 3 + 1) + (n mod 2 + 1), a(1) = 11.
-- Upstream: formal-conjectures statements/oeis-a136433.lean:0 (declaration OMA.S_oeis_a136433.main)
-- Credit: @surrenderyourfreedom (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Idea: the multipliers cycle through 1, 2, 3, so three consecutive steps multiply by exactly 6:
-- a(k+4) = 6 a(k+1) + c(k mod 6) for an explicit additive table c. Since c has period 6,
-- a(k+10) - 6 a(k+7) = a(k+4) - 6 a(k+1), which is the conjectured recurrence.

namespace OMA.A136433Proof

open OMA.S_oeis_a136433

/-- The additive term of three consecutive steps, indexed by `k mod 6`. -/
def c : ℕ → ℤ
  | 0 => 13
  | 1 => 9
  | 2 => 7
  | 3 => 17
  | 4 => 6
  | _ => 8

/-- Three steps of the recurrence multiply by `6` and add `c (k % 6)`. -/
lemma step3 (k : ℕ) : (a (k + 4) : ℤ) = 6 * a (k + 1) + c (k % 6) := by
  have e4 : a (k + 4) = a (k + 3) * ((k + 2) % 3 + 1) + ((k + 2) % 2 + 1) := rfl
  have e3 : a (k + 3) = a (k + 2) * ((k + 1) % 3 + 1) + ((k + 1) % 2 + 1) := rfl
  have e2 : a (k + 2) = a (k + 1) * (k % 3 + 1) + (k % 2 + 1) := rfl
  rw [e4, e3, e2]
  rw [show k % 3 = k % 6 % 3 by omega, show (k + 1) % 3 = (k % 6 + 1) % 3 by omega,
    show (k + 2) % 3 = (k % 6 + 2) % 3 by omega, show k % 2 = k % 6 % 2 by omega,
    show (k + 1) % 2 = (k % 6 + 1) % 2 by omega, show (k + 2) % 2 = (k % 6 + 2) % 2 by omega]
  have hr : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases k % 6 <;> simp [c] <;> ring

end OMA.A136433Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a136433.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
  rw [show k + 10 - 3 = k + 7 by omega, show k + 10 - 6 = k + 4 by omega,
    show k + 10 - 9 = k + 1 by omega]
  have h1 := OMA.A136433Proof.step3 k
  have h2 := OMA.A136433Proof.step3 (k + 6)
  rw [show k + 6 + 4 = k + 10 by omega, show k + 6 + 1 = k + 7 by omega,
    Nat.add_mod_right] at h2
  linarith
