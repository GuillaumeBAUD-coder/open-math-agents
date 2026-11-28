import OMAStatements.S_oeis_a111403

-- Problem: A111403: a(n) = f(f(n+1)) - f(f(n)), where f(m) = 2^m.
-- Upstream: formal-conjectures statements/oeis-a111403.lean:0 (declaration OMA.S_oeis_a111403.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a111403

open OMA.S_oeis_a111403

lemma key (n : ℕ) : A002716 (2 * n) = (2 : ℤ) ^ (2 ^ (n + 1)) - 2 ^ (2 ^ n) + 1 ∧
    A002716 (2 * n + 1) = (2 : ℤ) ^ (2 ^ (n + 1)) + 1 := by
  induction n with
  | zero => norm_num [A002716]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    have e0 : A002716 (2 * (n + 1)) =
        A002716 (2 * n + 1) ^ 2 - 3 * A002716 (2 * n + 1) + 3 := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, A002716, if_pos (by omega)]
    have e1 : A002716 (2 * (n + 1) + 1) =
        A002716 (2 * (n + 1)) + A002716 (2 * n + 1) - 1 := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, A002716, if_neg (by omega)]
      rfl
    have hp : (2 : ℤ) ^ (2 ^ (n + 1 + 1)) = ((2 : ℤ) ^ (2 ^ (n + 1))) ^ 2 := by
      rw [← pow_mul, pow_succ 2 (n + 1)]
    refine ⟨?_, ?_⟩
    · rw [e0, h1, hp]
      ring
    · rw [e1, e0, h1, hp]
      ring

lemma solve : ∀ n : ℕ, a n = A002716 (2 * n) - 1 := by
  intro n
  rw [(key n).1]
  simp only [a, f]
  push_cast
  ring

end OMA.P_oeis_a111403

theorem OMA.solution : type_of% @OMA.S_oeis_a111403.main := OMA.P_oeis_a111403.solve
