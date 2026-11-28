import OMAStatements.S_oeis_a171556
import Mathlib

-- Problem: A171556: a(n) = 3*C(n)-2, where C(n) = A000108(n).
-- Upstream: formal-conjectures statements/oeis-a171556.lean:0 (declaration OMA.S_oeis_a171556.main)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof.  The Catalan numbers satisfy (m + 2) C(m+1) = 2 (2m + 1) C(m).  Write n = k + 2.  The
-- constant parts of the three terms cancel, and the Catalan parts are a combination of the
-- Catalan recurrence at m = k + 1 and at m = k.

namespace OMA.A171556

/-- The first-order recurrence of the Catalan numbers. -/
lemma catalan_rec (n : ℕ) : (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h1 : (n + 1 + 1) * catalan (n + 1) = (n + 1).centralBinom :=
    succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 : (n + 1) * catalan n = n.centralBinom := succ_mul_catalan_eq_centralBinom n
  have h3 : (n + 1) * (n + 1).centralBinom = 2 * (2 * n + 1) * n.centralBinom :=
    Nat.succ_mul_centralBinom_succ n
  have h4 : (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
    calc (n + 1) * ((n + 2) * catalan (n + 1))
        = (n + 1) * ((n + 1 + 1) * catalan (n + 1)) := by ring
      _ = (n + 1) * (n + 1).centralBinom := by rw [h1]
      _ = 2 * (2 * n + 1) * n.centralBinom := h3
      _ = 2 * (2 * n + 1) * ((n + 1) * catalan n) := by rw [h2]
      _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) h4

lemma catalan_pos' (n : ℕ) : 1 ≤ catalan n := by
  have h2 : (n + 1) * catalan n = n.centralBinom := succ_mul_catalan_eq_centralBinom n
  have h3 := Nat.centralBinom_pos n
  rcases Nat.eq_zero_or_pos (catalan n) with h | h
  · rw [h, mul_zero] at h2
    omega
  · exact h

lemma a_cast (n : ℕ) : (OMA.S_oeis_a171556.a n : ℤ) = 3 * (catalan n : ℤ) - 2 := by
  unfold OMA.S_oeis_a171556.a
  have h := catalan_pos' n
  have h2 : 2 ≤ 3 * catalan n := by omega
  rw [Nat.cast_sub h2]
  push_cast
  ring

end OMA.A171556

theorem OMA.solution : type_of% @OMA.S_oeis_a171556.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 2 - 2 = k := by omega
  rw [e1, e2, OMA.A171556.a_cast, OMA.A171556.a_cast, OMA.A171556.a_cast]
  have r1 : ((k : ℤ) + 3) * (catalan (k + 2) : ℤ)
      = 2 * (2 * (k : ℤ) + 3) * (catalan (k + 1) : ℤ) := by
    have h := OMA.A171556.catalan_rec (k + 1)
    have h' : (k + 3) * catalan (k + 2) = 2 * (2 * k + 3) * catalan (k + 1) := by
      have e : k + 1 + 2 = k + 3 := by omega
      have e' : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [e, e'] at h
      exact h
    exact_mod_cast h'
  have r2 : ((k : ℤ) + 2) * (catalan (k + 1) : ℤ) = 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by
    exact_mod_cast OMA.A171556.catalan_rec k
  push_cast
  linear_combination (3 * (k : ℤ)) * r1 - (3 * ((k : ℤ) + 1)) * r2
