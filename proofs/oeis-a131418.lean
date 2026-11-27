import OMAStatements.S_oeis_a131418
import Mathlib

-- Problem: A131418: Numbers n such that Sum_digits(n)=Sum_digits[n+Sum_digits(n)], with n>=0.
-- Upstream: formal-conjectures statements/oeis-a131418.lean:0 (declaration OMA.S_oeis_a131418.main)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof.  A number is congruent to its digit sum modulo 9.  Let s be the digit sum of n.  Then
-- n = s (mod 9), and the digit sum of n + s, which is s by hypothesis, is n + s (mod 9).
-- Hence n + s = s (mod 9), that is, 9 divides n.

theorem OMA.solution : type_of% @OMA.S_oeis_a131418.main := by
  intro n h
  unfold OMA.S_oeis_a131418.IsTerm OMA.S_oeis_a131418.digitSum at h
  have h2 : n + (Nat.digits 10 n).sum ≡ (Nat.digits 10 (n + (Nat.digits 10 n).sum)).sum [MOD 9] :=
    Nat.modEq_nine_digits_sum (n + (Nat.digits 10 n).sum)
  rw [← h] at h2
  have h3 : n + (Nat.digits 10 n).sum ≡ 0 + (Nat.digits 10 n).sum [MOD 9] := by
    rw [zero_add]
    exact h2
  have h4 : n ≡ 0 [MOD 9] := Nat.ModEq.add_right_cancel' _ h3
  exact (Nat.modEq_zero_iff_dvd).1 h4
