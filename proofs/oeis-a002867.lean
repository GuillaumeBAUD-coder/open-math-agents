import OMAStatements.S_oeis_a002867
import Mathlib

-- Problem: A002867: a(n) = binomial(n,floor(n/2))*(n+1)!.
-- Upstream: formal-conjectures statements/oeis-a002867.lean:0 (declaration OMA.S_oeis_a002867.main)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof.  Split by the parity of n.  With X = C(2k+1, k) and Y = C(2k, k) one has
-- C(2k+2, k+1) = 2 X and (k+1) X = (2k+1) Y; with Z = C(2k+3, k+1) one has (k+2) Z = (2k+3) * 2 X.
-- After expanding the factorials the recurrence is a multiple of one of these two identities.

namespace OMA.A002867

lemma choose_mid (k : ℕ) : (2 * k + 2).choose (k + 1) = 2 * (2 * k + 1).choose k := by
  have h1 : (2 * k + 2).choose (k + 1) = (2 * k + 1).choose k + (2 * k + 1).choose (k + 1) :=
    Nat.choose_succ_succ' (2 * k + 1) k
  have h2 : (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k :=
    Nat.choose_symm_of_eq_add (by omega)
  omega

lemma choose_step (k : ℕ) : (k + 1) * (2 * k + 1).choose k = (2 * k + 1) * (2 * k).choose k := by
  have h := Nat.add_one_mul_choose_eq (2 * k) k
  have h2 : (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k :=
    Nat.choose_symm_of_eq_add (by omega)
  rw [h2] at h
  linarith

lemma choose_step' (k : ℕ) :
    (k + 2) * (2 * k + 3).choose (k + 1) = (2 * k + 3) * (2 * k + 2).choose (k + 1) := by
  have h := Nat.add_one_mul_choose_eq (2 * k + 2) (k + 1)
  have h2 : (2 * k + 3).choose (k + 2) = (2 * k + 3).choose (k + 1) :=
    Nat.choose_symm_of_eq_add (by omega)
  have h3 : (2 * k + 2 + 1).choose (k + 1 + 1) = (2 * k + 3).choose (k + 2) := rfl
  rw [h3, h2] at h
  linarith

end OMA.A002867

theorem OMA.solution : type_of% @OMA.S_oeis_a002867.main := by
  intro n hn
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 2 ∨ n = 2 * k + 3 := by
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · exact ⟨m - 1, Or.inl (by omega)⟩
    · exact ⟨m - 1, Or.inr (by omega)⟩
  · -- n = 2k + 2
    have e1 : 2 * k + 2 - 1 = 2 * k + 1 := by omega
    have e2 : 2 * k + 2 - 2 = 2 * k := by omega
    have d1 : (2 * k + 2) / 2 = k + 1 := by omega
    have d2 : (2 * k + 1) / 2 = k := by omega
    have d3 : (2 * k) / 2 = k := by omega
    have f1 : (2 * k + 2 + 1).factorial = (2 * k + 3) * ((2 * k + 2) * (2 * k + 1).factorial) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]
    have f2 : (2 * k + 1 + 1).factorial = (2 * k + 2) * (2 * k + 1).factorial :=
      Nat.factorial_succ _
    have hY : ((k : ℤ) + 1) * ((2 * k + 1).choose k : ℤ)
        = (2 * (k : ℤ) + 1) * ((2 * k).choose k : ℤ) := by
      exact_mod_cast OMA.A002867.choose_step k
    unfold OMA.S_oeis_a002867.a
    rw [e1, e2, d1, d2, d3, f1, f2, OMA.A002867.choose_mid k]
    push_cast
    linear_combination (4 * (2 * (k : ℤ) + 2) * ((2 * k + 1).factorial : ℤ)) * hY
  · -- n = 2k + 3
    have e1 : 2 * k + 3 - 1 = 2 * k + 2 := by omega
    have e2 : 2 * k + 3 - 2 = 2 * k + 1 := by omega
    have d1 : (2 * k + 3) / 2 = k + 1 := by omega
    have d2 : (2 * k + 2) / 2 = k + 1 := by omega
    have d3 : (2 * k + 1) / 2 = k := by omega
    have f1 : (2 * k + 3 + 1).factorial = (2 * k + 4) * ((2 * k + 3) * (2 * k + 2).factorial) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]
    have f2 : (2 * k + 2 + 1).factorial = (2 * k + 3) * (2 * k + 2).factorial :=
      Nat.factorial_succ _
    have f3 : (2 * k + 1 + 1).factorial = (2 * k + 2).factorial := rfl
    have hZ : ((k : ℤ) + 2) * ((2 * k + 3).choose (k + 1) : ℤ)
        = (2 * (k : ℤ) + 3) * (2 * ((2 * k + 1).choose k : ℤ)) := by
      have h := OMA.A002867.choose_step' k
      rw [OMA.A002867.choose_mid k] at h
      exact_mod_cast h
    unfold OMA.S_oeis_a002867.a
    rw [e1, e2, d1, d2, d3, f1, f2, f3, OMA.A002867.choose_mid k]
    push_cast
    linear_combination (2 * (2 * (k : ℤ) + 3) * ((2 * k + 2).factorial : ℤ)) * hZ
