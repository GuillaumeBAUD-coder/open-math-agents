import OMAStatements.S_oeis_a133603

-- Problem: A133603: The matrix-vector product A133566 * A000108.
-- Upstream: formal-conjectures statements/oeis-a133603.lean:0 (declaration OMA.S_oeis_a133603.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The Catalan numbers satisfy (k+2) C(k+1) = 2 (2k+1) C(k). For odd n the recurrence involves
C(n), C(n-1), C(n-2) and for even n it involves C(n), ..., C(n-3); in both cases the left side is a
polynomial combination of these relations. -/

namespace A133603Aux

open OMA.S_oeis_a133603

theorem catR (k : ℕ) : ((k : ℤ) + 2) * (catalan (k + 1) : ℤ) = 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by
  have h1 : (((k + 1 + 1) * catalan (k + 1) : ℕ) : ℤ) = ((k + 1).centralBinom : ℤ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom (k + 1)
  have h0 : (((k + 1) * catalan k : ℕ) : ℤ) = (k.centralBinom : ℤ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom k
  have hc : (((k + 1) * (k + 1).centralBinom : ℕ) : ℤ) = ((2 * (2 * k + 1) * k.centralBinom : ℕ) : ℤ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  push_cast at h1 h0 hc
  have hk : (k : ℤ) + 1 ≠ 0 := by positivity
  have h : ((k : ℤ) + 1) * (((k : ℤ) + 2) * (catalan (k + 1) : ℤ) - 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ)) = 0 := by
    linear_combination ((k : ℤ) + 1) * h1 - 2 * (2 * (k : ℤ) + 1) * h0 + hc
  have h2 := (mul_eq_zero.mp h).resolve_left hk
  linarith

theorem a_odd (j : ℕ) : a (2 * j + 1) = (catalan (2 * j + 1) : ℤ) := by
  unfold a
  have e1 : (2 * j + 1) % 2 = 1 := by omega
  rw [if_pos e1]

theorem a_even (j : ℕ) : a (2 * j + 2) = (catalan (2 * j + 2) : ℤ) + (catalan (2 * j + 1) : ℤ) := by
  unfold a
  have e1 : ¬ ((2 * j + 2) % 2 = 1) := by omega
  have e2 : ¬ (2 * j + 2 = 0) := by omega
  rw [if_neg e1, if_neg e2]
  rfl

end A133603Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a133603.main := by
  intro n hn
  obtain ⟨j, hj⟩ : ∃ j, n = 2 * j + 3 ∨ n = 2 * j + 4 := ⟨(n - 3) / 2, by omega⟩
  rcases hj with rfl | rfl
  · have e1 : 2 * j + 3 - 1 = 2 * j + 2 := rfl
    have e2 : 2 * j + 3 - 2 = 2 * j + 1 := rfl
    have a3 : OMA.S_oeis_a133603.a (2 * j + 3) = (catalan (2 * j + 3) : ℤ) := A133603Aux.a_odd (j + 1)
    rw [e1, e2, a3, A133603Aux.a_even j, A133603Aux.a_odd j]
    have ha := A133603Aux.catR (2 * j + 2)
    have hb := A133603Aux.catR (2 * j + 1)
    push_cast at ha hb ⊢
    linear_combination (2 * (2 * (j : ℤ) + 3) - 7 * (2 * (j : ℤ) + 3) ^ 2 + 3 * (2 * (j : ℤ) + 3) ^ 3) * ha + (20 + 6 * (2 * (j : ℤ) + 3) - 34 * (2 * (j : ℤ) + 3) ^ 2 + 12 * (2 * (j : ℤ) + 3) ^ 3) * hb
  · have e1 : 2 * j + 4 - 1 = 2 * j + 3 := rfl
    have e2 : 2 * j + 4 - 2 = 2 * j + 2 := rfl
    have a4 : OMA.S_oeis_a133603.a (2 * j + 4) = (catalan (2 * j + 4) : ℤ) + (catalan (2 * j + 3) : ℤ) :=
      A133603Aux.a_even (j + 1)
    have a3 : OMA.S_oeis_a133603.a (2 * j + 3) = (catalan (2 * j + 3) : ℤ) := A133603Aux.a_odd (j + 1)
    rw [e1, e2, a4, a3, A133603Aux.a_even j]
    have ha := A133603Aux.catR (2 * j + 3)
    have hb := A133603Aux.catR (2 * j + 2)
    have hc := A133603Aux.catR (2 * j + 1)
    push_cast at ha hb hc ⊢
    linear_combination (2 * (2 * (j : ℤ) + 4) - 7 * (2 * (j : ℤ) + 4) ^ 2 + 3 * (2 * (j : ℤ) + 4) ^ 3) * ha + (22 + (2 * (j : ℤ) + 4) - 38 * (2 * (j : ℤ) + 4) ^ 2 + 15 * (2 * (j : ℤ) + 4) ^ 3) * hb + (12 - 2 * (2 * (j : ℤ) + 4) - 22 * (2 * (j : ℤ) + 4) ^ 2 + 12 * (2 * (j : ℤ) + 4) ^ 3) * hc
