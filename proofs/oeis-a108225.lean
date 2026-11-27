import OMAStatements.S_oeis_a108225

-- Problem: oeis-a108225
-- Credit: @anmolspace
-- Proof: paired induction a (n+1) = b (n+1) + 1 ∧ a (n+2) = b (n+2) + 1. With x = b (n+1) and
-- T = x (x+1) / 2 (so 2T = x(x+1)), the step reduces to
-- (T + x + 3)(T - x + 2) = (T+1)(T+2) + 4, a polynomial identity given 2T = x(x+1).

namespace OMA.P108225
open OMA.S_oeis_a108225

lemma key (x T : ℕ) (hT : 2 * T = x * (x + 1)) :
    (T + 1 + 1 + (x + 1)) * (T + 1 + 1 - (x + 1) + 1) / 2 = (T + 1) * (T + 1 + 1) / 2 + 1 + 1 := by
  have hxT : x ≤ T := by nlinarith [Nat.le_mul_self x]
  obtain ⟨y, rfl⟩ : ∃ y, T = x + y := ⟨T - x, by omega⟩
  have h1 : x + y + 1 + 1 - (x + 1) + 1 = y + 2 := by omega
  rw [h1]
  have h2 : (x + y + 1 + 1 + (x + 1)) * (y + 2) = (x + y + 1) * (x + y + 1 + 1) + 2 * 2 := by
    nlinarith [hT]
  rw [h2, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]

lemma pair (n : ℕ) : a (n + 1) = b (n + 1) + 1 ∧ a (n + 2) = b (n + 2) + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have ea : a (n + 1 + 2) = (a (n + 2) + a (n + 1)) * (a (n + 2) - a (n + 1) + 1) / 2 := rfl
    have eb3 : b (n + 1 + 2) = b (n + 2) * (b (n + 2) + 1) / 2 + 1 := rfl
    have eb2 : b (n + 2) = b (n + 1) * (b (n + 1) + 1) / 2 + 1 := rfl
    have hT : 2 * (b (n + 1) * (b (n + 1) + 1) / 2) = b (n + 1) * (b (n + 1) + 1) :=
      Nat.mul_div_cancel' (Nat.even_mul_succ_self _).two_dvd
    rw [ea, eb3, ih.1, ih.2, eb2]
    exact key _ _ hT

end OMA.P108225

theorem OMA.solution : type_of% @OMA.S_oeis_a108225.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (OMA.P108225.pair m).1
