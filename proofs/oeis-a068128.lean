import OMAStatements.S_oeis_a068128
import Mathlib.Tactic

/-!
Counterexample at n = 0 for OEIS A068128: triangular 0 = 0, and any natural
number whose base-10 digit sum is 0 equals 0, so the target set is contained
in {0} and cannot be infinite.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068128.main) := by
  intro h
  have hinf := h 0
  have htri0 : OMA.S_oeis_a068128.triangular 0 = 0 := rfl
  have hsum0 : ∀ t : ℕ, (Nat.digits 10 t).sum = 0 → t = 0 := by
    intro t
    induction t using Nat.strongRecOn with
    | ind t ih =>
      intro hsum
      by_cases ht : t = 0
      · exact ht
      · rw [Nat.digits_eq_cons_digits_div (by omega) ht, List.sum_cons] at hsum
        have hdiv : t / 10 = 0 :=
          ih (t / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero ht) (by omega)) (by omega)
        omega
  have hsub : {t : ℕ | (∃ k : ℕ, t = OMA.S_oeis_a068128.triangular k) ∧
      (Nat.digits 10 t).sum = OMA.S_oeis_a068128.triangular 0} ⊆ ({0} : Set ℕ) := by
    intro t ht
    rw [htri0] at ht
    exact hsum0 t ht.2
  exact hinf ((Set.finite_singleton 0).subset hsub)
