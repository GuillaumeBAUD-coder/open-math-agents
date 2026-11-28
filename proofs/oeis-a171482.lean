import OMAStatements.S_oeis_a171482
import Mathlib

/-!
OEIS A171482, Conjecture 1: a(n) - a(n-1) is 0 or 1.

Strong induction on n, proving at the same time that 1 ≤ a(n) ≤ n for n ≥ 1.
For n + 1 ≥ 4 compare the recurrence at n + 1 and at n.
* If a(n) = a(n-1), the first summands agree and the second summands are a(m) and a(m-1)
  with m = n - a(n) - 1 ≤ n, so the induction hypothesis at m applies
  (both summands are a(0) when m = 0).
* If a(n) = a(n-1) + 1, the second summands agree and the first summands are a(a(n)) and
  a(a(n) - 1), so the induction hypothesis at a(n) ≤ n applies.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a171482.main := by
  intro a h0 h1 h2 hrec
  have key : ∀ n : ℕ, 1 ≤ n →
      (a n = a (n - 1) ∨ a n = a (n - 1) + 1) ∧ 1 ≤ a n ∧ a n ≤ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases Nat.lt_or_ge n 4 with hlt | hge
      · interval_cases n
        · refine ⟨Or.inl ?_, ?_, ?_⟩ <;> simp [h0, h1]
        · refine ⟨Or.inl ?_, ?_, ?_⟩ <;> simp [h1, h2]
        · have h3 : a 3 = 2 := by
            have h := hrec 3 (le_refl 3)
            simpa [h2, h1, h0] using h
          refine ⟨Or.inr ?_, ?_, ?_⟩ <;> simp [h3, h2]
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        obtain ⟨hstep, hk1, hkk⟩ := ih k (by omega) (by omega)
        have e1 : a (k + 1) = a (a k) + a (k + 1 - a k - 2) := by
          have h := hrec (k + 1) (by omega)
          simpa using h
        have e2 := hrec k (by omega)
        show (a (k + 1) = a k ∨ a (k + 1) = a k + 1) ∧ 1 ≤ a (k + 1) ∧ a (k + 1) ≤ k + 1
        rcases hstep with hA | hB
        · rw [← hA] at e2
          rcases Nat.lt_or_ge (k - a k) 2 with hsm | hbg
          · have i1 : k + 1 - a k - 2 = 0 := by omega
            have i2 : k - a k - 2 = 0 := by omega
            rw [i1] at e1
            rw [i2] at e2
            omega
          · have i2 : k - a k - 2 = k + 1 - a k - 2 - 1 := by omega
            rw [i2] at e2
            obtain ⟨hs, -, -⟩ := ih (k + 1 - a k - 2) (by omega) (by omega)
            omega
        · have hidx : a (k - 1) = a k - 1 := by omega
          rw [hidx] at e2
          have hidx2 : k - (a k - 1) - 2 = k + 1 - a k - 2 := by omega
          rw [hidx2] at e2
          obtain ⟨hs, -, -⟩ := ih (a k) (by omega) hk1
          omega
  intro n hn
  exact (key n hn).1
