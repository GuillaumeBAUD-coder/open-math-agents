import OMAStatements.S_oeis_a192379
import Mathlib

def OMA.u : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 0, 0, 0)
  | n+1 => ((u n).2.1 + (u n).2.2.2 + 2*(u n).2.2.1,
      (u n).1 + (u n).2.1 + (u n).2.2.1 + 3*(u n).2.2.2,
      (u n).1 + (u n).2.2.2, (u n).2.1 + (u n).2.2.1 + (u n).2.2.2)

open Polynomial OMA OMA.S_oeis_a192379 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192379.main := by
  have m : (X^2 - X - 1 : ℤ[X]).Monic := by monicity!
  have A (n : ℕ) : a n = (u n).2.2.1 := by
    have ⟨s, t, hs, ht⟩ : ∃ s t, (pq n).1 = (X^2-X-1)*s + (C (u n).1 + C (u n).2.1 * X) ∧
        (pq n).2 = (X^2-X-1)*t + (C (u n).2.2.1 + C (u n).2.2.2 * X) := by
      induction n with
      | zero => exact ⟨0, 0, by simp [pq, u]⟩
      | succ n ih =>
        obtain ⟨s, t, hs, ht⟩ := ih
        exact ⟨X*s + C (u n).2.1 + (X+2)*t + C (u n).2.2.2, s + X*t + C (u n).2.2.2,
          by simp [pq, u, hs, ht]; ring, by simp [pq, u, hs, ht]; ring⟩
    rw [a, p, ht, add_modByMonic, self_mul_modByMonic m, (modByMonic_eq_self_iff m).2
      ((show degree _ ≤ 1 by compute_degree).trans_lt (by
        rw [show (X^2-X-1 : ℤ[X]).degree = 2 by compute_degree!]
        norm_num))]
    simp
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [A, u]
  ring
