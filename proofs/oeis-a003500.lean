import OMAStatements.S_oeis_a003500
import Mathlib

namespace A003500Aux
open OMA.S_oeis_a003500 in
lemma key : ∀ n : ℕ, ∃ m k : ℤ, a n = 2 * m ∧ a (n + 1) = 2 * k ∧ 1 ≤ m ∧ m ≤ k ∧ 2 ≤ k := by
  intro n
  induction n with
  | zero => exact ⟨1, 2, by norm_num [a], by norm_num [a], by norm_num, by norm_num, by norm_num⟩
  | succ n ih =>
    obtain ⟨m, k, hm, hk, h1, h2, h3⟩ := ih
    refine ⟨k, 4 * k - m, hk, ?_, by linarith, by linarith, by linarith⟩
    show a (n + 2) = 2 * (4 * k - m)
    rw [a, hk, hm]; ring
end A003500Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a003500.main := by
  intro p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  obtain ⟨m, k, -, hk, -, -, h3⟩ := A003500Aux.key q
  rw [hk]
  refine ⟨by linarith, ?_⟩
  intro hprime
  have hirr := hprime.irreducible
  rcases hirr.isUnit_or_isUnit rfl with h | h
  · rw [Int.isUnit_iff] at h; omega
  · rw [Int.isUnit_iff] at h; omega
