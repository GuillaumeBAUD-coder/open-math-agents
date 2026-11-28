import OMAStatements.S_oeis_a171556
import Mathlib

namespace OMA.A171556Proof

lemma cat_rec (m : ℕ) : ((m : ℤ) + 2) * (catalan (m + 1) : ℤ) = 2 * (2 * (m : ℤ) + 1) * (catalan m : ℤ) := by
  have h1 : (m + 1 + 1) * catalan (m + 1) = Nat.centralBinom (m + 1) := succ_mul_catalan_eq_centralBinom (m + 1)
  have h0 : (m + 1) * catalan m = Nat.centralBinom m := succ_mul_catalan_eq_centralBinom m
  have h2 : (m + 1) * Nat.centralBinom (m + 1) = 2 * (2 * m + 1) * Nat.centralBinom m :=
    Nat.succ_mul_centralBinom_succ m
  have h : (m + 1) * ((m + 2) * catalan (m + 1)) = (m + 1) * (2 * (2 * m + 1) * catalan m) := by
    calc (m + 1) * ((m + 2) * catalan (m + 1)) = (m + 1) * Nat.centralBinom (m + 1) := by rw [← h1]
      _ = 2 * (2 * m + 1) * Nat.centralBinom m := h2
      _ = (m + 1) * (2 * (2 * m + 1) * catalan m) := by rw [← h0]; ring
  have h' := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) h
  exact_mod_cast h'

lemma cat_pos (m : ℕ) : 1 ≤ catalan m := by
  have h0 : (m + 1) * catalan m = Nat.centralBinom m := succ_mul_catalan_eq_centralBinom m
  have hp : 0 < Nat.centralBinom m := Nat.centralBinom_pos m
  rcases Nat.eq_zero_or_pos (catalan m) with h | h
  · rw [h] at h0; omega
  · exact h

lemma a_cast (m : ℕ) : (OMA.S_oeis_a171556.a m : ℤ) = 3 * (catalan m : ℤ) - 2 := by
  have := cat_pos m
  unfold OMA.S_oeis_a171556.a
  omega

end OMA.A171556Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a171556.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 2 - 2 = k := by omega
  rw [e1, e2, OMA.A171556Proof.a_cast, OMA.A171556Proof.a_cast, OMA.A171556Proof.a_cast]
  have h1 := OMA.A171556Proof.cat_rec k
  have h2 := OMA.A171556Proof.cat_rec (k + 1)
  push_cast at h2 ⊢
  linear_combination 3 * (k : ℤ) * h2 - 3 * ((k : ℤ) + 1) * h1
