import OMAStatements.S_oeis_a112849
import Mathlib

namespace A112849Proof

lemma val (a : ℕ → ℚ)
    (h : ∀ n : ℕ, 2 ≤ n → a n = 1 + (1 / 2) * ((2 * n - 1).choose (n - 1) : ℚ) +
      (1 / 2) * ((2 * n - 1).choose n : ℚ))
    (j : ℕ) (hj : 1 ≤ j) : a (j + 1) = 1 + (1 / 2) * ((j + 1).centralBinom : ℚ) := by
  have h1 := h (j + 1) (by omega)
  have e1 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have e2 : j + 1 - 1 = j := by omega
  rw [e1, e2] at h1
  have hc : (j + 1).centralBinom = (2 * j + 1).choose j + (2 * j + 1).choose (j + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have e3 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [e3, Nat.choose_succ_succ']
  rw [h1, hc]
  push_cast
  ring

lemma ratio (k : ℕ) :
    ((k : ℚ) + 1) * ((k + 1).centralBinom : ℚ) = 2 * (2 * (k : ℚ) + 1) * (k.centralBinom : ℚ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ k

end A112849Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a112849.main := by
  intro a _ h n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have v4 := A112849Proof.val a h (m + 3) (by omega)
  have v3 := A112849Proof.val a h (m + 2) (by omega)
  have v2 := A112849Proof.val a h (m + 1) (by omega)
  have h4 := A112849Proof.ratio (m + 3)
  have h3 := A112849Proof.ratio (m + 2)
  have i1 : m + 4 - 1 = m + 3 := by omega
  have i2 : m + 4 - 2 = m + 2 := by omega
  rw [i1, i2]
  simp only [Nat.add_assoc, Nat.reduceAdd] at v4 v3 v2 h4 h3
  rw [v4, v3, v2]
  push_cast at h4 h3 ⊢
  linear_combination (1 / 2) * (3 * ((m : ℚ) + 4) - 5) * h4 - (1 / 2) * (3 * ((m : ℚ) + 4) - 2) * h3
