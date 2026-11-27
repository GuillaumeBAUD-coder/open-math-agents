import OMAStatements.S_oeis_a110199
import Mathlib

-- Problem: OEIS A110199, partial sums of Catalan numbers C(0) + ... + C(floor(n/2))
-- Credit: @JamesSlash
-- Proof: split on the parity of n. For odd n the four terms cancel in pairs; for even n
-- the identity reduces to the Catalan recurrence (m + 2) C(m + 1) = 2 (2m + 1) C(m).

namespace OMA.A110199Proof

lemma cat (m : ℕ) : (m + 2) * catalan (m + 1) = 2 * (2 * m + 1) * catalan m := by
  have h1 := succ_mul_catalan_eq_centralBinom (m + 1)
  have h2 := succ_mul_catalan_eq_centralBinom m
  have h3 := Nat.succ_mul_centralBinom_succ m
  have key : (m + 1) * ((m + 2) * catalan (m + 1)) = (m + 1) * (2 * (2 * m + 1) * catalan m) := by
    rw [show m + 2 = m + 1 + 1 by ring, h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) key

end OMA.A110199Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a110199.main := by
  intro n hn
  unfold OMA.S_oeis_a110199.a
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 2 := ⟨m - 2, by omega⟩
    have e0 : 2 * (p + 2) / 2 + 1 = p + 3 := by omega
    have e1 : (2 * (p + 2) - 1) / 2 + 1 = p + 2 := by omega
    have e2 : (2 * (p + 2) - 2) / 2 + 1 = p + 2 := by omega
    have e3 : (2 * (p + 2) - 3) / 2 + 1 = p + 1 := by omega
    rw [e0, e1, e2, e3]
    simp only [Finset.sum_range_succ]
    have hc : ((p + 3 : ℕ) : ℤ) * (catalan (p + 2) : ℤ) =
        2 * (2 * ((p + 1 : ℕ) : ℤ) + 1) * (catalan (p + 1) : ℤ) := by
      exact_mod_cast OMA.A110199Proof.cat (p + 1)
    push_cast at hc ⊢
    linear_combination (-2 : ℤ) * hc
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have e0 : (2 * (p + 1) + 1) / 2 + 1 = p + 2 := by omega
    have e1 : (2 * (p + 1) + 1 - 1) / 2 + 1 = p + 2 := by omega
    have e2 : (2 * (p + 1) + 1 - 2) / 2 + 1 = p + 1 := by omega
    have e3 : (2 * (p + 1) + 1 - 3) / 2 + 1 = p + 1 := by omega
    rw [e0, e1, e2, e3]
    ring
