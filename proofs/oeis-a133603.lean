import OMAStatements.S_oeis_a133603
import Mathlib

-- Problem: OEIS A133603: the corrected Mathar recurrence (n >= 3) for a(n) = C(n) (n odd),
-- C(n) + C(n-1) (n even), C the Catalan numbers.
-- Sketch: write C(k) = centralBinom(k)/(k+1) and use (k+1) centralBinom(k+1) = 2(2k+1) centralBinom(k);
-- with n = m+3 and a case split on the parity of m, each case is a rational-function identity in
-- centralBinom(m) (field_simp, ring). No computer search.
-- Credit: @sntntHb (the owner of the agent is credited as the solver)

namespace A133603Aux

open OMA.S_oeis_a133603

theorem hc (k : ℕ) : (((k + 1).centralBinom : ℕ) : ℚ) =
    (k.centralBinom : ℚ) * (2 * (2 * k + 1)) / (k + 1) := by
  have h := Nat.succ_mul_centralBinom_succ k
  have h' : ((k : ℚ) + 1) * (((k + 1).centralBinom : ℕ) : ℚ) = 2 * (2 * k + 1) * k.centralBinom := by
    exact_mod_cast h
  field_simp
  linear_combination h'

theorem hcat (k : ℕ) : ((catalan k : ℕ) : ℚ) = (k.centralBinom : ℚ) / (k + 1) := by
  have h := succ_mul_catalan_eq_centralBinom k
  have h' : ((k : ℚ) + 1) * ((catalan k : ℕ) : ℚ) = (k.centralBinom : ℚ) := by exact_mod_cast h
  field_simp
  linear_combination h'

theorem main' : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ) * ((n : ℤ) - 2) * (3 * (n : ℤ) - 1) * ((n : ℤ) + 1) * a n -
      8 * (n : ℤ) * (2 * (n : ℤ) - 3) * a (n - 1) -
      4 * ((n : ℤ) - 1) * (3 * (n : ℤ) + 2) * (2 * (n : ℤ) - 3) * (2 * (n : ℤ) - 5) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 2 - 1 = m + 1 := by omega
  have e4 : m + 1 - 1 = m := by omega
  rw [e1, e2]
  apply Int.cast_injective (α := ℚ)
  unfold a
  rcases Nat.even_or_odd m with hm | hm
  · have p3 : (m + 3) % 2 = 1 := by rcases hm with ⟨k, hk⟩; omega
    have p2 : ¬ (m + 2) % 2 = 1 := by rcases hm with ⟨k, hk⟩; omega
    have p1 : (m + 1) % 2 = 1 := by rcases hm with ⟨k, hk⟩; omega
    rw [if_pos p3, if_neg p2, if_pos p1, if_neg (by omega), e3]
    push_cast
    simp only [hcat]
    have c1 := hc m
    have c2 := hc (m + 1)
    have c3 := hc (m + 2)
    simp only [add_assoc, Nat.reduceAdd] at c1 c2 c3 ⊢
    rw [c3, c2, c1]
    push_cast
    field_simp
    ring
  · have p3 : ¬ (m + 3) % 2 = 1 := by rcases hm with ⟨k, hk⟩; omega
    have p2 : (m + 2) % 2 = 1 := by rcases hm with ⟨k, hk⟩; omega
    have p1 : ¬ (m + 1) % 2 = 1 := by rcases hm with ⟨k, hk⟩; omega
    rw [if_neg p3, if_pos p2, if_neg p1, if_neg (by omega), if_neg (by omega), e4,
      show m + 3 - 1 = m + 2 by omega]
    push_cast
    simp only [hcat]
    have c1 := hc m
    have c2 := hc (m + 1)
    have c3 := hc (m + 2)
    simp only [add_assoc, Nat.reduceAdd] at c1 c2 c3 ⊢
    rw [c3, c2, c1]
    push_cast
    field_simp
    ring

end A133603Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a133603.main := A133603Aux.main'
