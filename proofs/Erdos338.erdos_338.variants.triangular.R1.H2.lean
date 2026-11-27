import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1
import Mathlib

-- Step Erdos338.erdos_338.variants.triangular.R1.H2: hypothesis H2 of reduction Erdos338.erdos_338.variants.triangular.R1
-- Credit: @luciusacarr

/-! Triangular numbers are `0, 1, 3, 6 (mod 9)`, so no `n ≡ 5 (mod 9)` is a sum of at most two of them. -/

open Erdos338 Filter

namespace OMA338tri

lemma tri_mod9 (k : ℕ) : k * (k + 1) / 2 % 9 = 0 ∨ k * (k + 1) / 2 % 9 = 1 ∨
    k * (k + 1) / 2 % 9 = 3 ∨ k * (k + 1) / 2 % 9 = 6 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 18 ∧ k = 18 * q + r := ⟨k / 18, k % 18, Nat.mod_lt _ (by norm_num), by omega⟩
  have e : (18 * q + r) * (18 * q + r + 1) = r * (r + 1) + 2 * (9 * (18 * q * q + q * (2 * r + 1))) := by ring
  rw [e, Nat.add_mul_div_left _ _ (by norm_num), Nat.add_mul_mod_self_left]
  interval_cases r <;> simp

lemma not_two (S : Multiset ℕ) (hS : ∀ x ∈ S, x ∈ Set.range fun k : ℕ ↦ k * (k + 1) / 2)
    (hc : S.card ≤ 2) : S.sum % 9 ≠ 5 := by
  have key : ∀ x ∈ S, x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 3 ∨ x % 9 = 6 := by
    intro x hx
    obtain ⟨k, rfl⟩ := hS x hx
    exact tri_mod9 k
  rcases Nat.lt_or_ge S.card 2 with h | h
  · rcases Nat.lt_or_ge S.card 1 with h' | h'
    · have : S.card = 0 := by omega
      rw [Multiset.card_eq_zero] at this; subst this; simp
    · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp (show S.card = 1 by omega)
      have := key a (by simp)
      rw [Multiset.sum_singleton]; omega
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp (show S.card = 2 by omega)
    have := key a (by simp); have := key b (by simp)
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
    omega

theorem main_H2 : OMA.R_Erdos338_erdos_338_variants_triangular_R1.H2 := by
  unfold OMA.R_Erdos338_erdos_338_variants_triangular_R1.H2
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  obtain ⟨S, hS, hc, hs⟩ := hN (9 * N + 5) (by omega)
  exact not_two S hS hc (by omega)

end OMA338tri

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1.H2 := OMA338tri.main_H2
