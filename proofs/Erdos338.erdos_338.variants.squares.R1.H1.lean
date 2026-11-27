import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1
import Mathlib

-- Step Erdos338.erdos_338.variants.squares.R1.H1: hypothesis H1 of reduction Erdos338.erdos_338.variants.squares.R1
-- Credit: @luciusacarr

/-! The squares are a basis of order exactly 4: Lagrange's four-square theorem gives order
at most 4, and `8k + 7` is never a sum of at most three squares. -/

namespace OMA338sqH1

open Erdos338 Filter

lemma sq_mod8 (k : ℕ) : k ^ 2 % 8 = 0 ∨ k ^ 2 % 8 = 1 ∨ k ^ 2 % 8 = 4 := by
  have h : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have : k ^ 2 % 8 = (k % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
  rw [this]
  interval_cases (k % 8) <;> simp

lemma not_three (S : Multiset ℕ) (hS : ∀ x ∈ S, x ∈ Set.range fun k : ℕ ↦ k ^ 2)
    (hc : S.card ≤ 3) : S.sum % 8 ≠ 7 := by
  have key : ∀ x ∈ S, x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 4 := by
    intro x hx
    obtain ⟨k, rfl⟩ := hS x hx
    exact sq_mod8 k
  have hs : ∀ a b c : ℕ, a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 4 → b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 4 →
      c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 4 → (a + b + c) % 8 ≠ 7 := by intros; omega
  have h0 : (0 : ℕ) % 8 = 0 ∨ (0 : ℕ) % 8 = 1 ∨ (0 : ℕ) % 8 = 4 := by norm_num
  rcases Nat.lt_or_ge S.card 3 with h | h
  · rcases Nat.lt_or_ge S.card 2 with h' | h'
    · rcases Nat.lt_or_ge S.card 1 with h'' | h''
      · have : S.card = 0 := by omega
        rw [Multiset.card_eq_zero] at this; subst this; simp
      · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp (show S.card = 1 by omega)
        rw [Multiset.sum_singleton]
        simpa using hs a 0 0 (key a (by simp)) h0 h0
    · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp (show S.card = 2 by omega)
      simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
      simpa using hs a b 0 (key a (by simp)) (key b (by simp)) h0
  · obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp (show S.card = 3 by omega)
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
    have := hs a b c (key a (by simp)) (key b (by simp)) (key c (by simp))
    rwa [add_assoc] at this

lemma hasOrder_four : HasOrder (Set.range fun k : ℕ ↦ k ^ 2) 4 := by
  refine Eventually.of_forall fun m => ?_
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
  refine ⟨{a ^ 2, b ^ 2, c ^ 2, d ^ 2}, ?_, by simp, ?_⟩
  · intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · simp; omega

lemma not_hasOrder_three : ¬ HasOrder (Set.range fun k : ℕ ↦ k ^ 2) 3 := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  obtain ⟨S, hS, hc, hs⟩ := hN (8 * N + 7) (by omega)
  exact not_three S hS hc (by omega)

lemma hasOrder_mono {A : Set ℕ} {h h' : ℕ} (H : HasOrder A h) (hh : h ≤ h') : HasOrder A h' := by
  unfold HasOrder at *
  filter_upwards [H] with m ⟨S, hS, hc, hs⟩
  exact ⟨S, hS, hc.trans hh, hs⟩

theorem main_H1 : OMA.R_Erdos338_erdos_338_variants_squares_R1.H1 := by
  unfold OMA.R_Erdos338_erdos_338_variants_squares_R1.H1
  unfold basisOrder
  apply le_antisymm
  · exact iInf₂_le 4 hasOrder_four
  · refine le_iInf₂ fun h hh => ?_
    by_contra hlt
    have : h ≤ 3 := by
      have : (h : ℕ∞) < 4 := lt_of_not_ge hlt
      have : h < 4 := by exact_mod_cast this
      omega
    exact not_hasOrder_three (hasOrder_mono hh this)

end OMA338sqH1

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1.H1 := OMA338sqH1.main_H1
