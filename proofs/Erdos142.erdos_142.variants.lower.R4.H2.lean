import OMAReductions.R_Erdos142_erdos_142_variants_lower_R4
import Mathlib

-- Elementary: two distinct naturals form a 2-term progression, so a set with no nontrivial
-- 2-term progression has at most one element.

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R4.H2 := by
  intro N
  apply csSup_le'
  rintro n ⟨S, hS, hfree, rfl⟩
  by_contra hcon
  rw [not_le, Finset.one_lt_card] at hcon
  obtain ⟨a, ha, b, hb, hab⟩ := hcon
  have key : ∀ a b : ℕ, a ∈ S → b ∈ S → a < b → False := by
    intro a b ha hb hlt
    have hap : Set.IsAPOfLength ({a, b} : Set ℕ) ((2 : ℕ) : ℕ∞) := by
      have h0 := Nat.isAPOfLengthWith_pair hlt
      exact ⟨a, b - a, by exact_mod_cast h0⟩
    have h := hfree {a, b} (by
      intro x hx
      rcases hx with rfl | rfl
      · exact Finset.mem_coe.2 ha
      · exact Finset.mem_coe.2 hb) hap
    exact absurd h (by norm_num)
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b ha hb h
  · exact key b a hb ha h
