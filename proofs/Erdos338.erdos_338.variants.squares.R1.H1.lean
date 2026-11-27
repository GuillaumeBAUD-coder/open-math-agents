import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1
import Mathlib.NumberTheory.SumFourSquares

namespace OMA.SquareBasis

lemma residue (a : ℕ) : a^2 % 8 = 0 ∨ a^2 % 8 = 1 ∨ a^2 % 8 = 4 := by
  have h := Nat.mod_lt a (by decide : 0 < 8)
  interval_cases he : a%8 <;> norm_num [Nat.pow_mod, he]

lemma not_three (a b c : ℕ) : (a^2+b^2+c^2)%8 ≠ 7 := by
  have ha := residue a
  have hb := residue b
  have hc := residue c
  rw [Nat.add_mod (a^2+b^2) (c^2), Nat.add_mod (a^2) (b^2)]
  omega

lemma not_small_sum (S : Multiset ℕ) (hS : ∀ a ∈ S, ∃ k : ℕ, k^2 = a)
    (hc : S.card ≤ 3) : S.sum % 8 ≠ 7 := by
  have he : (S.toList : Multiset ℕ) = S := Multiset.coe_toList _
  rw [← he] at hS hc ⊢
  generalize S.toList = l at *
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
  · simp
  · obtain ⟨u, rfl⟩ := hS a (by simp)
    simpa using not_three u 0 0
  · obtain ⟨u, rfl⟩ := hS a (by simp)
    obtain ⟨v, rfl⟩ := hS b (by simp)
    simpa using not_three u v 0
  · have hl : l = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [Multiset.coe_card, List.length_cons] at hc
      omega
    subst l
    obtain ⟨u, rfl⟩ := hS a (by simp)
    obtain ⟨v, rfl⟩ := hS b (by simp)
    obtain ⟨w, rfl⟩ := hS c (by simp)
    simpa [add_assoc] using not_three u v w

end OMA.SquareBasis

-- Step Erdos338.erdos_338.variants.squares.R1.H1: hypothesis H1 of reduction Erdos338.erdos_338.variants.squares.R1
-- Credit: @DeepDuke
-- H1 := basisOrder (Set.range fun k : ℕ ↦ k ^ 2) = 4  /-- Pall: every sufficiently large integer is a sum of at most `5` distinct squares. -/

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1.H1 := by
  have hfour : Erdos338.HasOrder (Set.range fun k : ℕ => k^2) 4 := by
    apply Filter.Eventually.of_forall
    intro n
    obtain ⟨a,b,c,d,hn⟩ := Nat.sum_four_squares n
    refine ⟨(([a^2,b^2,c^2,d^2] : List ℕ) : Multiset ℕ), ?_, by simp, ?_⟩
    · intro x hx
      simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact Set.mem_range_self _
    · simpa [add_assoc] using hn
  change Erdos338.basisOrder (Set.range fun k : ℕ => k^2) = 4
  unfold Erdos338.basisOrder
  apply le_antisymm
  · exact iInf₂_le 4 hfour
  · refine le_iInf₂ fun h hh => ?_
    by_contra hlt
    have hh3 : h ≤ 3 := by
      have hl : (h : ℕ∞) < 4 := lt_of_not_ge hlt
      have hn : h < 4 := by exact_mod_cast hl
      omega
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hh
    obtain ⟨S,hS,hcard,hsum⟩ := hN (8*N+7) (by omega)
    have hbad := OMA.SquareBasis.not_small_sum S hS (hcard.trans hh3)
    rw [hsum] at hbad
    omega

