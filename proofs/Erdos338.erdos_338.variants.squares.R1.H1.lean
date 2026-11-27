import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1

-- Step Erdos338.erdos_338.variants.squares.R1.H1: hypothesis H1 of reduction Erdos338.erdos_338.variants.squares.R1
-- Credit: @ivillar
-- H1 := basisOrder (Set.range fun k : ℕ ↦ k ^ 2) = 4
--
-- Proof: Lagrange's four-square theorem (Nat.sum_four_squares) gives order at most 4, and no
-- number 8N+7 is a sum of at most three squares (squares mod 8 lie in {0,1,4}), so no h <= 3 works.

namespace OMA.E338

lemma three_sq_mod8 (a b c : ℕ) : (a ^ 2 + b ^ 2 + c ^ 2) % 8 ≠ 7 := by
  intro h
  have key : ∀ x y z : ZMod 8, x ^ 2 + y ^ 2 + z ^ 2 ≠ 7 := by decide
  apply key a b c
  have h' : ((a ^ 2 + b ^ 2 + c ^ 2 : ℕ) : ZMod 8) = ((7 : ℕ) : ZMod 8) := by
    rw [ZMod.natCast_eq_natCast_iff']
    exact h
  push_cast at h'
  exact h'

lemma small_sum (S : Multiset ℕ) (hS : ∀ x ∈ S, x ∈ Set.range fun k : ℕ ↦ k ^ 2)
    (hc : S.card ≤ 3) : ∃ a b c : ℕ, S.sum = a ^ 2 + b ^ 2 + c ^ 2 := by
  have sq : ∀ x ∈ S, ∃ k, k ^ 2 = x := fun x hx => hS x hx
  interval_cases h : S.card
  · rw [Multiset.card_eq_zero] at h
    subst h
    exact ⟨0, 0, 0, by simp⟩
  · obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp h
    obtain ⟨k, hk⟩ := sq x (by simp)
    exact ⟨k, 0, 0, by simp [hk]⟩
  · obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.mp h
    obtain ⟨k, hk⟩ := sq x (by simp)
    obtain ⟨l, hl⟩ := sq y (by simp)
    exact ⟨k, l, 0, by simp [hk, hl]⟩
  · obtain ⟨x, y, z, rfl⟩ := Multiset.card_eq_three.mp h
    obtain ⟨k, hk⟩ := sq x (by simp)
    obtain ⟨l, hl⟩ := sq y (by simp)
    obtain ⟨n, hn⟩ := sq z (by simp)
    exact ⟨k, l, n, by simp [hk, hl, hn]; ring⟩

end OMA.E338

open OMA.E338 in
theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1.H1 := by
  unfold OMA.R_Erdos338_erdos_338_variants_squares_R1.H1 Erdos338.basisOrder
  have h4 : Erdos338.HasOrder (Set.range fun k : ℕ ↦ k ^ 2) 4 := by
    unfold Erdos338.HasOrder
    refine Filter.Eventually.of_forall fun m => ?_
    obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
    refine ⟨{a ^ 2, b ^ 2, c ^ 2, d ^ 2}, ?_, by simp, ?_⟩
    · intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    · simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
      rw [← h]; ring
  have hmin : ∀ h : ℕ, Erdos338.HasOrder (Set.range fun k : ℕ ↦ k ^ 2) h → 4 ≤ h := by
    intro h hh
    by_contra hlt
    unfold Erdos338.HasOrder at hh
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hh
    obtain ⟨S, hS, hc, hsum⟩ := hN (8 * N + 7) (by omega)
    obtain ⟨a, b, c, habc⟩ := small_sum S hS (by omega)
    apply three_sq_mod8 a b c
    rw [← habc, hsum]
    omega
  apply le_antisymm
  · exact iInf₂_le 4 h4
  · exact le_iInf₂ fun h hh => by exact_mod_cast hmin h hh
