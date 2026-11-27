import FormalConjectures.ErdosProblems.«46»

/-! Select one dense color after dilation by the denominator. Repeatedly apply the
unit-fraction theorem beyond the largest previous summand, then dilate the union. -/
namespace OMA.R_Erdos46_erdos_46_variants_positive_rat_R1
open Finset
open scoped Classical

/-- Some color class has positive upper density even after deleting any initial segment. -/
def H1 : Prop := ∀ c : ℕ → ℕ, (Set.range c).Finite → ∃ j : ℕ, ∀ B : ℕ,
  0 < {n : ℕ | B < n ∧ c n = j}.upperDensity

/-- Bloom's unit-sum theorem for sets of positive upper density. -/
def H2 : Prop := ∀ A : Set ℕ, 0 ∉ A → 0 < A.upperDensity →
  ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ ∑ n ∈ S, (1 / n : ℚ) = 1

theorem main : H1 → H2 → type_of% @Erdos46.erdos_46.variants.positive_rat := by
  intro hcolor hunit c hc q hq
  let d := q.den
  have hd : 0 < d := q.den_pos
  let g := fun n : ℕ => c (d * n)
  have hg : (Set.range g).Finite := hc.subset (by rintro _ ⟨n, rfl⟩; exact ⟨_, rfl⟩)
  obtain ⟨j, hj⟩ := hcolor g hg
  have pool (k : ℕ) : ∃ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n ∧ g n = j) ∧
      (∑ n ∈ S, (1 / n : ℚ)) = k := by
    induction k with
    | zero => exact ⟨∅, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨S, hS, hsum⟩ := ih
      let B := max 1 (S.sup id)
      obtain ⟨T, hT, hTsum⟩ := hunit _ (by simp) (hj B)
      have hdis : Disjoint S T := by
        apply disjoint_left.2
        intro n hn ht
        have hle : n ≤ B := (le_sup (f := id) hn).trans (le_max_right _ _)
        exact (not_lt_of_ge hle) (hT ht).1
      refine ⟨S ∪ T, ?_, ?_⟩
      · intro n hn
        rcases mem_union.1 hn with hs | ht
        · exact hS n hs
        · exact ⟨lt_of_le_of_lt (le_max_left _ _) (hT ht).1, (hT ht).2⟩
      · rw [sum_union hdis, hsum, hTsum, Nat.cast_succ]
  have hi : 0 ≤ q.num := le_of_lt (Rat.num_pos.mpr hq)
  obtain ⟨S, hS, hs⟩ := pool q.num.toNat
  refine ⟨S.image (d * ·), ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hn
    exact (hS a ha).1.trans (Nat.le_mul_of_pos_left a hd)
  · rw [sum_image (by intro a ha b hb he; exact Nat.eq_of_mul_eq_mul_left hd he)]
    calc
      _ = (∑ n ∈ S, (1 / n : ℚ)) / d := by
        rw [sum_div]
        apply sum_congr rfl
        intro n hn
        push_cast
        ring
      _ = q := by
        rw [hs]
        have hcast : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hi
        rw [hcast]
        exact Rat.num_div_den q
  · intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨v, hv, rfl⟩ := hb
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hv
    exact (hS n hn).2.trans (hS m hm).2.symm

end OMA.R_Erdos46_erdos_46_variants_positive_rat_R1
