import FormalConjectures.ErdosProblems.«669»

open Erdos669
open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos669.erdos_669.variants.upper_bound := by
  classical
  intro k n hk
  have hkpos : 0 < k.choose 2 := Nat.choose_pos hk
  have hbound : maxLinesAtLeast k n ≤ n.choose 2 / k.choose 2 := by
    refine csSup_le' ?_
    rintro _ ⟨S, rfl, rfl⟩
    refine (Nat.le_div_iff_mul_le hkpos).2 ?_
    let lines := linesWithAtLeastPointsFor k (S : Set ℝ²)
    have hfin : lines.Finite :=
      ((S.finite_toSet.prod S.finite_toSet).image fun pq : ℝ² × ℝ² => affineSpan ℝ {pq.1, pq.2}).subset
        fun _ ⟨⟨p, hp, q, hq, _, hL⟩, _⟩ => ⟨(p, q), Set.mk_mem_prod hp hq, hL⟩
    let Ls := hfin.toFinset
    let pts (L : AffineSubspace ℝ ℝ²) := S.filter (· ∈ L)
    let pairs (L : AffineSubspace ℝ ℝ²) := (pts L).powersetCard 2
    have key : ∀ L ∈ Ls, ∀ p ∈ pts L, ∀ q ∈ pts L, p ≠ q → affineSpan ℝ {p, q} = L :=
      fun L hL p hp q hq hpq => by
        obtain ⟨_, _, _, _, _, ha⟩ := (hfin.mem_toFinset.mp hL).1
        rw [← ha]; exact affineSpan_pair_eq_of_mem_of_mem_of_ne
          (ha ▸ (Finset.mem_filter.mp hp).2) (ha ▸ (Finset.mem_filter.mp hq).2) hpq
    have hdisj : (Ls : Set (AffineSubspace ℝ ℝ²)).PairwiseDisjoint pairs := fun L hL M hM hne =>
      Finset.disjoint_left.2 fun U hUL hUM => by
        obtain ⟨hUL1, hc⟩ := Finset.mem_powersetCard.mp hUL
        obtain ⟨p, q, hp, hq, hpq⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < U.card)
        have h2 := (Finset.mem_powersetCard.mp hUM).1
        exact hne ((key L hL p (hUL1 hp) q (hUL1 hq) hpq).symm.trans (key M hM p (h2 hp) q (h2 hq) hpq))
    change lines.ncard * k.choose 2 ≤ S.card.choose 2
    rw [Set.ncard_eq_toFinset_card lines hfin]
    calc Ls.card * k.choose 2 ≤ ∑ L ∈ Ls, (pairs L).card :=
          Finset.card_nsmul_le_sum _ _ _ fun L hL => by
            rw [Finset.card_powersetCard]
            refine Nat.choose_le_choose 2 ?_
            have heq : ((pts L : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ S := by ext p; simp [pts, and_comm]
            rw [← Set.ncard_coe_finset, heq]; exact (hfin.mem_toFinset.mp hL).2
      _ = (Ls.biUnion pairs).card := (Finset.card_biUnion hdisj).symm
      _ ≤ S.card.choose 2 := (Finset.card_le_card (Finset.biUnion_subset.2 fun L _ =>
          Finset.powersetCard_mono (S.filter_subset _))).trans_eq (Finset.card_powersetCard _ _)
  rw [le_div_iff₀ (by exact_mod_cast hkpos : 0 < (k.choose 2 : ℝ))]
  exact_mod_cast (Nat.le_div_iff_mul_le hkpos).mp hbound

