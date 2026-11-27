import OMAReductions.R_Erdos128_erdos_128_R2

/-!
Reduction Erdos128.erdos_128.R2.H1.R1 of step Erdos128.erdos_128.R2.H1

Step R2.H1 is the band `5n/14 ≤ δ(G) ≤ 4n/11` with `χ(G) ≥ 4`. By Jin's theorem (triangle-free graphs with
`δ > 10n/29` are 3-colourable; Jin 1995, via homomorphisms into the Andrásfai graphs And(k), k ≤ 9) the band is
empty, since `5/14 > 10/29`. This file proves the first level of that argument for all finite `n`:

* `colorable_three_of_no_v8_minus_e_band` (PROVED): a maximal triangle-free graph with `5α < 2n` and
  `35δ > 12n` (so in particular `14δ ≥ 5n`) that contains no copy of `V_8 - e` (the Möbius ladder And(3) minus a
  diagonal) is 3-colourable.
  This is the band version of Step 3 of reduction R2 (`colorable_three_of_no_v8_minus_e`, by iskamag, PR #1798,
  stated there for `11δ > 4n`); its proof is adapted here with the new degree arithmetic: a shortest odd cycle of
  `G - N(v₀)` is a 5-cycle (`50L < 350`), fewer than `2n/7` vertices miss the five classes `A_i`, and the final
  count `d(v₀) + d(z₀) ≤ Δ + #B` contradicts `35δ > 12n` and `Δ < 2n/5` (`24n/35 ≥ 2n/5 + 2n/7`). The threshold
  `12/35` lies below Jin's `10/29`, so the lemma also covers part of the band of step R2.H2.
* `grotzsch_weighted_deg_le`, `no_grotzsch_band` (PROVED): fractional-clique bound. If `o, m, z` is a homomorphic
  image of the Grötzsch graph in a triangle-free graph, then `3 ∑ d(o i) + 2 ∑ d(m i) + 4 d(z) ≤ 10 n` (the preimage
  of every neighbourhood is independent in the Grötzsch graph, whose independent sets weigh at most 10 out of 29,
  checked by `decide` over the 2^11 Boolean patterns). Hence no such image exists when `14δ ≥ 5n` (`145 n ≤ 140 n`);
  this is the source of Jin's constant 10/29. The hypotheses below get it as a premise.
* `main`: pass to a maximal triangle-free supergraph (Step 1 of R2), which keeps every hypothesis used here.

What remains is the case where the maximal supergraph contains `V_8 - e`. In the band, `V_8 - e` can no longer be
upgraded to a homomorphism onto `V_8` (Step 2 of R2 needs `11δ > 4n`): blow-ups of And(4) and And(5) contain it and
have `δ = 4n/11` and `δ = 5n/14`. Following Jin's levels, the case is split by the next Andrásfai graph And(4)
(`Z/11`, `i ~ i + 1, i + 4, i + 7, i + 10`):
* H1: the graph contains `V_8 - e` but no homomorphic image of And(4);
* H2: the graph contains a homomorphic image of And(4).
Both conclude `False` (the graph is a maximal triangle-free counterexample with `14δ ≥ 5n` that is not
3-colourable and contains no Grötzsch image). Both follow from Jin's theorem; neither is used to prove the other.
-/

-- Reduction Erdos128.erdos_128.R2.H1.R1 of step Erdos128.erdos_128.R2.H1
-- Credit: @JamesSlash
-- The band Step 3 below adapts the Step 3 proof of reduction Erdos128.erdos_128.R2 (author iskamag, PR #1798).

namespace OMA.R_Erdos128_erdos_128_R2_H1_R1

open Finset SimpleGraph OMA.R_Erdos128_erdos_128_R2

-- Band, V_8 - e present, no homomorphic image of And(4).
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.CliqueFree 3 →
    (∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    (∀ v : V, 5 * Fintype.card V ≤ 14 * (G.neighborSet v).ncard) →
    ¬ G.Colorable 3 →
    (¬ ∃ (o m : Fin 5 → V) (z : V), ∀ i : Fin 5, G.Adj (o i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 1)) ∧
      G.Adj (m i) (o (i + 4)) ∧ G.Adj z (m i)) →
    (∃ v : Fin 8 → V, ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
      ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → G.Adj (v i) (v j)) →
    (¬ ∃ φ : Fin 11 → V, ∀ i j : Fin 11, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7 ∨ j = i + 10) →
      G.Adj (φ i) (φ j)) →
    False

-- Band, homomorphic image of And(4) present.
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.CliqueFree 3 →
    (∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    (∀ v : V, 5 * Fintype.card V ≤ 14 * (G.neighborSet v).ncard) →
    ¬ G.Colorable 3 →
    (¬ ∃ (o m : Fin 5 → V) (z : V), ∀ i : Fin 5, G.Adj (o i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 1)) ∧
      G.Adj (m i) (o (i + 4)) ∧ G.Adj z (m i)) →
    (∃ φ : Fin 11 → V, ∀ i j : Fin 11, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7 ∨ j = i + 10) →
      G.Adj (φ i) (φ j)) →
    False

/-- Band Step 3 (adapted from `colorable_three_of_no_v8_minus_e` of reduction R2, iskamag, PR #1798):
    maximal triangle-free + `5α < 2n` + `35δ > 12n` + no `V_8 - (2, 6)` implies 3-colourable. -/
theorem colorable_three_of_no_v8_minus_e_band {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h5a : ∀ I : Finset V, (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) → 5 * #I < 2 * Fintype.card V)
    (h35d : ∀ x : V, 12 * Fintype.card V < 35 * (G.neighborSet x).ncard)
    (hnoV8 : ¬ ∃ v : Fin 8 → V, ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
      ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → G.Adj (v i) (v j))
    (hshort_walk : ∀ (W : Type) [Fintype W] (H : SimpleGraph W),
      H.CliqueFree 3 → ¬ H.Colorable 2 →
      ∃ L : ℕ, Odd L ∧ 5 ≤ L ∧
        (∀ L' < L, Odd L' → ¬ ∃ g : ℕ → W, g L' = g 0 ∧ ∀ i < L', H.Adj (g i) (g (i + 1))) ∧
        ∃ f : ℕ → W, f L = f 0 ∧ (∀ i < L, H.Adj (f i) (f (i + 1))) ∧
          (∀ i j, i < j → j < L → f i ≠ f j) ∧
          (∀ i j, i + 2 ≤ j → j < L → j - i ≤ L - 2 → ¬ H.Adj (f i) (f j)))
    (hshort_deg2 : ∀ (W : Type) [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      H.CliqueFree 3 → ∀ {L : ℕ}, Odd L → 5 ≤ L →
      (∀ L' < L, Odd L' → ¬ ∃ g : ℕ → W, g L' = g 0 ∧ ∀ i < L', H.Adj (g i) (g (i + 1))) →
      ∀ {f : ℕ → W}, f L = f 0 → (∀ i < L, H.Adj (f i) (f (i + 1))) →
      ∀ w : W, #((Finset.range L).filter (fun i => H.Adj w (f i))) ≤ 2) :
    G.Colorable 3 := by
  classical
  by_contra hnot3
  set n := Fintype.card V
  have hn_pos : 0 < n := by
    by_contra h0
    have hE : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
    exact hnot3 ⟨SimpleGraph.Coloring.mk (fun x => (hE.false x).elim)
      (fun {a _} _ => (hE.false a).elim)⟩
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hn_pos
  have hdeg : ∀ x : V, 12 * n < 35 * #(Finset.univ.filter (G.Adj x)) := by
    intro x
    have h1 := h35d x
    rw [Set.ncard_eq_toFinset_card'] at h1
    have h2 : (G.neighborSet x).toFinset = Finset.univ.filter (G.Adj x) := by ext y; simp
    rwa [h2] at h1
  have hdeg_up : ∀ x : V, 5 * #(Finset.univ.filter (G.Adj x)) < 2 * n := fun x =>
    h5a _ (fun u hu v hv huv => not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp hu).2 huv
      (Finset.mem_filter.mp hv).2)
  -- Substep 3a: Pick a shortest odd cycle C of length L in G - N(v₀); force L = 5
  let I : Finset V := Finset.univ.filter (G.Adj v₀)
  have h5I : 5 * #I < 2 * n := hdeg_up v₀
  let S : Set V := {w : V | w ∉ I}
  let H : SimpleGraph S := G.induce S
  have hH_TF : H.CliqueFree 3 := by
    intro t ht
    apply hTF (t.image Subtype.val)
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact ht.1 ha hb (fun hab => hxy (congrArg Subtype.val hab))
    · rw [Finset.card_image_of_injective _ Subtype.val_injective, ht.2]
  have hH_not2 : ¬ H.Colorable 2 := by
    rintro ⟨c2⟩
    apply hnot3
    refine ⟨SimpleGraph.Coloring.mk (fun w =>
      if hw : w ∈ I then (2 : Fin 3) else ⟨(c2 ⟨w, hw⟩).val, by have := (c2 ⟨w, hw⟩).isLt; omega⟩) ?_⟩
    intro a b hab
    by_cases ha : a ∈ I <;> by_cases hb : b ∈ I
    · exfalso
      exact not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp ha).2 hab (Finset.mem_filter.mp hb).2
    · simp only [ha, hb, dite_true, dite_false]
      intro heq
      have hval := congrArg Fin.val heq
      have hlt := (c2 ⟨b, hb⟩).isLt
      dsimp only at hval; omega
    · simp only [ha, hb, dite_true, dite_false]
      intro heq
      have hval := congrArg Fin.val heq
      have hlt := (c2 ⟨a, ha⟩).isLt
      dsimp only at hval; omega
    · simp only [ha, hb, dite_false]
      intro heq
      have hval := congrArg Fin.val heq
      dsimp only at hval
      exact c2.valid (show H.Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab) (Fin.ext hval)
  obtain ⟨L, hL_odd, hL5, hL_min, fH, hfH_loop, hfH_adj, _, _⟩ := hshort_walk S H hH_TF hH_not2
  let f : ℕ → V := fun i => (fH i).val
  have hf_loop : f L = f 0 := congrArg Subtype.val hfH_loop
  have hf_adj : ∀ i < L, G.Adj (f i) (f (i + 1)) := fun i hi => hfH_adj i hi
  have hf_notI : ∀ i : ℕ, f i ∉ I := fun i => (fH i).property
  have hL_eq5 : L = 5 := by
    have hdeg_out : ∀ w : V, w ∉ I → #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ 2 := fun w hw =>
      hshort_deg2 S H hH_TF hL_odd hL5 hL_min hfH_loop hfH_adj ⟨w, hw⟩
    have hdeg_in : ∀ w : V, 2 * #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ L - 1 := by
      intro w
      set T := (Finset.range L).filter (fun i => G.Adj w (f i))
      have hinj : Set.InjOn (fun i : ℕ => (i + 1) % L) (T : Set ℕ) := by
        intro a ha b hb heq
        dsimp only at heq
        have haL := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have hbL := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        by_cases ha1 : a + 1 < L <;> by_cases hb1 : b + 1 < L
        · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at heq; omega
        · rw [Nat.mod_eq_of_lt ha1, show b + 1 = L by omega, Nat.mod_self] at heq; omega
        · rw [show a + 1 = L by omega, Nat.mod_self, Nat.mod_eq_of_lt hb1] at heq; omega
        · omega
      have hdisj : Disjoint T (T.image (fun i => (i + 1) % L)) := by
        rw [Finset.disjoint_left]
        intro j hjT hjIm
        obtain ⟨i, hiT, rfl⟩ := Finset.mem_image.mp hjIm
        have hiL := Finset.mem_range.mp (Finset.mem_filter.mp hiT).1
        have hwi := (Finset.mem_filter.mp hiT).2
        have hwj := (Finset.mem_filter.mp hjT).2
        by_cases hi1 : i + 1 < L
        · rw [Nat.mod_eq_of_lt hi1] at hwj
          exact not_adj_of_cliqueFree_three hTF hwi (hf_adj i hiL) hwj
        · rw [show i + 1 = L by omega, Nat.mod_self] at hwj
          have hadj := hf_adj i hiL
          rw [show i + 1 = L by omega, hf_loop] at hadj
          exact not_adj_of_cliqueFree_three hTF hwi hadj hwj
      have hsub : T ∪ T.image (fun i => (i + 1) % L) ⊆ Finset.range L := by
        refine Finset.union_subset (Finset.filter_subset _ _) ?_
        intro j hj
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
      have h2T : 2 * #T ≤ L := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj, Finset.card_range] at h1
        omega
      obtain ⟨m, hm⟩ := hL_odd
      omega
    have hsum_swap : ∑ i ∈ Finset.range L, #(Finset.univ.filter (G.Adj (f i))) =
        ∑ w : V, #((Finset.range L).filter (fun i => G.Adj w (f i))) := by
      simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro w _
      apply Finset.sum_congr rfl; intro i _; simp [G.adj_comm]
    have hsum_up : 2 * ∑ i ∈ Finset.range L, #(Finset.univ.filter (G.Adj (f i))) ≤
        4 * (n - #I) + (L - 1) * #I := by
      rw [hsum_swap]
      have hpart : ∑ w : V, #((Finset.range L).filter (fun i => G.Adj w (f i))) =
          ∑ w ∈ Finset.univ \ I, #((Finset.range L).filter (fun i => G.Adj w (f i))) +
          ∑ w ∈ I, #((Finset.range L).filter (fun i => G.Adj w (f i))) := by
        rw [← Finset.sum_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset (Finset.subset_univ I)]
      have h1 : ∑ w ∈ Finset.univ \ I, #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ 2 * (n - #I) := by
        calc _ ≤ ∑ _w ∈ Finset.univ \ I, 2 := Finset.sum_le_sum (fun w hw => hdeg_out w (Finset.mem_sdiff.mp hw).2)
          _ = #(Finset.univ \ I) * 2 := by rw [Finset.sum_const, smul_eq_mul]
          _ = 2 * (n - #I) := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ, mul_comm]
      have h2 : 2 * ∑ w ∈ I, #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ (L - 1) * #I := by
        rw [Finset.mul_sum]
        calc _ ≤ ∑ _w ∈ I, (L - 1) := Finset.sum_le_sum (fun w _ => hdeg_in w)
          _ = (L - 1) * #I := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      omega
    have hsum_lo : 12 * n * L < 35 * ∑ i ∈ Finset.range L, #(Finset.univ.filter (G.Adj (f i))) := by
      rw [Finset.mul_sum]
      have hlt := Finset.sum_lt_sum_of_nonempty (s := Finset.range L) (by rw [Finset.nonempty_range_iff]; omega)
        (fun i _ => hdeg (f i))
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm] at hlt
      exact hlt
    have hI_le : #I ≤ n := (Finset.card_le_card (Finset.subset_univ I)).trans (by simp [n])
    have h4n : 4 * (n - #I) + (L - 1) * #I = 4 * n + (L - 5) * #I := by
      zify [hI_le, hL5, show 1 ≤ L by omega]; ring
    rw [h4n] at hsum_up
    have hcomb : 120 * n * L < 700 * n + 35 * (L - 5) * (2 * n) := by
      have hmul : (L - 5) * (5 * #I) ≤ (L - 5) * (2 * n) := Nat.mul_le_mul_left (L - 5) (by omega)
      nlinarith only [hsum_lo, hsum_up, hmul]
    have hLlt : 120 * L < 700 + 70 * (L - 5) := by nlinarith only [hcomb, hn_pos]
    obtain ⟨m, hm⟩ := hL_odd
    omega
  -- Helper: build a V_8 - (2, 6) contradiction from 8 vertices and 11 edges
  have hV8_contra : ∀ (u0 u1 u2 u3 u4 u5 u6 u7 : V),
      G.Adj u0 u1 → G.Adj u1 u2 → G.Adj u2 u3 → G.Adj u3 u4 →
      G.Adj u4 u5 → G.Adj u5 u6 → G.Adj u6 u7 → G.Adj u7 u0 →
      G.Adj u0 u4 → G.Adj u1 u5 → G.Adj u3 u7 → False :=
    fun u0 u1 u2 u3 u4 u5 u6 u7 e01 e12 e23 e34 e45 e56 e67 e70 e04 e15 e37 =>
      hnoV8 (exists_v8_minus_e_of_edges u0 u1 u2 u3 u4 u5 u6 u7 e01 e12 e23 e34 e45 e56 e67 e70 e04 e15 e37)
  -- Shared bound: for any 5-cycle c, the set B of vertices outside A_0 ∪ ... ∪ A_4 has 7 * #B < 2 * n
  have hB_bound_any : ∀ (c : Fin 5 → V), (∀ i : Fin 5, G.Adj (c i) (c (i + 1))) →
      7 * #(Finset.univ.filter (fun w => ∀ i : Fin 5, ¬ (G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4))))) < 2 * n := by
    intro c hc_adj
    let B : Finset V := Finset.univ.filter (fun w => ∀ i : Fin 5, ¬ (G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4))))
    have hpt : ∀ w : V, (if w ∈ B then 1 else 0) + #(Finset.univ.filter (fun i : Fin 5 => G.Adj w (c i))) ≤ 2 := by
      intro w
      let b : Fin 5 → ℕ := fun i => if G.Adj w (c i) then 1 else 0
      have hcard : #(Finset.univ.filter (fun i : Fin 5 => G.Adj w (c i))) =
          b 0 + b 1 + b 2 + b 3 + b 4 := by rw [Finset.card_filter, Fin.sum_univ_five]
      rw [hcard]
      have hna : ∀ i : Fin 5, b i + b (i + 1) ≤ 1 := by
        intro i; dsimp only [b]
        by_cases h1 : G.Adj w (c i) <;> by_cases h2 : G.Adj w (c (i + 1))
        · exact (not_adj_of_cliqueFree_three hTF h1 (hc_adj i) h2).elim
        all_goals simp [h1, h2]
      have h01 : b 0 + b 1 ≤ 1 := hna 0
      have h12 : b 1 + b 2 ≤ 1 := hna 1
      have h23 : b 2 + b 3 ≤ 1 := hna 2
      have h34 : b 3 + b 4 ≤ 1 := hna 3
      have h40 : b 4 + b 0 ≤ 1 := hna 4
      by_cases hwB : w ∈ B
      · simp only [hwB, if_true]
        have hnotA : ∀ i : Fin 5, b (i + 1) + b (i + 4) ≤ 1 := by
          intro i; dsimp only [b]
          by_cases h1 : G.Adj w (c (i + 1)) <;> by_cases h2 : G.Adj w (c (i + 4))
          · exfalso; exact (Finset.mem_filter.mp hwB).2 i ⟨h1, h2⟩
          all_goals simp [h1, h2]
        have : b 1 + b 4 ≤ 1 := hnotA 0
        have : b 2 + b 0 ≤ 1 := hnotA 1
        have : b 3 + b 1 ≤ 1 := hnotA 2
        have : b 4 + b 2 ≤ 1 := hnotA 3
        have : b 0 + b 3 ≤ 1 := hnotA 4
        omega
      · simp only [hwB, if_false, zero_add]; omega
    have hsum_le : #B + ∑ i : Fin 5, #(Finset.univ.filter (G.Adj (c i))) ≤ 2 * n := by
      have h1 : ∑ w : V, ((if w ∈ B then 1 else 0) + #(Finset.univ.filter (fun i : Fin 5 => G.Adj w (c i)))) ≤ 2 * n := by
        calc _ ≤ ∑ _w : V, 2 := Finset.sum_le_sum (fun w _ => hpt w)
          _ = 2 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      have h2 : ∑ w : V, ((if w ∈ B then 1 else 0) + #(Finset.univ.filter (fun i : Fin 5 => G.Adj w (c i)))) =
          #B + ∑ i : Fin 5, #(Finset.univ.filter (G.Adj (c i))) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        · simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
      omega
    have hsum_gt : 60 * n < 35 * ∑ i : Fin 5, #(Finset.univ.filter (G.Adj (c i))) := by
      rw [Finset.mul_sum]
      have hlt := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 5))) (by simp)
        (fun i _ => hdeg (c i))
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
      omega
    change 7 * #B < 2 * n
    omega
  -- Helper: for ANY 5-cycle c avoiding N(v₀), prove (P1), (P2) and finish when v₀ hits A_r & avoids A_{r+3}!
  have hfinish : ∀ (c : Fin 5 → V), (∀ i : Fin 5, G.Adj (c i) (c (i + 1))) →
      (∀ i : Fin 5, ¬ G.Adj v₀ (c i)) →
      ∀ (r : Fin 5) (w₀ : V), G.Adj w₀ (c (r + 1)) → G.Adj w₀ (c (r + 4)) → G.Adj v₀ w₀ →
      (∀ w : V, G.Adj w (c (r + 4)) → G.Adj w (c (r + 2)) → ¬ G.Adj v₀ w) → False := by
    intro c hc_adj hv0_c r w₀ hw01 hw04 hv0w0 hno_r3
    let A : Fin 5 → Finset V := fun i => Finset.univ.filter (fun w => G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4)))
    let B : Finset V := Finset.univ.filter (fun w => ∀ i : Fin 5, ¬ (G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4))))
    have hB_bound : 7 * #B < 2 * n := hB_bound_any c hc_adj
    -- (P1): No vertex x hits both A i and A (i + 1)
    have hP1 : ∀ (i : Fin 5) (x y1 y2 : V), y1 ∈ A i → y2 ∈ A (i + 1) →
        G.Adj x y1 → G.Adj x y2 → False := by
      intro i x y1 y2 hy1 hy2 hxy1 hxy2
      have ⟨h1a, h1b⟩ := (Finset.mem_filter.mp hy1).2
      have ⟨h2a, h2b⟩ := (Finset.mem_filter.mp hy2).2
      rw [fin5_add_1_1] at h2a
      rw [fin5_add_1_4] at h2b
      have e45 : G.Adj (c (i + 1)) (c (i + 2)) := by have h := hc_adj (i + 1); rwa [fin5_add_1_1] at h
      have e56 : G.Adj (c (i + 2)) (c (i + 3)) := by have h := hc_adj (i + 2); rwa [fin5_add_2_1] at h
      have e67 : G.Adj (c (i + 3)) (c (i + 4)) := by have h := hc_adj (i + 3); rwa [fin5_add_3_1] at h
      have e70 : G.Adj (c (i + 4)) (c i) := by have h := hc_adj (i + 4); rwa [fin5_add_4_1] at h
      exact hV8_contra (c i) y2 x y1 (c (i + 1)) (c (i + 2)) (c (i + 3)) (c (i + 4))
        h2b.symm hxy2.symm hxy1 h1a e45 e56 e67 e70 (hc_adj i) h2a h1b
    -- (P2): No edge (a, b) with a hitting A (i + 4) and A (i + 1) and b hitting A (i + 1)
    have hP2 : ∀ (i : Fin 5) (a b u v' y : V), u ∈ A (i + 4) → v' ∈ A (i + 1) → y ∈ A (i + 1) →
        G.Adj a u → G.Adj a v' → G.Adj a b → G.Adj b y → False := by
      intro i a b u v' y hu hv' hy hau hav' hab hby
      have ⟨hua, hub⟩ := (Finset.mem_filter.mp hu).2
      have ⟨hva, hvb⟩ := (Finset.mem_filter.mp hv').2
      have ⟨hya, hyb⟩ := (Finset.mem_filter.mp hy).2
      rw [fin5_add_4_1] at hua
      rw [fin5_add_4_4] at hub
      rw [fin5_add_1_1] at hva hya
      rw [fin5_add_1_4] at hvb hyb
      have e23 : G.Adj (c (i + 3)) (c (i + 2)) := by have h := (hc_adj (i + 2)).symm; rwa [fin5_add_2_1] at h
      exact hV8_contra (c i) u (c (i + 3)) (c (i + 2)) v' a b y
        hua.symm hub e23 hva.symm hav'.symm hab hby hyb hvb.symm hau.symm hya.symm
    -- Pick common neighbor z₀ of v₀ and c r via maximality
    have hv0_ne : v₀ ≠ c r := by
      intro heq; rw [heq] at hv0_c; exact hv0_c (r + 1) (hc_adj r)
    obtain ⟨z₀, hv0z0, hcrz0⟩ := hmax v₀ (c r) hv0_ne (hv0_c r)
    have hcrA : c r ∈ A r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_adj r, by
      have h := (hc_adj (r + 4)).symm; rwa [fin5_add_4_1] at h⟩
    have hw0A : w₀ ∈ A r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw01, hw04⟩
    have hw0A4 : w₀ ∈ A (r + 4 + 1) := by rw [fin5_add_4_1]; exact hw0A
    have hcrA4 : c r ∈ A (r + 4 + 1) := by rw [fin5_add_4_1]; exact hcrA
    -- Both N(v₀) and N(z₀) lie inside N(c (r + 1)) ∪ B!
    have hsub_v0 : Finset.univ.filter (G.Adj v₀) ⊆ Finset.univ.filter (G.Adj (c (r + 1))) ∪ B := by
      intro w hw
      have hv0w := (Finset.mem_filter.mp hw).2
      by_cases hwB : w ∈ B
      · exact Finset.mem_union_right _ hwB
      · have hexA : ∃ j : Fin 5, w ∈ A j := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => hnone j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩)
        obtain ⟨j, hwAj⟩ := hexA
        rcases fin5_cases_rel r j with rfl | rfl | rfl | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hwAj).2.1.symm⟩)
        · exact (hP1 r v₀ w₀ w hw0A hwAj hv0w0 hv0w).elim
        · have h2 := (Finset.mem_filter.mp hwAj).2.2
          rw [fin5_add_2_4] at h2
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.symm⟩)
        · have ⟨h3a, h3b⟩ := (Finset.mem_filter.mp hwAj).2
          rw [fin5_add_3_1] at h3a
          rw [fin5_add_3_4] at h3b
          exact (hno_r3 w h3a h3b hv0w).elim
        · exact (hP1 (r + 4) v₀ w w₀ hwAj hw0A4 hv0w hv0w0).elim
    have hsub_z0 : Finset.univ.filter (G.Adj z₀) ⊆ Finset.univ.filter (G.Adj (c (r + 1))) ∪ B := by
      intro w hw
      have hz0w := (Finset.mem_filter.mp hw).2
      by_cases hwB : w ∈ B
      · exact Finset.mem_union_right _ hwB
      · have hexA : ∃ j : Fin 5, w ∈ A j := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => hnone j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩)
        obtain ⟨j, hwAj⟩ := hexA
        rcases fin5_cases_rel r j with rfl | rfl | rfl | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hwAj).2.1.symm⟩)
        · exact (hP1 r z₀ (c r) w hcrA hwAj hcrz0.symm hz0w).elim
        · have h2 := (Finset.mem_filter.mp hwAj).2.2
          rw [fin5_add_2_4] at h2
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.symm⟩)
        · have hwA4 : w ∈ A (r + 4 + 4) := by rw [fin5_add_4_4]; exact hwAj
          exact (hP2 (r + 4) z₀ v₀ w (c r) w₀ hwA4 hcrA4 hw0A4 hz0w hcrz0.symm hv0z0.symm hv0w0).elim
        · exact (hP1 (r + 4) z₀ w (c r) hwAj hcrA4 hz0w hcrz0.symm).elim
    have hdisj_vz : Disjoint (Finset.univ.filter (G.Adj v₀)) (Finset.univ.filter (G.Adj z₀)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      exact not_adj_of_cliqueFree_three hTF hv0z0 (Finset.mem_filter.mp hw2).2 (Finset.mem_filter.mp hw1).2
    have hcard_sum : #(Finset.univ.filter (G.Adj v₀)) + #(Finset.univ.filter (G.Adj z₀)) ≤
        #(Finset.univ.filter (G.Adj (c (r + 1)))) + #B := by
      rw [← Finset.card_union_of_disjoint hdisj_vz]
      exact (Finset.card_le_card (Finset.union_subset hsub_v0 hsub_z0)).trans (Finset.card_union_le _ _)
    have hd_v0 := hdeg v₀
    have hd_z0 := hdeg z₀
    have hd_up := hdeg_up (c (r + 1))
    omega
  -- Instantiate c : Fin 5 -> V from the shortest 5-cycle f
  let c : Fin 5 → V := fun i => f i.val
  have hc_adj : ∀ i : Fin 5, G.Adj (c i) (c (i + 1)) := by
    intro i; fin_cases i
    · exact hf_adj 0 (by omega)
    · exact hf_adj 1 (by omega)
    · exact hf_adj 2 (by omega)
    · exact hf_adj 3 (by omega)
    · have h4 := hf_adj 4 (by omega)
      rw [show 4 + 1 = L by omega, hf_loop] at h4
      exact h4
  have hv0_c : ∀ i : Fin 5, ¬ G.Adj v₀ (c i) := fun i h =>
    hf_notI i.val (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  -- Either v₀ hits some A_r (then orient c so v₀ avoids A_{r+3}) or N(v₀) ⊆ B (contradicting 7 * #B < 2n)!
  by_cases hex : ∃ (r : Fin 5) (w₀ : V), G.Adj w₀ (c (r + 1)) ∧ G.Adj w₀ (c (r + 4)) ∧ G.Adj v₀ w₀
  · obtain ⟨r, w₀, hw01, hw04, hv0w0⟩ := hex
    by_cases hhit3 : ∃ w₃ : V, G.Adj w₃ (c (r + 4)) ∧ G.Adj w₃ (c (r + 2)) ∧ G.Adj v₀ w₃
    · -- v₀ hits A_{r+3}, so by (P1) it avoids A_{r+2}; reverse c to c'(k) := c(-k)!
      obtain ⟨w₃, hw34, hw32, hv0w3⟩ := hhit3
      let c' : Fin 5 → V := fun k => c (-k)
      have hc'_adj : ∀ k : Fin 5, G.Adj (c' k) (c' (k + 1)) := fun k => by
        dsimp only [c']
        have h := (hc_adj (-(k + 1))).symm
        rwa [fin5_neg_add] at h
      have hv0_c' : ∀ k : Fin 5, ¬ G.Adj v₀ (c' k) := fun k => hv0_c (-k)
      apply hfinish c' hc'_adj hv0_c' (-r) w₀
        (by dsimp only [c']; rwa [fin5_neg_neg_1])
        (by dsimp only [c']; rwa [fin5_neg_neg_4])
        hv0w0
      intro w hw1 hw2 hv0w
      dsimp only [c'] at hw1 hw2
      rw [fin5_neg_neg_4] at hw1
      rw [fin5_neg_neg_2] at hw2
      have e45 : G.Adj (c (r + 3)) (c (r + 4)) := by have h := hc_adj (r + 3); rwa [fin5_add_3_1] at h
      have e56 : G.Adj (c (r + 4)) (c r) := by have h := hc_adj (r + 4); rwa [fin5_add_4_1] at h
      have e70 : G.Adj (c (r + 1)) (c (r + 2)) := by have h := hc_adj (r + 1); rwa [fin5_add_1_1] at h
      have e04 : G.Adj (c (r + 2)) (c (r + 3)) := by have h := hc_adj (r + 2); rwa [fin5_add_2_1] at h
      exact hV8_contra (c (r + 2)) w₃ v₀ w (c (r + 3)) (c (r + 4)) (c r) (c (r + 1))
        hw32.symm hv0w3.symm hv0w hw2 e45 e56 (hc_adj r) e70 e04 hw34 hw1
    · push Not at hhit3
      exact hfinish c hc_adj hv0_c r w₀ hw01 hw04 hv0w0 hhit3
  · -- N(v₀) ⊆ B, contradicting 12n < 35 * d(v₀) ≤ 35 * #B < 10n!
    push Not at hex
    have hB_bound := hB_bound_any c hc_adj
    have hsubB : Finset.univ.filter (G.Adj v₀) ⊆
        Finset.univ.filter (fun w => ∀ i : Fin 5, ¬ (G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4)))) := by
      intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i ⟨h1, h2⟩ => hex i w h1 h2 (Finset.mem_filter.mp hw).2⟩
    have hleB := Finset.card_le_card hsubB
    have hdv0 := hdeg v₀
    omega

/-- The Grötzsch independent-set weight bound as a finite Boolean check (2^11 cases, kernel `decide`):
    weights 3 (outer 5-cycle), 2 (inner vertices), 4 (apex); every independent set weighs at most 10. -/
theorem grotzsch_bool : ∀ s0 s1 s2 s3 s4 t0 t1 t2 t3 t4 u : Bool,
    (!(s0 && s1) && !(s1 && s2) && !(s2 && s3) && !(s3 && s4) && !(s4 && s0) &&
     !(t0 && s1) && !(t0 && s4) && !(t1 && s2) && !(t1 && s0) && !(t2 && s3) && !(t2 && s1) &&
     !(t3 && s4) && !(t3 && s2) && !(t4 && s0) && !(t4 && s3) &&
     !(u && t0) && !(u && t1) && !(u && t2) && !(u && t3) && !(u && t4)) = true →
    3 * (s0.toNat + s1.toNat + s2.toNat + s3.toNat + s4.toNat) +
      2 * (t0.toNat + t1.toNat + t2.toNat + t3.toNat + t4.toNat) + 4 * u.toNat ≤ 10 := by
  decide

/-- Fractional-clique bound for a homomorphic image of the Grötzsch graph (outer 5-cycle `o`, inner `m i ~ o (i ± 1)`,
    apex `z ~ m i`) in a triangle-free graph: `3 ∑ d(o i) + 2 ∑ d(m i) + 4 d(z) ≤ 10 n`. -/
theorem grotzsch_weighted_deg_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) (o m : Fin 5 → V) (z : V)
    (h : ∀ i : Fin 5, G.Adj (o i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 4)) ∧
      G.Adj z (m i)) :
    3 * ∑ i, #(univ.filter (G.Adj (o i))) + 2 * ∑ i, #(univ.filter (G.Adj (m i))) +
      4 * #(univ.filter (G.Adj z)) ≤ 10 * Fintype.card V := by
  classical
  have e01 : G.Adj (o 0) (o 1) := (h 0).1
  have e12 : G.Adj (o 1) (o 2) := (h 1).1
  have e23 : G.Adj (o 2) (o 3) := (h 2).1
  have e34 : G.Adj (o 3) (o 4) := (h 3).1
  have e40 : G.Adj (o 4) (o 0) := (h 4).1
  have a01 : G.Adj (m 0) (o 1) := (h 0).2.1
  have a04 : G.Adj (m 0) (o 4) := (h 0).2.2.1
  have a12 : G.Adj (m 1) (o 2) := (h 1).2.1
  have a10 : G.Adj (m 1) (o 0) := (h 1).2.2.1
  have a23 : G.Adj (m 2) (o 3) := (h 2).2.1
  have a21 : G.Adj (m 2) (o 1) := (h 2).2.2.1
  have a34 : G.Adj (m 3) (o 4) := (h 3).2.1
  have a32 : G.Adj (m 3) (o 2) := (h 3).2.2.1
  have a40 : G.Adj (m 4) (o 0) := (h 4).2.1
  have a43 : G.Adj (m 4) (o 3) := (h 4).2.2.1
  have z0 : G.Adj z (m 0) := (h 0).2.2.2
  have z1 : G.Adj z (m 1) := (h 1).2.2.2
  have z2 : G.Adj z (m 2) := (h 2).2.2.2
  have z3 : G.Adj z (m 3) := (h 3).2.2.2
  have z4 : G.Adj z (m 4) := (h 4).2.2.2
  have hx : ∀ x : V, 3 * ∑ i, (if G.Adj (o i) x then 1 else 0) + 2 * ∑ i, (if G.Adj (m i) x then 1 else 0) +
      4 * (if G.Adj z x then 1 else 0) ≤ 10 := by
    intro x
    have hp : ∀ p q : V, G.Adj p q → (decide (G.Adj p x) && decide (G.Adj q x)) = false := by
      intro p q hpq
      by_cases hpx : G.Adj p x <;> by_cases hqx : G.Adj q x
      · exact (hTF {p, q, x} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hpq, hpx, hqx⟩)).elim
      all_goals simp [hpx, hqx]
    have key := grotzsch_bool (decide (G.Adj (o 0) x)) (decide (G.Adj (o 1) x)) (decide (G.Adj (o 2) x))
      (decide (G.Adj (o 3) x)) (decide (G.Adj (o 4) x)) (decide (G.Adj (m 0) x)) (decide (G.Adj (m 1) x))
      (decide (G.Adj (m 2) x)) (decide (G.Adj (m 3) x)) (decide (G.Adj (m 4) x)) (decide (G.Adj z x))
      (by rw [hp _ _ e01, hp _ _ e12, hp _ _ e23, hp _ _ e34, hp _ _ e40, hp _ _ a01, hp _ _ a04, hp _ _ a12,
            hp _ _ a10, hp _ _ a23, hp _ _ a21, hp _ _ a34, hp _ _ a32, hp _ _ a40, hp _ _ a43, hp _ _ z0,
            hp _ _ z1, hp _ _ z2, hp _ _ z3, hp _ _ z4]; rfl)
    have conv : ∀ p : V, (if G.Adj p x then 1 else 0) = (decide (G.Adj p x)).toNat := fun p => by
      by_cases hpx : G.Adj p x <;> simp [hpx]
    simp only [Fin.sum_univ_five, conv]
    exact key
  have hdeg : ∀ p : V, #(univ.filter (G.Adj p)) = ∑ x, (if G.Adj p x then 1 else 0) := fun p => by
    rw [Finset.card_filter]
  have hsum : 3 * ∑ i, #(univ.filter (G.Adj (o i))) + 2 * ∑ i, #(univ.filter (G.Adj (m i))) +
      4 * #(univ.filter (G.Adj z)) = ∑ x : V, (3 * ∑ i, (if G.Adj (o i) x then 1 else 0) +
        2 * ∑ i, (if G.Adj (m i) x then 1 else 0) + 4 * (if G.Adj z x then 1 else 0)) := by
    simp_rw [hdeg]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_comm (f := fun i x => if G.Adj (o i) x then 1 else 0),
      Finset.sum_comm (f := fun i x => if G.Adj (m i) x then 1 else 0)]
  rw [hsum]
  calc _ ≤ ∑ _x : V, 10 := Finset.sum_le_sum (fun x _ => hx x)
    _ = 10 * Fintype.card V := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- In the band `14 δ ≥ 5 n` there is no homomorphic image of the Grötzsch graph (`χ_f = 29/10 > 14/5`). -/
theorem no_grotzsch_band {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3) (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * (G.neighborSet v).ncard)
    (o m : Fin 5 → V) (z : V)
    (h : ∀ i : Fin 5, G.Adj (o i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 4)) ∧
      G.Adj z (m i)) : False := by
  classical
  have hdeg : ∀ x : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj x)) := by
    intro x
    have h1 := h14 x
    rw [Set.ncard_eq_toFinset_card'] at h1
    have h2 : (G.neighborSet x).toFinset = univ.filter (G.Adj x) := by ext y; simp
    rwa [h2] at h1
  have hW := grotzsch_weighted_deg_le G hTF o m z h
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨z⟩
  simp only [Fin.sum_univ_five] at hW
  have d0 := hdeg (o 0); have d1 := hdeg (o 1); have d2 := hdeg (o 2); have d3 := hdeg (o 3)
  have d4 := hdeg (o 4); have d5 := hdeg (m 0); have d6 := hdeg (m 1); have d7 := hdeg (m 2)
  have d8 := hdeg (m 3); have d9 := hdeg (m 4); have d10 := hdeg z
  linarith

theorem main : H1 → H2 → OMA.R_Erdos128_erdos_128_R2.H1 := by
  intro h1 h2 V _ G _hn12 _h73 _h500 h5a _hC4 _hC5 _h2K2 hnot3 h14 _h11 hH hTF
  classical
  obtain ⟨M, hGM, hMTF, hMmax⟩ := exists_maximal_triangleFree G hTF
  have hMH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (M.induce V').edgeSet.ncard > Fintype.card V ^ 2 := by
    intro V' hV'
    have hG' := hH V' hV'
    have hsub : (G.induce V').edgeSet ⊆ (M.induce V').edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ a b => exact hGM he
    have hle : (G.induce V').edgeSet.ncard ≤ (M.induce V').edgeSet.ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hM14 : ∀ x : V, 5 * Fintype.card V ≤ 14 * (M.neighborSet x).ncard := by
    intro x
    have h1x := h14 x
    have hle : (G.neighborSet x).ncard ≤ (M.neighborSet x).ncard :=
      Set.ncard_le_ncard (fun y hy => hGM hy) (Set.toFinite _)
    omega
  have hMnot3 : ¬ M.Colorable 3 := fun hc => hnot3 (hc.mono_left hGM)
  have hnoG : ¬ ∃ (o m : Fin 5 → V) (z : V), ∀ i : Fin 5, M.Adj (o i) (o (i + 1)) ∧ M.Adj (m i) (o (i + 1)) ∧
      M.Adj (m i) (o (i + 4)) ∧ M.Adj z (m i) :=
    fun ⟨o, m, z, h⟩ => no_grotzsch_band M hMTF hM14 o m z h
  by_cases hV8 : ∃ v : Fin 8 → V, ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
      ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → M.Adj (v i) (v j)
  · by_cases hA4 : ∃ φ : Fin 11 → V, ∀ i j : Fin 11, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7 ∨ j = i + 10) →
        M.Adj (φ i) (φ j)
    · exact h2 V M hMTF hMmax hMH hM14 hMnot3 hnoG hA4
    · exact h1 V M hMTF hMmax hMH hM14 hMnot3 hnoG hV8 hA4
  · have hM5a : ∀ I : Finset V, (∀ u ∈ I, ∀ v ∈ I, ¬ M.Adj u v) → 5 * #I < 2 * Fintype.card V := by
      intro I hI
      have h1I := h5a (I : Set V)
        (fun u hu v hv _ hG => hI u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv) (hGM hG))
      rwa [Set.ncard_coe_finset] at h1I
    have hM35 : ∀ x : V, 12 * Fintype.card V < 35 * (M.neighborSet x).ncard := by
      intro x
      have h1x := hM14 x
      have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
      omega
    exact hMnot3 (colorable_three_of_no_v8_minus_e_band M hMTF hMmax hM5a hM35 hV8
      (fun _ _ H h1 h2 => exists_shortest_odd_walk_of_nonbip H h1 h2)
      (fun _ _ H _ h1 {_} h2 h3 h4 {_} h5 h6 w => shortest_odd_walk_deg_le_two H h1 h2 h3 h4 h5 h6 w))

end OMA.R_Erdos128_erdos_128_R2_H1_R1
