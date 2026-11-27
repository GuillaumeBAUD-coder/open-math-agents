import OMAReductions.R_Erdos128_erdos_128_R2

section R1Section
/-
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

namespace OMA.Erdos128H1R1

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

end OMA.Erdos128H1R1
end R1Section

section H1Section
/-
# Proof of `Erdos128.erdos_128.R2.H1.R1.H1`

In a maximal triangle-free graph `G` with `14 * δ(G) ≥ 5 * n`, dense half-sets (`50 * e(V') > n^2`),
no homomorphic image of the Grötzsch graph, no homomorphic image of `And(4)`, and containing a
homomorphic image of `V_8 - (2, 6)`, we derive a contradiction by proving that `G` admits a
homomorphism to `V_8` (`And(3)`) and then applying `not_hom_andrasfai` from reduction `R2`:

1. **Substep 1 (`no_026` / `no_426`)**: No vertex hits `{v 0, v 2, v 6}` or `{v 4, v 2, v 6}`
   (via a `K_{2,2}` of Grötzsch obstructions yielding `15 * n ≤ 14 * n`).
2. **Substep 2 (`exists_full_v8`)**: Upgrade `V_8 - (2, 6)` to a full `V_8` homomorphism
   (via maximality + fractional clique bounds `85 * n ≤ 84 * n`).
3. **Substep 3 (`no_hit_v8_edge`, `u_complete`)**: For any full `V_8` image `v`, no vertex hits both
   `U v i` and `U v j` for an edge `(i, j)` of `V_8` (orbit `(0, 1)` via `And(4)` giving `85 * n ≤ 84 * n`;
   orbit `(0, 4)` via Grötzsch giving `100 * n ≤ 98 * n`). By maximality, `U v 0, ..., U v 7` form a
   complete blow-up of `V_8`.
4. **Substep 4 (`no_101`)**: For any full `V_8` image `v`, any vertex adjacent to both `v (c + 1)` and
   `v (c + 7)` is also adjacent to `v (c + 4)` (via a 4-cycle of Grötzsch obstructions giving `85 * n ≤ 84 * n`).
5. **Substep 5 (`B = ∅`)**: Choosing a full `V_8` image `v` maximizing `∑ j, #(U v j)`, every vertex
   `x ∈ B := V \ ⋃ U v j` has `cls x = c` and misses either all of `U v (c + 1)` or all of `U v (c + 7)`.
   A sharp 5-weight vertex count gives `14 * |N_G(x) ∩ U| + 7 * #B < 5 * n` for every `x ∈ B`, which
   combined with Mantel's theorem on `G[B]` forces `B = ∅`.
6. **Conclusion**: `cls` is a homomorphism `G → V_8`, contradicting `not_hom_andrasfai` (`d = 3`).
-/

namespace Erdos128_R2_H1_R1_H1

open Finset SimpleGraph OMA.R_Erdos128_erdos_128_R2

abbrev IsV8MinusE {V : Type} (G : SimpleGraph V) (v : Fin 8 → V) : Prop :=
  ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
    ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → G.Adj (v i) (v j)

abbrev IsFullV8 {V : Type} (G : SimpleGraph V) (v : Fin 8 → V) : Prop :=
  ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) → G.Adj (v i) (v j)

abbrev NoGrotzsch {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ ∃ (o m : Fin 5 → V) (z : V), ∀ i : Fin 5,
    G.Adj (o i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 1)) ∧
    G.Adj (m i) (o (i + 4)) ∧ G.Adj z (m i)

abbrev NoAnd4 {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ ∃ φ : Fin 11 → V, ∀ i j : Fin 11,
    (j = i + 1 ∨ j = i + 4 ∨ j = i + 7 ∨ j = i + 10) → G.Adj (φ i) (φ j)

private lemma mkGrotzsch {V : Type} (G : SimpleGraph V) (hnoG : NoGrotzsch G)
    (o0 o1 o2 o3 o4 m0 m1 m2 m3 m4 z : V)
    (e01 : G.Adj o0 o1) (e12 : G.Adj o1 o2) (e23 : G.Adj o2 o3) (e34 : G.Adj o3 o4) (e40 : G.Adj o4 o0)
    (a01 : G.Adj m0 o1) (a04 : G.Adj m0 o4)
    (a12 : G.Adj m1 o2) (a10 : G.Adj m1 o0)
    (a23 : G.Adj m2 o3) (a21 : G.Adj m2 o1)
    (a34 : G.Adj m3 o4) (a32 : G.Adj m3 o2)
    (a40 : G.Adj m4 o0) (a43 : G.Adj m4 o3)
    (z0 : G.Adj z m0) (z1 : G.Adj z m1) (z2 : G.Adj z m2) (z3 : G.Adj z m3) (z4 : G.Adj z m4) : False := by
  apply hnoG
  let o : Fin 5 → V := ![o0, o1, o2, o3, o4]
  let m : Fin 5 → V := ![m0, m1, m2, m3, m4]
  refine ⟨o, m, z, fun i => ?_⟩
  fin_cases i
  · exact ⟨e01, a01, a04, z0⟩
  · exact ⟨e12, a12, a10, z1⟩
  · exact ⟨e23, a23, a21, z2⟩
  · exact ⟨e34, a34, a32, z3⟩
  · exact ⟨e40, a40, a43, z4⟩

private lemma mkAnd4 {V : Type} (G : SimpleGraph V) (hnoA : NoAnd4 G)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : V)
    (e0_1 : G.Adj p0 p1) (e1_2 : G.Adj p1 p2) (e2_3 : G.Adj p2 p3) (e3_4 : G.Adj p3 p4)
    (e4_5 : G.Adj p4 p5) (e5_6 : G.Adj p5 p6) (e6_7 : G.Adj p6 p7) (e7_8 : G.Adj p7 p8)
    (e8_9 : G.Adj p8 p9) (e9_10 : G.Adj p9 p10) (e10_0 : G.Adj p10 p0)
    (e0_4 : G.Adj p0 p4) (e1_5 : G.Adj p1 p5) (e2_6 : G.Adj p2 p6) (e3_7 : G.Adj p3 p7)
    (e4_8 : G.Adj p4 p8) (e5_9 : G.Adj p5 p9) (e6_10 : G.Adj p6 p10) (e7_0 : G.Adj p7 p0)
    (e8_1 : G.Adj p8 p1) (e9_2 : G.Adj p9 p2) (e10_3 : G.Adj p10 p3) : False := by
  apply hnoA
  let φ : Fin 11 → V := ![p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
  refine ⟨φ, fun i j hij => ?_⟩
  rcases hij with rfl | rfl | rfl | rfl
  · fin_cases i
    · exact e0_1
    · exact e1_2
    · exact e2_3
    · exact e3_4
    · exact e4_5
    · exact e5_6
    · exact e6_7
    · exact e7_8
    · exact e8_9
    · exact e9_10
    · exact e10_0
  · fin_cases i
    · exact e0_4
    · exact e1_5
    · exact e2_6
    · exact e3_7
    · exact e4_8
    · exact e5_9
    · exact e6_10
    · exact e7_0
    · exact e8_1
    · exact e9_2
    · exact e10_3
  · fin_cases i
    · exact e7_0.symm
    · exact e8_1.symm
    · exact e9_2.symm
    · exact e10_3.symm
    · exact e0_4.symm
    · exact e1_5.symm
    · exact e2_6.symm
    · exact e3_7.symm
    · exact e4_8.symm
    · exact e5_9.symm
    · exact e6_10.symm
  · fin_cases i
    · exact e10_0.symm
    · exact e0_1.symm
    · exact e1_2.symm
    · exact e2_3.symm
    · exact e3_4.symm
    · exact e4_5.symm
    · exact e5_6.symm
    · exact e6_7.symm
    · exact e7_8.symm
    · exact e8_9.symm
    · exact e9_10.symm

private lemma weighted_deg_contra {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    {k : ℕ} (pts : Fin k → V) (wts : Fin k → ℕ) (cap : ℕ)
    (hgt : 14 * cap < 5 * ∑ i : Fin k, wts i)
    (hcap : ∀ w : V, (∑ i : Fin k, if G.Adj w (pts i) then wts i else 0) ≤ cap)
    (hne : Nonempty V) : False := by
  set n := Fintype.card V
  have hn : 0 < n := Fintype.card_pos_iff.mpr hne
  have hsum_le : ∑ w : V, (∑ i : Fin k, if G.Adj w (pts i) then wts i else 0) ≤ cap * n := by
    calc _ ≤ ∑ _w : V, cap := Finset.sum_le_sum (fun w _ => hcap w)
      _ = cap * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hsum_eq : ∑ w : V, (∑ i : Fin k, if G.Adj w (pts i) then wts i else 0) =
      ∑ i : Fin k, wts i * #(univ.filter (G.Adj (pts i))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    congr 2; ext w; simp [G.adj_comm]
  have hsum_ge : 5 * (∑ i : Fin k, wts i) * n ≤
      14 * ∑ i : Fin k, wts i * #(univ.filter (G.Adj (pts i))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum; intro i _
    have hdi := h14 (pts i)
    have hmul := Nat.mul_le_mul_left (wts i) hdi
    have h1 : 5 * wts i * n = wts i * (5 * n) := by ring
    have h2 : 14 * (wts i * #(univ.filter (G.Adj (pts i)))) = wts i * (14 * #(univ.filter (G.Adj (pts i)))) := by ring
    omega
  have hcap_ge : 5 * (∑ i : Fin k, wts i) * n ≤ 14 * cap * n := by
    have : 14 * (cap * n) = 14 * cap * n := by ring
    omega
  have : 5 * (∑ i : Fin k, wts i) ≤ 14 * cap := Nat.le_of_mul_le_mul_right hcap_ge hn
  omega

private lemma decide_not_both {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) {p q w : V} (hpq : G.Adj p q) :
    (decide (G.Adj w p) && decide (G.Adj w q)) = false := by
  by_cases h1 : G.Adj w p <;> by_cases h2 : G.Adj w q
  · exact (not_adj_of_cliqueFree_three hTF h1 hpq h2).elim
  all_goals simp [h1, h2]

private lemma decide_not_triple {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q r w : V} (h : ¬ (G.Adj w p ∧ G.Adj w q ∧ G.Adj w r)) :
    (decide (G.Adj w p) && decide (G.Adj w q) && decide (G.Adj w r)) = false := by
  by_cases h1 : G.Adj w p <;> by_cases h2 : G.Adj w q <;> by_cases h3 : G.Adj w r
  · exact (h ⟨h1, h2, h3⟩).elim
  all_goals simp [h1, h2, h3]

private lemma decide_not_quad {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q r s w : V} (h : ¬ (G.Adj w p ∧ G.Adj w q ∧ G.Adj w r ∧ G.Adj w s)) :
    (decide (G.Adj w p) && decide (G.Adj w q) && decide (G.Adj w r) && decide (G.Adj w s)) = false := by
  by_cases h1 : G.Adj w p <;> by_cases h2 : G.Adj w q <;> by_cases h3 : G.Adj w r <;> by_cases h4 : G.Adj w s
  · exact (h ⟨h1, h2, h3, h4⟩).elim
  all_goals simp [h1, h2, h3, h4]

private lemma adj_term_eq {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    {w u v : V} {a b : ℕ} (hu : u = v) (ha : a = b) :
    (if G.Adj w u then a else 0) = b * (decide (G.Adj w v)).toNat := by
  subst hu; subst ha; by_cases h1 : G.Adj w u <;> simp [h1]

private lemma sum_fin9 (f : Fin 9 → ℕ) :
    ∑ i : Fin 9, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]; rfl

private lemma sum_fin10 (f : Fin 10 → ℕ) :
    ∑ i : Fin 10, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]; rfl

private lemma sum_fin11 (f : Fin 11 → ℕ) :
    ∑ i : Fin 11, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]; rfl

/- Finite Boolean weight-cap lemmas (each ≤ 2^11 cases, checked by kernel `decide`). -/

private theorem bool_hno026_A : ∀ b1 b2 b3 b5 b6 b7 : Bool,
    (!(b1 && b2) && !(b2 && b3) && !(b5 && b6) && !(b6 && b7) && !(b1 && b5) && !(b3 && b7) &&
     !(b1 && b3 && b6) && !(b2 && b5 && b7)) = true →
    b1.toNat + b2.toNat + b3.toNat + b5.toNat + b6.toNat + b7.toNat ≤ 2 := by decide

private theorem bool_hno026_B : ∀ b2 b3 b4 b5 b6 b8 : Bool,
    (!(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) && !(b2 && b8) && !(b6 && b8) &&
     !(b2 && b4 && b6) && !(b3 && b5 && b8)) = true →
    b2.toNat + b3.toNat + b4.toNat + b5.toNat + b6.toNat + b8.toNat ≤ 2 := by decide

private theorem bool_upgrade_1a : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b3 && b7) &&
     !(b2 && b8) && !(b6 && b8) &&
     !(b1 && b9) && !(b4 && b9) && !(b7 && b9) && !(b8 && b9) &&
     !(b0 && b10) && !(b3 && b10) && !(b5 && b10) && !(b8 && b10) &&
     !(b0 && b2 && b6) && !(b4 && b2 && b6)) = true →
    1 * b0.toNat + 2 * b1.toNat + 2 * b2.toNat + 2 * b3.toNat + 1 * b4.toNat + 2 * b5.toNat +
      2 * b6.toNat + 2 * b7.toNat + 1 * b8.toNat + 1 * b9.toNat + 1 * b10.toNat ≤ 6 := by decide

private theorem bool_upgrade_1b : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b3 && b7) &&
     !(b2 && b8) && !(b6 && b8) &&
     !(b0 && b2 && b6) && !(b4 && b2 && b6) && !(b1 && b4 && b7 && b8)) = true →
    2 * b0.toNat + 2 * b1.toNat + 3 * b2.toNat + 1 * b3.toNat + 1 * b4.toNat + 1 * b5.toNat +
      3 * b6.toNat + 2 * b7.toNat + 2 * b8.toNat ≤ 6 := by decide

private theorem bool_edge01_A : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b2 && b6) && !(b3 && b7) &&
     !(b8 && b9) && !(b8 && b10) &&
     !(b9 && b1) && !(b9 && b4) && !(b9 && b7) &&
     !(b10 && b2) && !(b10 && b5) && !(b10 && b0) &&
     !(b3 && b6 && b9 && b10) && !(b2 && b4 && b7 && b8)) = true →
    1 * b0.toNat + 1 * b1.toNat + 2 * b2.toNat + 2 * b3.toNat + 2 * b4.toNat + 1 * b5.toNat +
      1 * b6.toNat + 1 * b7.toNat + 2 * b8.toNat + 2 * b9.toNat + 2 * b10.toNat ≤ 6 := by decide

private theorem bool_edge01_B : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b2 && b6) && !(b3 && b7) &&
     !(b8 && b9) && !(b8 && b10) &&
     !(b9 && b1) && !(b9 && b4) && !(b9 && b7) &&
     !(b10 && b2) && !(b10 && b5) && !(b10 && b0) &&
     !(b3 && b6 && b9 && b10) && !(b2 && b5 && b7 && b8)) = true →
    1 * b0.toNat + 1 * b1.toNat + 1 * b2.toNat + 1 * b3.toNat + 1 * b4.toNat + 2 * b5.toNat +
      2 * b6.toNat + 2 * b7.toNat + 2 * b8.toNat + 2 * b9.toNat + 2 * b10.toNat ≤ 6 := by decide

private theorem bool_edge04_A : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b2 && b6) && !(b3 && b7) &&
     !(b8 && b9) && !(b8 && b10) &&
     !(b9 && b1) && !(b9 && b4) && !(b9 && b7) &&
     !(b10 && b5) && !(b10 && b0) && !(b10 && b3) &&
     !(b1 && b3 && b6 && b8) && !(b2 && b9 && b10)) = true →
    1 * b0.toNat + 2 * b1.toNat + 2 * b2.toNat + 2 * b3.toNat + 1 * b4.toNat + 1 * b5.toNat +
      1 * b6.toNat + 1 * b7.toNat + 3 * b8.toNat + 3 * b9.toNat + 3 * b10.toNat ≤ 7 := by decide

private theorem bool_hno101_A : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b2 && b6) && !(b3 && b7) &&
     !(b8 && b1) && !(b8 && b7) && !(b9 && b4) && !(b8 && b9) &&
     !(b2 && b4 && b8) && !(b1 && b3 && b6 && b9)) = true →
    1 * b0.toNat + 2 * b1.toNat + 2 * b2.toNat + 2 * b3.toNat + 3 * b4.toNat + 1 * b5.toNat +
      1 * b6.toNat + 1 * b7.toNat + 2 * b8.toNat + 2 * b9.toNat ≤ 6 := by decide

/- Step 1: No vertex hits `{v 0, v 2, v 6}` or `{v 4, v 2, v 6}` in `V_8 - (2, 6)`. -/

private lemma no_026 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsV8MinusE G v) :
    ∀ z : V, ¬ (G.Adj z (v 0) ∧ G.Adj z (v 2) ∧ G.Adj z (v 6)) := by
  rintro z ⟨hz0, hz2, hz6⟩
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide) (by decide) (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide) (by decide) (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide) (by decide) (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide) (by decide) (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide) (by decide) (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide) (by decide) (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide) (by decide) (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide) (by decide) (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide) (by decide) (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide) (by decide) (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide) (by decide) (by decide)
  by_cases hA : (∃ a : V, G.Adj a (v 1) ∧ G.Adj a (v 3) ∧ G.Adj a (v 6)) ∨
                (∃ a : V, G.Adj a (v 2) ∧ G.Adj a (v 5) ∧ G.Adj a (v 7))
  · have hno246 : ∀ b : V, ¬ (G.Adj b (v 2) ∧ G.Adj b (v 4) ∧ G.Adj b (v 6)) := by
      rintro b ⟨hb2, hb4, hb6⟩
      rcases hA with ⟨a, ha1, ha3, ha6⟩ | ⟨a, ha2, ha5, ha7⟩
      · exact mkGrotzsch G hnoG (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) z a b (v 7) (v 6)
          e01 e12 e23 e34 e04.symm e15.symm e45.symm hz2 hz0 ha3 ha1 hb4 hb2 e70 e37.symm
          e56.symm hz6.symm ha6.symm hb6.symm e67
      · exact mkGrotzsch G hnoG (v 0) (v 4) (v 5) (v 6) (v 7) (v 3) (v 1) b a z (v 2)
          e04 e45 e56 e67 e70 e34 e37 e15 e01.symm hb6 hb4 ha7 ha5 hz0 hz6
          e23 e12.symm hb2.symm ha2.symm hz2.symm
    have hno35z : ∀ b : V, ¬ (G.Adj b (v 3) ∧ G.Adj b (v 5) ∧ G.Adj b z) := by
      rintro b ⟨hb3, hb5, hbz⟩
      rcases hA with ⟨a, ha1, ha3, ha6⟩ | ⟨a, ha2, ha5, ha7⟩
      · exact mkGrotzsch G hnoG (v 0) (v 1) (v 5) (v 6) z (v 2) (v 4) a b (v 7) (v 3)
          e01 e15 e56 hz6.symm hz0 e12.symm hz2.symm e45 e04.symm ha6 ha1 hbz hb5 e70 e67.symm
          e23.symm e34 ha3.symm hb3.symm e37
      · exact mkGrotzsch G hnoG (v 0) (v 7) (v 3) (v 2) z (v 6) (v 4) a b (v 1) (v 5)
          e70.symm e37.symm e23.symm hz2.symm hz0 e67 hz6.symm e34.symm e04.symm ha2 ha7 hbz hb3 e01.symm e12
          e56 e45.symm ha5.symm hb5.symm e15.symm
    let pts : Fin 6 → V := ![v 2, v 3, v 4, v 5, v 6, z]
    let wts : Fin 6 → ℕ := ![1, 1, 1, 1, 1, 1]
    refine weighted_deg_contra G h14 pts wts 2 (by decide) (fun w => ?_) ⟨z⟩
    have key := bool_hno026_B (decide (G.Adj w (v 2))) (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4)))
      (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6))) (decide (G.Adj w z))
      (by rw [decide_not_both G hTF e23, decide_not_both G hTF e34, decide_not_both G hTF e45,
              decide_not_both G hTF e56, decide_not_both G hTF hz2.symm, decide_not_both G hTF hz6.symm,
              decide_not_triple G (hno246 w), decide_not_triple G (hno35z w)]; rfl)
    rw [Fin.sum_univ_six,
      adj_term_eq G (show pts 0 = v 2 from rfl) (show wts 0 = 1 from rfl),
      adj_term_eq G (show pts 1 = v 3 from rfl) (show wts 1 = 1 from rfl),
      adj_term_eq G (show pts 2 = v 4 from rfl) (show wts 2 = 1 from rfl),
      adj_term_eq G (show pts 3 = v 5 from rfl) (show wts 3 = 1 from rfl),
      adj_term_eq G (show pts 4 = v 6 from rfl) (show wts 4 = 1 from rfl),
      adj_term_eq G (show pts 5 = z from rfl) (show wts 5 = 1 from rfl)]
    omega
  · push Not at hA
    let pts : Fin 6 → V := ![v 1, v 2, v 3, v 5, v 6, v 7]
    let wts : Fin 6 → ℕ := ![1, 1, 1, 1, 1, 1]
    refine weighted_deg_contra G h14 pts wts 2 (by decide) (fun w => ?_) ⟨z⟩
    have key := bool_hno026_A (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2))) (decide (G.Adj w (v 3)))
      (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6))) (decide (G.Adj w (v 7)))
      (by rw [decide_not_both G hTF e12, decide_not_both G hTF e23, decide_not_both G hTF e56,
              decide_not_both G hTF e67, decide_not_both G hTF e15, decide_not_both G hTF e37,
              decide_not_triple G (fun ⟨h1, h3, h6⟩ => hA.1 w h1 h3 h6),
              decide_not_triple G (fun ⟨h2, h5, h7⟩ => hA.2 w h2 h5 h7)]; rfl)
    rw [Fin.sum_univ_six,
      adj_term_eq G (show pts 0 = v 1 from rfl) (show wts 0 = 1 from rfl),
      adj_term_eq G (show pts 1 = v 2 from rfl) (show wts 1 = 1 from rfl),
      adj_term_eq G (show pts 2 = v 3 from rfl) (show wts 2 = 1 from rfl),
      adj_term_eq G (show pts 3 = v 5 from rfl) (show wts 3 = 1 from rfl),
      adj_term_eq G (show pts 4 = v 6 from rfl) (show wts 4 = 1 from rfl),
      adj_term_eq G (show pts 5 = v 7 from rfl) (show wts 5 = 1 from rfl)]
    omega

private lemma isV8MinusE_refl4 {V : Type} {G : SimpleGraph V} {v : Fin 8 → V} (hv : IsV8MinusE G v) :
    IsV8MinusE G (fun i => v (4 - i)) := by
  intro i j hij h26 h62
  apply hv (4 - i) (4 - j)
  · rcases hij with rfl | rfl | rfl <;> (fin_cases i <;> decide)
  · intro h; apply h26; fin_cases i <;> fin_cases j <;> simp_all
  · intro h; apply h62; fin_cases i <;> fin_cases j <;> simp_all

private lemma no_426 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsV8MinusE G v) :
    ∀ z : V, ¬ (G.Adj z (v 4) ∧ G.Adj z (v 2) ∧ G.Adj z (v 6)) := by
  intro z ⟨hz4, hz2, hz6⟩
  exact no_026 G hTF h14 hnoG (fun i => v (4 - i)) (isV8MinusE_refl4 hv) z ⟨hz4, hz2, hz6⟩

/- Step 2: Upgrade `V_8 - (2, 6)` to a full `V_8` homomorphism. -/

private lemma upgrade_no_147z {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsV8MinusE G v) (z : V)
    (hz2 : G.Adj z (v 2)) (hz6 : G.Adj z (v 6))
    (hno147z : ∀ w : V, ¬ (G.Adj w (v 1) ∧ G.Adj w (v 4) ∧ G.Adj w (v 7) ∧ G.Adj w z)) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide) (by decide) (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide) (by decide) (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide) (by decide) (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide) (by decide) (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide) (by decide) (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide) (by decide) (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide) (by decide) (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide) (by decide) (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide) (by decide) (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide) (by decide) (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide) (by decide) (by decide)
  have h026 := no_026 G hTF h14 hnoG v hv
  have h426 := no_426 G hTF h14 hnoG v hv
  let pts : Fin 9 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, z]
  let wts : Fin 9 → ℕ := ![2, 2, 3, 1, 1, 1, 3, 2, 2]
  refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun w => ?_) ⟨z⟩
  have key := bool_upgrade_1b (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
    (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
    (decide (G.Adj w (v 7))) (decide (G.Adj w z))
    (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
            decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
            decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
            decide_not_both G hTF e15, decide_not_both G hTF e37,
            decide_not_both G hTF hz2.symm, decide_not_both G hTF hz6.symm,
            decide_not_triple G (h026 w), decide_not_triple G (h426 w),
            decide_not_quad G (hno147z w)]; rfl)
  rw [sum_fin9,
    adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 2 from rfl),
    adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 2 from rfl),
    adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 3 from rfl),
    adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 1 from rfl),
    adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 1 from rfl),
    adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 1 from rfl),
    adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 3 from rfl),
    adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 2 from rfl),
    adj_term_eq G (show pts 8 = z from rfl) (show wts 8 = 2 from rfl)]
  omega

private lemma exists_full_v8 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsV8MinusE G v) :
    IsFullV8 G v := by
  have h26 : G.Adj (v 2) (v 6) := by
    by_contra hnot
    have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide) (by decide) (by decide)
    have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide) (by decide) (by decide)
    have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide) (by decide) (by decide)
    have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide) (by decide) (by decide)
    have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide) (by decide) (by decide)
    have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide) (by decide) (by decide)
    have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide) (by decide) (by decide)
    have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide) (by decide) (by decide)
    have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide) (by decide) (by decide)
    have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide) (by decide) (by decide)
    have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide) (by decide) (by decide)
    have hne26 : v 2 ≠ v 6 := by
      intro heq
      rw [← heq] at e56
      exact not_adj_of_cliqueFree_three hTF e12.symm e15 e56.symm
    obtain ⟨z, hz2, hz6⟩ := hmax (v 2) (v 6) hne26 hnot
    by_cases hy1 : ∃ y1 : V, G.Adj y1 (v 1) ∧ G.Adj y1 (v 4) ∧ G.Adj y1 (v 7) ∧ G.Adj y1 z
    · by_cases hy2 : ∃ y2 : V, G.Adj y2 (v 0) ∧ G.Adj y2 (v 3) ∧ G.Adj y2 (v 5) ∧ G.Adj y2 z
      · obtain ⟨y1, h11, h14', h17, h1z⟩ := hy1
        obtain ⟨y2, h20, h23, h25, h2z⟩ := hy2
        have h026 := no_026 G hTF h14 hnoG v hv
        have h426 := no_426 G hTF h14 hnoG v hv
        let pts : Fin 11 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, z, y1, y2]
        let wts : Fin 11 → ℕ := ![1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 1]
        refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun w => ?_) ⟨z⟩
        have key := bool_upgrade_1a (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
          (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
          (decide (G.Adj w (v 7))) (decide (G.Adj w z)) (decide (G.Adj w y1)) (decide (G.Adj w y2))
          (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
                  decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
                  decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
                  decide_not_both G hTF e15, decide_not_both G hTF e37,
                  decide_not_both G hTF hz2, decide_not_both G hTF hz6,
                  decide_not_both G hTF h11.symm, decide_not_both G hTF h14'.symm,
                  decide_not_both G hTF h17.symm, decide_not_both G hTF h1z.symm,
                  decide_not_both G hTF h20.symm, decide_not_both G hTF h23.symm,
                  decide_not_both G hTF h25.symm, decide_not_both G hTF h2z.symm,
                  decide_not_triple G (h026 w), decide_not_triple G (h426 w)]; rfl)
        rw [sum_fin11,
          adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
          adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 2 from rfl),
          adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 2 from rfl),
          adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 2 from rfl),
          adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 1 from rfl),
          adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 2 from rfl),
          adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 2 from rfl),
          adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 2 from rfl),
          adj_term_eq G (show pts 8 = z from rfl) (show wts 8 = 1 from rfl),
          adj_term_eq G (show pts 9 = y1 from rfl) (show wts 9 = 1 from rfl),
          adj_term_eq G (show pts 10 = y2 from rfl) (show wts 10 = 1 from rfl)]
        omega
      · push Not at hy2
        exact upgrade_no_147z G hTF h14 hnoG (fun i => v (4 - i)) (isV8MinusE_refl4 hv) z
          hz2.symm hz6.symm (fun w ⟨h1, h4, h7, hz⟩ => hy2 w h4 h1 h7 hz)
    · push Not at hy1
      exact upgrade_no_147z G hTF h14 hnoG v hv z hz2.symm hz6.symm
        (fun w ⟨h1, h4, h7, hz⟩ => hy1 w h1 h4 h7 hz)
  intro i j hij
  by_cases h1 : i = 2 ∧ j = 6
  · rw [h1.1, h1.2]; exact h26
  · by_cases h2 : i = 6 ∧ j = 2
    · rw [h2.1, h2.2]; exact h26.symm
    · exact hv i j hij h1 h2

/- Full `V_8` symmetries and `U v j` definition. -/

private def Uset {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : Fin 8 → V) (j : Fin 8) : Finset V :=
  univ.filter (fun w => G.Adj w (v (j + 1)) ∧ G.Adj w (v (j + 4)) ∧ G.Adj w (v (j + 7)))

private lemma isFullV8_rot {V : Type} {G : SimpleGraph V} {v : Fin 8 → V}
    (hv : IsFullV8 G v) (s : Fin 8) : IsFullV8 G (fun k => v (s + k)) := by
  intro i j hij
  apply hv (s + i) (s + j)
  rcases hij with rfl | rfl | rfl <;> (fin_cases s <;> fin_cases i <;> decide)

private lemma isFullV8_neg {V : Type} {G : SimpleGraph V} {v : Fin 8 → V}
    (hv : IsFullV8 G v) : IsFullV8 G (fun k => v (-k)) := by
  intro i j hij
  apply hv (-i) (-j)
  rcases hij with rfl | rfl | rfl <;> (fin_cases i <;> decide)

/- Step 3: No vertex hits both `U v i` and `U v j` for an edge `(i, j)` of `V_8`. -/

private lemma no_hit_edge_01 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoA : NoAnd4 G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x y1 y2 : V) (hy1 : y1 ∈ Uset G v 0) (hy2 : y2 ∈ Uset G v 1)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  have ⟨h9_1', h9_4', h9_7'⟩ := (Finset.mem_filter.mp hy1).2
  have ⟨h10_2', h10_5', h10_0'⟩ := (Finset.mem_filter.mp hy2).2
  have h9_1 : G.Adj y1 (v 1) := h9_1'
  have h9_4 : G.Adj y1 (v 4) := h9_4'
  have h9_7 : G.Adj y1 (v 7) := h9_7'
  have h10_2 : G.Adj y2 (v 2) := h10_2'
  have h10_5 : G.Adj y2 (v 5) := h10_5'
  have h10_0 : G.Adj y2 (v 0) := h10_0'
  have hno36910 : ∀ w : V, ¬ (G.Adj w (v 3) ∧ G.Adj w (v 6) ∧ G.Adj w y1 ∧ G.Adj w y2) := by
    rintro w ⟨hw3, hw6, hw9, hw10⟩
    exact mkAnd4 G hnoA (v 0) (v 7) (v 6) (v 5) (v 4) (v 3) (v 2) (v 1) y1 w y2
      e70.symm e67.symm e56.symm e45.symm e34.symm e23.symm e12.symm h9_1.symm hw9.symm hw10 h10_0
      e04 e37.symm e26.symm e15.symm h9_4.symm hw3.symm h10_2.symm e01.symm h9_7 hw6 h10_5
  by_cases hA : ∃ a : V, G.Adj a (v 2) ∧ G.Adj a (v 4) ∧ G.Adj a (v 7) ∧ G.Adj a x
  · obtain ⟨a, ha2, ha4, ha7, hax⟩ := hA
    have hnoB : ∀ b : V, ¬ (G.Adj b (v 2) ∧ G.Adj b (v 5) ∧ G.Adj b (v 7) ∧ G.Adj b x) := by
      rintro b ⟨hb2, hb5, hb7, hbx⟩
      exact mkAnd4 G hnoA (v 0) (v 7) b (v 5) (v 4) a (v 2) (v 1) y1 x y2
        e70.symm hb7.symm hb5 e45.symm ha4.symm ha2 e12.symm h9_1.symm hxy1.symm hxy2 h10_0
        e04 ha7.symm hb2 e15.symm h9_4.symm hax h10_2.symm e01.symm h9_7 hbx.symm h10_5
    let pts : Fin 11 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, x, y1, y2]
    let wts : Fin 11 → ℕ := ![1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
    refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun w => ?_) ⟨x⟩
    have key := bool_edge01_B (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
      (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
      (decide (G.Adj w (v 7))) (decide (G.Adj w x)) (decide (G.Adj w y1)) (decide (G.Adj w y2))
      (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
              decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
              decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
              decide_not_both G hTF e15, decide_not_both G hTF e26, decide_not_both G hTF e37,
              decide_not_both G hTF hxy1, decide_not_both G hTF hxy2,
              decide_not_both G hTF h9_1, decide_not_both G hTF h9_4, decide_not_both G hTF h9_7,
              decide_not_both G hTF h10_2, decide_not_both G hTF h10_5, decide_not_both G hTF h10_0,
              decide_not_quad G (hno36910 w), decide_not_quad G (hnoB w)]; rfl)
    rw [sum_fin11,
      adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
      adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 1 from rfl),
      adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 1 from rfl),
      adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 1 from rfl),
      adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 1 from rfl),
      adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 2 from rfl),
      adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 2 from rfl),
      adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 2 from rfl),
      adj_term_eq G (show pts 8 = x from rfl) (show wts 8 = 2 from rfl),
      adj_term_eq G (show pts 9 = y1 from rfl) (show wts 9 = 2 from rfl),
      adj_term_eq G (show pts 10 = y2 from rfl) (show wts 10 = 2 from rfl)]
    omega
  · push Not at hA
    let pts : Fin 11 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, x, y1, y2]
    let wts : Fin 11 → ℕ := ![1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2]
    refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun w => ?_) ⟨x⟩
    have key := bool_edge01_A (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
      (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
      (decide (G.Adj w (v 7))) (decide (G.Adj w x)) (decide (G.Adj w y1)) (decide (G.Adj w y2))
      (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
              decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
              decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
              decide_not_both G hTF e15, decide_not_both G hTF e26, decide_not_both G hTF e37,
              decide_not_both G hTF hxy1, decide_not_both G hTF hxy2,
              decide_not_both G hTF h9_1, decide_not_both G hTF h9_4, decide_not_both G hTF h9_7,
              decide_not_both G hTF h10_2, decide_not_both G hTF h10_5, decide_not_both G hTF h10_0,
              decide_not_quad G (hno36910 w),
              decide_not_quad G (fun ⟨h2, h4, h7, hx⟩ => hA w h2 h4 h7 hx)]; rfl)
    rw [sum_fin11,
      adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
      adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 1 from rfl),
      adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 2 from rfl),
      adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 2 from rfl),
      adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 2 from rfl),
      adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 1 from rfl),
      adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 1 from rfl),
      adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 1 from rfl),
      adj_term_eq G (show pts 8 = x from rfl) (show wts 8 = 2 from rfl),
      adj_term_eq G (show pts 9 = y1 from rfl) (show wts 9 = 2 from rfl),
      adj_term_eq G (show pts 10 = y2 from rfl) (show wts 10 = 2 from rfl)]
    omega

private lemma no_hit_edge_04_caseA {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x y1 y2 : V) (hy1 : y1 ∈ Uset G v 0) (hy2 : y2 ∈ Uset G v 4)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2)
    (hno1 : ∀ w : V, ¬ (G.Adj w (v 1) ∧ G.Adj w (v 3) ∧ G.Adj w (v 6) ∧ G.Adj w x))
    (hno2 : ∀ w : V, ¬ (G.Adj w (v 2) ∧ G.Adj w y1 ∧ G.Adj w y2)) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  have ⟨h9_1', h9_4', h9_7'⟩ := (Finset.mem_filter.mp hy1).2
  have ⟨h10_5', h10_0', h10_3'⟩ := (Finset.mem_filter.mp hy2).2
  have h9_1 : G.Adj y1 (v 1) := h9_1'
  have h9_4 : G.Adj y1 (v 4) := h9_4'
  have h9_7 : G.Adj y1 (v 7) := h9_7'
  have h10_5 : G.Adj y2 (v 5) := h10_5'
  have h10_0 : G.Adj y2 (v 0) := h10_0'
  have h10_3 : G.Adj y2 (v 3) := h10_3'
  let pts : Fin 11 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, x, y1, y2]
  let wts : Fin 11 → ℕ := ![1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 3]
  refine weighted_deg_contra G h14 pts wts 7 (by decide) (fun w => ?_) ⟨x⟩
  have key := bool_edge04_A (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
    (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
    (decide (G.Adj w (v 7))) (decide (G.Adj w x)) (decide (G.Adj w y1)) (decide (G.Adj w y2))
    (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
            decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
            decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
            decide_not_both G hTF e15, decide_not_both G hTF e26, decide_not_both G hTF e37,
            decide_not_both G hTF hxy1, decide_not_both G hTF hxy2,
            decide_not_both G hTF h9_1, decide_not_both G hTF h9_4, decide_not_both G hTF h9_7,
            decide_not_both G hTF h10_5, decide_not_both G hTF h10_0, decide_not_both G hTF h10_3,
            decide_not_quad G (hno1 w), decide_not_triple G (hno2 w)]; rfl)
  rw [sum_fin11,
    adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
    adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 2 from rfl),
    adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 2 from rfl),
    adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 2 from rfl),
    adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 1 from rfl),
    adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 1 from rfl),
    adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 1 from rfl),
    adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 1 from rfl),
    adj_term_eq G (show pts 8 = x from rfl) (show wts 8 = 3 from rfl),
    adj_term_eq G (show pts 9 = y1 from rfl) (show wts 9 = 3 from rfl),
    adj_term_eq G (show pts 10 = y2 from rfl) (show wts 10 = 3 from rfl)]
  omega

private lemma no_hit_edge_04 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x y1 y2 : V) (hy1 : y1 ∈ Uset G v 0) (hy2 : y2 ∈ Uset G v 4)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  have ⟨h9_1', h9_4', h9_7'⟩ := (Finset.mem_filter.mp hy1).2
  have ⟨h10_5', h10_0', h10_3'⟩ := (Finset.mem_filter.mp hy2).2
  have h9_1 : G.Adj y1 (v 1) := h9_1'
  have h9_4 : G.Adj y1 (v 4) := h9_4'
  have h9_7 : G.Adj y1 (v 7) := h9_7'
  have h10_5 : G.Adj y2 (v 5) := h10_5'
  have h10_0 : G.Adj y2 (v 0) := h10_0'
  have h10_3 : G.Adj y2 (v 3) := h10_3'
  by_cases hA : (∃ a : V, G.Adj a (v 1) ∧ G.Adj a (v 3) ∧ G.Adj a (v 6) ∧ G.Adj a x) ∨
                (∃ a : V, G.Adj a (v 2) ∧ G.Adj a y1 ∧ G.Adj a y2)
  · have hno1 : ∀ b : V, ¬ (G.Adj b (v 2) ∧ G.Adj b (v 5) ∧ G.Adj b (v 7) ∧ G.Adj b x) := by
      rintro b ⟨hb2, hb5, hb7, hbx⟩
      rcases hA with ⟨a, ha1, ha3, ha6, hax⟩ | ⟨a, ha2, ha9, ha10⟩
      · exact mkGrotzsch G hnoG (v 1) (v 5) y2 x a (v 6) (v 0) b (v 3) y1 (v 7)
          e15 h10_5.symm hxy2.symm hax.symm ha1 e56.symm ha6.symm h10_0.symm e01 hbx hb5
          ha3.symm h10_3.symm h9_1 hxy1.symm e67.symm e70 hb7.symm e37.symm h9_7.symm
      · exact mkGrotzsch G hnoG (v 1) (v 2) b (v 7) y1 a (v 5) (v 3) x (v 0) y2
          e12 hb2.symm hb7 h9_7.symm h9_1 ha2 ha9 hb5.symm e15.symm e37 e23.symm hxy1 hbx.symm
          e01 e70.symm ha10.symm h10_5 h10_3 hxy2.symm h10_0
    have hno2 : ∀ b : V, ¬ (G.Adj b (v 6) ∧ G.Adj b y1 ∧ G.Adj b y2) := by
      rintro b ⟨hb6, hb9, hb10⟩
      rcases hA with ⟨a, ha1, ha3, ha6, hax⟩ | ⟨a, ha2, ha9, ha10⟩
      · exact mkGrotzsch G hnoG (v 1) y1 (v 7) (v 6) a x (v 0) b (v 3) (v 5) y2
          h9_1.symm h9_7 e67.symm ha6.symm ha1 hxy1 hax.symm e70.symm e01 hb6 hb9 ha3.symm e37
          e15.symm e56 hxy2.symm h10_0 hb10.symm h10_3 h10_5
      · exact mkGrotzsch G hnoG (v 1) (v 2) (v 6) (v 7) y1 a (v 5) (v 3) b (v 0) y2
          e12 e26 e67 h9_7.symm h9_1 ha2 ha9 e56 e15.symm e37 e23.symm hb9 hb6 e01 e70.symm
          ha10.symm h10_5 h10_3 hb10.symm h10_0
    have hy1' : y1 ∈ Uset G (fun k => v (-k)) 0 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h9_7, h9_4, h9_1⟩
    have hy2' : y2 ∈ Uset G (fun k => v (-k)) 4 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h10_3, h10_0, h10_5⟩
    exact no_hit_edge_04_caseA G hTF h14 (fun k => v (-k)) (isFullV8_neg hv) x y1 y2 hy1' hy2' hxy1 hxy2
      (fun w ⟨h7, h5, h2, hx⟩ => hno1 w ⟨h2, h5, h7, hx⟩)
      (fun w ⟨h6, h9, h10⟩ => hno2 w ⟨h6, h9, h10⟩)
  · push Not at hA
    exact no_hit_edge_04_caseA G hTF h14 v hv x y1 y2 hy1 hy2 hxy1 hxy2
      (fun w ⟨h1, h3, h6, hx⟩ => hA.1 w h1 h3 h6 hx)
      (fun w ⟨h2, h9, h10⟩ => hA.2 w h2 h9 h10)

private lemma no_hit_v8_edge {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G) (hnoA : NoAnd4 G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x : V) (i j : Fin 8) (hij : j = i + 1 ∨ j = i + 4 ∨ j = i + 7)
    (y1 : V) (hy1 : y1 ∈ Uset G v i) (y2 : V) (hy2 : y2 ∈ Uset G v j)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2) : False := by
  have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hy1).2
  have ⟨b1, b4, b7⟩ := (Finset.mem_filter.mp hy2).2
  rcases hij with rfl | rfl | rfl
  · let v' : Fin 8 → V := fun k => v (i + k)
    have hy1' : y1 ∈ Uset G v' 0 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + (0 + 1) = i + 1 := by fin_cases i <;> decide
      have h4 : i + (0 + 4) = i + 4 := by fin_cases i <;> decide
      have h7 : i + (0 + 7) = i + 7 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨a1, a4, a7⟩
    have hy2' : y2 ∈ Uset G v' 1 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + (1 + 1) = i + 1 + 1 := by fin_cases i <;> decide
      have h4 : i + (1 + 4) = i + 1 + 4 := by fin_cases i <;> decide
      have h7 : i + (1 + 7) = i + 1 + 7 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨b1, b4, b7⟩
    exact no_hit_edge_01 G hTF h14 hnoA v' (isFullV8_rot hv i) x y1 y2 hy1' hy2' hxy1 hxy2
  · let v' : Fin 8 → V := fun k => v (i + k)
    have hy1' : y1 ∈ Uset G v' 0 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + (0 + 1) = i + 1 := by fin_cases i <;> decide
      have h4 : i + (0 + 4) = i + 4 := by fin_cases i <;> decide
      have h7 : i + (0 + 7) = i + 7 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨a1, a4, a7⟩
    have hy2' : y2 ∈ Uset G v' 4 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + (4 + 1) = i + 4 + 1 := by fin_cases i <;> decide
      have h4 : i + (4 + 4) = i + 4 + 4 := by fin_cases i <;> decide
      have h7 : i + (4 + 7) = i + 4 + 7 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨b1, b4, b7⟩
    exact no_hit_edge_04 G hTF h14 hnoG v' (isFullV8_rot hv i) x y1 y2 hy1' hy2' hxy1 hxy2
  · let v' : Fin 8 → V := fun k => v (i + (-k))
    have hv' : IsFullV8 G v' := isFullV8_neg (isFullV8_rot hv i)
    have hy1' : y1 ∈ Uset G v' 0 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + -(0 + 1) = i + 7 := by fin_cases i <;> decide
      have h4 : i + -(0 + 4) = i + 4 := by fin_cases i <;> decide
      have h7 : i + -(0 + 7) = i + 1 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨a7, a4, a1⟩
    have hy2' : y2 ∈ Uset G v' 1 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + -(1 + 1) = i + 7 + 7 := by fin_cases i <;> decide
      have h4 : i + -(1 + 4) = i + 7 + 4 := by fin_cases i <;> decide
      have h7 : i + -(1 + 7) = i + 7 + 1 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨b7, b4, b1⟩
    exact no_hit_edge_01 G hTF h14 hnoA v' hv' x y1 y2 hy1' hy2' hxy1 hxy2

private lemma uset_disjoint {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) (v : Fin 8 → V) (hv : IsFullV8 G v)
    {i j : Fin 8} (hij : i ≠ j) : Disjoint (Uset G v i) (Uset G v j) := by
  rw [Finset.disjoint_left]
  intro w hwi hwj
  have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hwi).2
  have ⟨b1, b4, b7⟩ := (Finset.mem_filter.mp hwj).2
  have hna : ∀ p q : Fin 8, (q = p + 1 ∨ q = p + 4 ∨ q = p + 7) → G.Adj w (v p) → G.Adj w (v q) → False :=
    fun p q hpq hp hq => not_adj_of_cliqueFree_three hTF hp (hv p q hpq) hq
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals first
    | exact hna _ _ (by decide) a1 b1 | exact hna _ _ (by decide) a1 b4 | exact hna _ _ (by decide) a1 b7
    | exact hna _ _ (by decide) a4 b1 | exact hna _ _ (by decide) a4 b4 | exact hna _ _ (by decide) a4 b7
    | exact hna _ _ (by decide) a7 b1

private lemma uset_complete {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G) (hnoA : NoAnd4 G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (i j : Fin 8) (hij : j = i + 1 ∨ j = i + 4 ∨ j = i + 7)
    (y1 : V) (hy1 : y1 ∈ Uset G v i) (y2 : V) (hy2 : y2 ∈ Uset G v j) :
    G.Adj y1 y2 := by
  by_contra hnot
  have hne_ij : i ≠ j := by rcases hij with rfl | rfl | rfl <;> (fin_cases i <;> decide)
  have hne : y1 ≠ y2 := fun heq => by
    rw [heq] at hy1
    exact Finset.disjoint_left.mp (uset_disjoint G hTF v hv hne_ij) hy1 hy2
  obtain ⟨x, hx1, hx2⟩ := hmax y1 y2 hne hnot
  exact no_hit_v8_edge G hTF h14 hnoG hnoA v hv x i j hij y1 hy1 y2 hy2 hx1.symm hx2.symm

/- Step 4: No vertex hits `{v (c + 1), v (c + 7)}` while missing `v (c + 4)`. -/

private lemma no_101_caseA {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x w : V) (hx1 : G.Adj x (v 1)) (hx7 : G.Adj x (v 7)) (hw4 : G.Adj w (v 4)) (hxw : G.Adj x w)
    (hnoA : ∀ u : V, ¬ (G.Adj u (v 2) ∧ G.Adj u (v 4) ∧ G.Adj u x))
    (hnoC : ∀ u : V, ¬ (G.Adj u (v 1) ∧ G.Adj u (v 3) ∧ G.Adj u (v 6) ∧ G.Adj u w)) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  let pts : Fin 10 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, x, w]
  let wts : Fin 10 → ℕ := ![1, 2, 2, 2, 3, 1, 1, 1, 2, 2]
  refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun u => ?_) ⟨x⟩
  have key := bool_hno101_A (decide (G.Adj u (v 0))) (decide (G.Adj u (v 1))) (decide (G.Adj u (v 2)))
    (decide (G.Adj u (v 3))) (decide (G.Adj u (v 4))) (decide (G.Adj u (v 5))) (decide (G.Adj u (v 6)))
    (decide (G.Adj u (v 7))) (decide (G.Adj u x)) (decide (G.Adj u w))
    (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
            decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
            decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
            decide_not_both G hTF e15, decide_not_both G hTF e26, decide_not_both G hTF e37,
            decide_not_both G hTF hx1, decide_not_both G hTF hx7, decide_not_both G hTF hw4,
            decide_not_both G hTF hxw,
            decide_not_triple G (hnoA u), decide_not_quad G (hnoC u)]; rfl)
  rw [sum_fin10,
    adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
    adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 2 from rfl),
    adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 2 from rfl),
    adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 2 from rfl),
    adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 3 from rfl),
    adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 1 from rfl),
    adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 1 from rfl),
    adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 1 from rfl),
    adj_term_eq G (show pts 8 = x from rfl) (show wts 8 = 2 from rfl),
    adj_term_eq G (show pts 9 = w from rfl) (show wts 9 = 2 from rfl)]
  omega

private lemma no_101_zero {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x : V) (hx1 : G.Adj x (v 1)) (hx7 : G.Adj x (v 7)) :
    G.Adj x (v 4) := by
  by_contra hx4
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  have hne : x ≠ v 4 := by
    intro heq; rw [heq] at hx1
    exact not_adj_of_cliqueFree_three hTF e04.symm e01 hx1
  obtain ⟨w, hxw, hw4⟩ := hmax x (v 4) hne hx4
  have hw4' : G.Adj w (v 4) := hw4.symm
  by_cases hAC : (∃ a : V, G.Adj a (v 2) ∧ G.Adj a (v 4) ∧ G.Adj a x) ∨
                 (∃ a : V, G.Adj a (v 1) ∧ G.Adj a (v 3) ∧ G.Adj a (v 6) ∧ G.Adj a w)
  · have hnoB : ∀ b : V, ¬ (G.Adj b (v 4) ∧ G.Adj b (v 6) ∧ G.Adj b x) := by
      rintro b ⟨hb4, hb6, hbx⟩
      rcases hAC with ⟨a, ha2, ha4, hax⟩ | ⟨a, ha1, ha3, ha6, haw⟩
      · exact mkGrotzsch G hnoG (v 1) (v 2) (v 6) (v 7) x a (v 5) (v 3) b (v 0) (v 4)
          e12 e26 e67 hx7.symm hx1 ha2 hax e56 e15.symm e37 e23.symm hbx hb6 e01 e70.symm
          ha4.symm e45 e34.symm hb4.symm e04.symm
      · exact mkGrotzsch G hnoG (v 1) x (v 7) (v 6) a w (v 0) b (v 3) (v 5) (v 4)
          hx1.symm hx7 e67.symm ha6.symm ha1 hxw.symm haw.symm e70.symm e01 hb6 hbx ha3.symm e37
          e15.symm e56 hw4'.symm e04.symm hb4.symm e34.symm e45
    have hnoD : ∀ b : V, ¬ (G.Adj b (v 2) ∧ G.Adj b (v 5) ∧ G.Adj b (v 7) ∧ G.Adj b w) := by
      rintro b ⟨hb2, hb5, hb7, hbw⟩
      rcases hAC with ⟨a, ha2, ha4, hax⟩ | ⟨a, ha1, ha3, ha6, haw⟩
      · exact mkGrotzsch G hnoG (v 1) (v 2) b (v 7) x a (v 5) (v 3) w (v 0) (v 4)
          e12 hb2.symm hb7 hx7.symm hx1 ha2 hax hb5.symm e15.symm e37 e23.symm hxw.symm hbw.symm
          e01 e70.symm ha4.symm e45 e34.symm hw4'.symm e04.symm
      · exact mkGrotzsch G hnoG (v 1) (v 5) (v 4) w a (v 6) (v 0) b (v 3) x (v 7)
          e15 e45.symm hw4'.symm haw.symm ha1 e56.symm ha6.symm e04 e01 hbw hb5
          ha3.symm e34 hx1 hxw e67.symm e70 hb7.symm e37.symm hx7.symm
    exact no_101_caseA G hTF h14 (fun k => v (-k)) (isFullV8_neg hv) x w hx7 hx1 hw4' hxw
      (fun u ⟨h6, h4, hx⟩ => hnoB u ⟨h4, h6, hx⟩)
      (fun u ⟨h7, h5, h2, hw⟩ => hnoD u ⟨h2, h5, h7, hw⟩)
  · push Not at hAC
    exact no_101_caseA G hTF h14 v hv x w hx1 hx7 hw4' hxw
      (fun u ⟨h2, h4, hx⟩ => hAC.1 u h2 h4 hx)
      (fun u ⟨h1, h3, h6, hw⟩ => hAC.2 u h1 h3 h6 hw)

private lemma no_101 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (c : Fin 8) (x : V) (hx1 : G.Adj x (v (c + 1))) (hx7 : G.Adj x (v (c + 7))) :
    G.Adj x (v (c + 4)) :=
  no_101_zero G hTF hmax h14 hnoG (fun k => v (c + k)) (isFullV8_rot hv c) x hx1 hx7

/- Elementary Mantel bound on any subset `B` of a triangle-free graph. -/

private lemma mantel_on_finset {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hTF : G.CliqueFree 3) (B : Finset V) :
    2 * ∑ x ∈ B, #(B.filter (G.Adj x)) ≤ (#B) ^ 2 := by
  by_cases hne : B.Nonempty
  · obtain ⟨u₀, hu₀B, hu₀max⟩ := Finset.exists_max_image B (fun u => #(B.filter (G.Adj u))) hne
    let I : Finset V := B.filter (G.Adj u₀)
    have hIB : I ⊆ B := Finset.filter_subset _ _
    have hI_le : #I ≤ #B := Finset.card_le_card hIB
    have hsum_split : ∑ x ∈ B, #(B.filter (G.Adj x)) =
        ∑ x ∈ I, #(B.filter (G.Adj x)) + ∑ x ∈ B \ I, #(B.filter (G.Adj x)) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hIB]
    have h1 : ∑ x ∈ I, #(B.filter (G.Adj x)) ≤ #I * (#B - #I) := by
      calc _ ≤ ∑ _x ∈ I, (#B - #I) := by
            apply Finset.sum_le_sum; intro x hx
            have hsub : B.filter (G.Adj x) ⊆ B \ I := by
              intro y hy
              rw [Finset.mem_sdiff]
              refine ⟨(Finset.mem_filter.mp hy).1, fun hyI => ?_⟩
              exact not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp hx).2
                (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hyI).2
            have hle := Finset.card_le_card hsub
            rwa [Finset.card_sdiff_of_subset hIB] at hle
        _ = #I * (#B - #I) := by rw [Finset.sum_const, smul_eq_mul]
    have h2 : ∑ x ∈ B \ I, #(B.filter (G.Adj x)) ≤ #I * (#B - #I) := by
      calc _ ≤ ∑ _x ∈ B \ I, #I := by
            apply Finset.sum_le_sum; intro x hx
            exact hu₀max x (Finset.mem_sdiff.mp hx).1
        _ = #I * (#B - #I) := by rw [Finset.sum_const, Finset.card_sdiff_of_subset hIB, smul_eq_mul, mul_comm]
    have hsq : 4 * (#I * (#B - #I)) ≤ (#B) ^ 2 := by
      zify [hI_le]
      nlinarith [sq_nonneg ((#B : ℤ) - 2 * (#I : ℤ))]
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp

/- Step 5: Pick a `∑ #(U v j)`-maximal full `V_8`, prove `B = ∅`, and apply `not_hom_andrasfai`. -/

private lemma main_proof : OMA.Erdos128H1R1.H1 := by
  intro V _ G hTF hmax h50 h14 _hnot3 hnoG ⟨v₀, hv₀⟩ hnoA
  classical
  have hdeg : ∀ x : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj x)) := by
    intro x
    have h1 := h14 x
    rw [Set.ncard_eq_toFinset_card'] at h1
    have h2 : (G.neighborSet x).toFinset = univ.filter (G.Adj x) := by ext y; simp
    rwa [h2] at h1
  have hv₀_full : IsFullV8 G v₀ := exists_full_v8 G hTF hmax hdeg hnoG v₀ hv₀
  let fullV8s : Finset (Fin 8 → V) := univ.filter (fun v => IsFullV8 G v)
  have hv₀_mem : v₀ ∈ fullV8s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₀_full⟩
  obtain ⟨v, hv_mem, hv_max⟩ :=
    Finset.exists_max_image fullV8s (fun w => ∑ j : Fin 8, #(Uset G w j)) ⟨v₀, hv₀_mem⟩
  have hv : IsFullV8 G v := (Finset.mem_filter.mp hv_mem).2
  set n := Fintype.card V
  have hmem_v : ∀ j : Fin 8, v j ∈ Uset G v j := fun j =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hv j (j + 1) (Or.inl rfl), hv j (j + 4) (Or.inr (Or.inl rfl)), hv j (j + 7) (Or.inr (Or.inr rfl))⟩
  have hU_exact : ∀ j : Fin 8, ∀ w ∈ Uset G v j, ∀ i : Fin 8,
      G.Adj w (v i) ↔ (i = j + 1 ∨ i = j + 4 ∨ i = j + 7) := by
    intro j w hw i
    have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hw).2
    constructor
    · intro hwi
      by_contra hnot
      have hna : ∀ p q : Fin 8, (q = p + 1 ∨ q = p + 4 ∨ q = p + 7) →
          G.Adj w (v p) → G.Adj w (v q) → False :=
        fun p q hpq hp hq => not_adj_of_cliqueFree_three hTF hp (hv p q hpq) hq
      fin_cases j <;> fin_cases i <;> simp at hnot
      all_goals first
        | exact hna _ _ (by decide) hwi a1 | exact hna _ _ (by decide) hwi a4
        | exact hna _ _ (by decide) hwi a7
    · rintro (rfl | rfl | rfl) <;> assumption
  -- Classify every vertex `x` via `v8_indep_subset_nbhd`
  have hex_cls : ∀ x : V, ∃ c : Fin 8, ∀ j : Fin 8, (∃ y ∈ Uset G v j, G.Adj x y) →
      j = c + 1 ∨ j = c + 4 ∨ j = c + 7 := by
    intro x
    let J : Finset (Fin 8) := univ.filter (fun j => ∃ y ∈ Uset G v j, G.Adj x y)
    have hJ_indep : ∀ i ∈ J, ∀ j ∈ J, ¬ (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) := by
      intro i hi j hj hij
      obtain ⟨y1, hy1, hxy1⟩ := (Finset.mem_filter.mp hi).2
      obtain ⟨y2, hy2, hxy2⟩ := (Finset.mem_filter.mp hj).2
      exact no_hit_v8_edge G hTF hdeg hnoG hnoA v hv x i j hij y1 hy1 y2 hy2 hxy1 hxy2
    obtain ⟨c, hc⟩ := v8_indep_subset_nbhd J hJ_indep
    exact ⟨c, fun j hj => hc j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩
  let cls : V → Fin 8 := fun x => (hex_cls x).choose
  have hcls_spec : ∀ x : V, ∀ j : Fin 8, ∀ y ∈ Uset G v j, G.Adj x y →
      j = cls x + 1 ∨ j = cls x + 4 ∨ j = cls x + 7 :=
    fun x j y hy hxy => (hex_cls x).choose_spec j ⟨y, hy, hxy⟩
  let B : Finset V := univ.filter (fun x => ∀ j : Fin 8, x ∉ Uset G v j)
  -- Every `x ∈ B` misses either all of `U v (cls x + 1)` or all of `U v (cls x + 7)`
  have hB_miss : ∀ x ∈ B,
      (∀ y ∈ Uset G v (cls x + 1), ¬ G.Adj x y) ∨
      (∀ y ∈ Uset G v (cls x + 7), ¬ G.Adj x y) := by
    intro x hxB
    by_contra hboth
    push Not at hboth
    obtain ⟨⟨y1, hy1, hxy1⟩, ⟨y7, hy7, hxy7⟩⟩ := hboth
    have h17 : cls x + 1 ≠ cls x + 7 := by generalize cls x = c; fin_cases c <;> decide
    set c := cls x
    let v' : Fin 8 → V := fun k => if k = c + 1 then y1 else if k = c + 7 then y7 else v k
    have hv'_memU : ∀ k : Fin 8, v' k ∈ Uset G v k := by
      intro k; dsimp only [v']
      split_ifs with h1 h7
      · subst h1; exact hy1
      · subst h7; exact hy7
      · exact hmem_v k
    have hv'_full : IsFullV8 G v' := fun i j hij =>
      uset_complete G hTF hmax hdeg hnoG hnoA v hv i j hij (v' i) (hv'_memU i) (v' j) (hv'_memU j)
    have hU_sub : ∀ k : Fin 8, Uset G v k ⊆ Uset G v' k := by
      intro k u hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
      · exact uset_complete G hTF hmax hdeg hnoG hnoA v hv k (k + 1) (Or.inl rfl) u hu (v' (k + 1)) (hv'_memU (k + 1))
      · exact uset_complete G hTF hmax hdeg hnoG hnoA v hv k (k + 4) (Or.inr (Or.inl rfl)) u hu (v' (k + 4)) (hv'_memU (k + 4))
      · exact uset_complete G hTF hmax hdeg hnoG hnoA v hv k (k + 7) (Or.inr (Or.inr rfl)) u hu (v' (k + 7)) (hv'_memU (k + 7))
    have hx_v'1 : G.Adj x (v' (c + 1)) := by dsimp only [v']; rw [if_pos rfl]; exact hxy1
    have hx_v'7 : G.Adj x (v' (c + 7)) := by
      dsimp only [v']; rw [if_neg h17.symm, if_pos rfl]; exact hxy7
    have hx_v'4 : G.Adj x (v' (c + 4)) := no_101 G hTF hmax hdeg hnoG v' hv'_full c x hx_v'1 hx_v'7
    have hx_in' : x ∈ Uset G v' c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx_v'1, hx_v'4, hx_v'7⟩
    have hx_notin : x ∉ Uset G v c := (Finset.mem_filter.mp hxB).2 c
    have hlt_c : #(Uset G v c) < #(Uset G v' c) :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hU_sub c, fun heq => hx_notin (heq ▸ hx_in')⟩)
    have hsum_lt : ∑ k : Fin 8, #(Uset G v k) < ∑ k : Fin 8, #(Uset G v' k) :=
      Finset.sum_lt_sum (fun k _ => Finset.card_le_card (hU_sub k)) ⟨c, Finset.mem_univ c, hlt_c⟩
    have hv'_le := hv_max v' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'_full⟩)
    omega
  -- Every `w ∈ B` hits at most 2 vertices of `{v 0, ..., v 7}`
  have hB_cap2 : ∀ w ∈ B, #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) ≤ 2 := by
    intro w hwB
    have hsub : univ.filter (fun i : Fin 8 => G.Adj w (v i)) ⊆ ({cls w + 1, cls w + 4, cls w + 7} : Finset (Fin 8)) := by
      intro i hi
      have hwi := (Finset.mem_filter.mp hi).2
      have := hcls_spec w i (v i) (hmem_v i) hwi
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have hne_all : univ.filter (fun i : Fin 8 => G.Adj w (v i)) ≠ ({cls w + 1, cls w + 4, cls w + 7} : Finset (Fin 8)) := by
      intro heq
      have h1 : cls w + 1 ∈ univ.filter (fun i : Fin 8 => G.Adj w (v i)) := by rw [heq]; simp
      have h4 : cls w + 4 ∈ univ.filter (fun i : Fin 8 => G.Adj w (v i)) := by rw [heq]; simp
      have h7 : cls w + 7 ∈ univ.filter (fun i : Fin 8 => G.Adj w (v i)) := by rw [heq]; simp
      exact (Finset.mem_filter.mp hwB).2 (cls w) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h4).2, (Finset.mem_filter.mp h7).2⟩)
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne_all⟩)
    have hcard3 : #({cls w + 1, cls w + 4, cls w + 7} : Finset (Fin 8)) ≤ 3 :=
      (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
    omega
  -- Partition `B` into `E0 c` (misses `U (c + 1)`) and `E2 c` (misses `U (c + 7)`)
  let E0 : Fin 8 → Finset V := fun c =>
    B.filter (fun x => cls x = c ∧ ∀ y ∈ Uset G v (c + 1), ¬ G.Adj x y)
  let E2 : Fin 8 → Finset V := fun c =>
    B.filter (fun x => cls x = c ∧ ∀ y ∈ Uset G v (c + 7), ¬ G.Adj x y)
  -- Sharp 5-weight vertex count for `E2 c`
  have hbound_E2 : ∀ c : Fin 8,
      14 * (#(Uset G v (c + 1)) + #(Uset G v (c + 4))) + 7 * #B + 14 * #(E2 c) ≤ 5 * n := by
    intro c
    have hpt : ∀ w : V,
        (if w ∈ Uset G v (c + 1) then 2 else 0) + (if w ∈ Uset G v (c + 4) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 6)) then 2 else 0) + (if G.Adj w (v (c + 7)) then 2 else 0) +
        (if w ∈ E2 c then 2 else 0) ≤ 5 := by
      intro w
      by_cases hwB : w ∈ B
      · have hnot1 : w ∉ Uset G v (c + 1) := (Finset.mem_filter.mp hwB).2 (c + 1)
        have hnot4 : w ∉ Uset G v (c + 4) := (Finset.mem_filter.mp hwB).2 (c + 4)
        have hcap := hB_cap2 w hwB
        have h67 : G.Adj (v (c + 6)) (v (c + 7)) := hv (c + 6) (c + 7) (Or.inl (by fin_cases c <;> decide))
        by_cases hwE : w ∈ E2 c
        · have ⟨hclsw, hmiss7⟩ := (Finset.mem_filter.mp hwE).2
          have hno7 : ¬ G.Adj w (v (c + 7)) := hmiss7 (v (c + 7)) (hmem_v (c + 7))
          have hno6 : ¬ G.Adj w (v (c + 6)) := by
            intro h6
            have hmem := hcls_spec w (c + 6) (v (c + 6)) (hmem_v (c + 6)) h6
            rw [hclsw] at hmem
            fin_cases c <;> simp at hmem
          simp [hnot1, hnot4, hwB, hwE, hno6, hno7]; omega
        · by_cases h6 : G.Adj w (v (c + 6)) <;> by_cases h7 : G.Adj w (v (c + 7))
          · exact (not_adj_of_cliqueFree_three hTF h6 h67 h7).elim
          all_goals (simp [hnot1, hnot4, hwB, hwE, h6, h7]; omega)
      · have hexU : ∃ k : Fin 8, w ∈ Uset G v k := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
        obtain ⟨k, hwk⟩ := hexU
        have hnotE : w ∉ E2 c := fun h => hwB (Finset.mem_filter.mp h).1
        have hmem_iff : ∀ j : Fin 8, w ∈ Uset G v j ↔ k = j := by
          intro j; constructor
          · intro hwj; by_contra hne
            exact Finset.disjoint_left.mp (uset_disjoint G hTF v hv hne) hwk hwj
          · rintro rfl; exact hwk
        have hdeg3 : #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) = 3 := by
          have heq : univ.filter (fun i : Fin 8 => G.Adj w (v i)) = {k + 1, k + 4, k + 7} := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton]
            exact hU_exact k w hwk i
          rw [heq]; fin_cases k <;> decide
        have h6iff : G.Adj w (v (c + 6)) ↔ (c + 6 = k + 1 ∨ c + 6 = k + 4 ∨ c + 6 = k + 7) :=
          hU_exact k w hwk (c + 6)
        have h7iff : G.Adj w (v (c + 7)) ↔ (c + 7 = k + 1 ∨ c + 7 = k + 4 ∨ c + 7 = k + 7) :=
          hU_exact k w hwk (c + 7)
        simp only [hwB, hnotE, if_false, add_zero, hdeg3, hmem_iff, h6iff, h7iff]
        fin_cases c <;> fin_cases k <;> decide
    have hsum_le : ∑ w : V, ((if w ∈ Uset G v (c + 1) then 2 else 0) + (if w ∈ Uset G v (c + 4) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 6)) then 2 else 0) + (if G.Adj w (v (c + 7)) then 2 else 0) +
        (if w ∈ E2 c then 2 else 0)) ≤ 5 * n := by
      calc _ ≤ ∑ _w : V, 5 := Finset.sum_le_sum (fun w _ => hpt w)
        _ = 5 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_eq : ∑ w : V, ((if w ∈ Uset G v (c + 1) then 2 else 0) + (if w ∈ Uset G v (c + 4) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 6)) then 2 else 0) + (if G.Adj w (v (c + 7)) then 2 else 0) +
        (if w ∈ E2 c then 2 else 0)) =
        2 * #(Uset G v (c + 1)) + 2 * #(Uset G v (c + 4)) + #B +
        (∑ i : Fin 8, #(univ.filter (G.Adj (v i)))) +
        2 * #(univ.filter (G.Adj (v (c + 6)))) + 2 * #(univ.filter (G.Adj (v (c + 7)))) +
        2 * #(E2 c) := by
      simp_rw [Finset.sum_add_distrib]
      have hconst : ∀ (S : Finset V) (a : ℕ), ∑ w : V, (if w ∈ S then a else 0) = a * #S := by
        intro S a
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, smul_eq_mul, mul_comm]
      have hadj : ∀ (u : V) (a : ℕ), ∑ w : V, (if G.Adj w u then a else 0) = a * #(univ.filter (G.Adj u)) := by
        intro u a
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 2; ext w; simp [G.adj_comm]
      have hswap : ∑ w : V, #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) =
          ∑ i : Fin 8, #(univ.filter (G.Adj (v i))) := by
        simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
      rw [hconst, hconst, hconst, one_mul, hswap, hadj, hadj, hconst]
    have h8deg : 40 * n ≤ 14 * ∑ i : Fin 8, #(univ.filter (G.Adj (v i))) := by
      rw [Finset.mul_sum]
      calc 40 * n = ∑ _i : Fin 8, 5 * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hdeg (v i))
    have hd6 := hdeg (v (c + 6))
    have hd7 := hdeg (v (c + 7))
    omega
  -- Symmetric 5-weight vertex count for `E0 c`
  have hbound_E0 : ∀ c : Fin 8,
      14 * (#(Uset G v (c + 4)) + #(Uset G v (c + 7))) + 7 * #B + 14 * #(E0 c) ≤ 5 * n := by
    intro c
    have hpt : ∀ w : V,
        (if w ∈ Uset G v (c + 4) then 2 else 0) + (if w ∈ Uset G v (c + 7) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 1)) then 2 else 0) + (if G.Adj w (v (c + 2)) then 2 else 0) +
        (if w ∈ E0 c then 2 else 0) ≤ 5 := by
      intro w
      by_cases hwB : w ∈ B
      · have hnot4 : w ∉ Uset G v (c + 4) := (Finset.mem_filter.mp hwB).2 (c + 4)
        have hnot7 : w ∉ Uset G v (c + 7) := (Finset.mem_filter.mp hwB).2 (c + 7)
        have hcap := hB_cap2 w hwB
        have h12 : G.Adj (v (c + 1)) (v (c + 2)) := hv (c + 1) (c + 2) (Or.inl (by fin_cases c <;> decide))
        by_cases hwE : w ∈ E0 c
        · have ⟨hclsw, hmiss1⟩ := (Finset.mem_filter.mp hwE).2
          have hno1 : ¬ G.Adj w (v (c + 1)) := hmiss1 (v (c + 1)) (hmem_v (c + 1))
          have hno2 : ¬ G.Adj w (v (c + 2)) := by
            intro h2
            have hmem := hcls_spec w (c + 2) (v (c + 2)) (hmem_v (c + 2)) h2
            rw [hclsw] at hmem
            fin_cases c <;> simp at hmem
          simp [hnot4, hnot7, hwB, hwE, hno1, hno2]; omega
        · by_cases h1 : G.Adj w (v (c + 1)) <;> by_cases h2 : G.Adj w (v (c + 2))
          · exact (not_adj_of_cliqueFree_three hTF h1 h12 h2).elim
          all_goals (simp [hnot4, hnot7, hwB, hwE, h1, h2]; omega)
      · have hexU : ∃ k : Fin 8, w ∈ Uset G v k := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
        obtain ⟨k, hwk⟩ := hexU
        have hnotE : w ∉ E0 c := fun h => hwB (Finset.mem_filter.mp h).1
        have hmem_iff : ∀ j : Fin 8, w ∈ Uset G v j ↔ k = j := by
          intro j; constructor
          · intro hwj; by_contra hne
            exact Finset.disjoint_left.mp (uset_disjoint G hTF v hv hne) hwk hwj
          · rintro rfl; exact hwk
        have hdeg3 : #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) = 3 := by
          have heq : univ.filter (fun i : Fin 8 => G.Adj w (v i)) = {k + 1, k + 4, k + 7} := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton]
            exact hU_exact k w hwk i
          rw [heq]; fin_cases k <;> decide
        have h1iff : G.Adj w (v (c + 1)) ↔ (c + 1 = k + 1 ∨ c + 1 = k + 4 ∨ c + 1 = k + 7) :=
          hU_exact k w hwk (c + 1)
        have h2iff : G.Adj w (v (c + 2)) ↔ (c + 2 = k + 1 ∨ c + 2 = k + 4 ∨ c + 2 = k + 7) :=
          hU_exact k w hwk (c + 2)
        simp only [hwB, hnotE, if_false, add_zero, hdeg3, hmem_iff, h1iff, h2iff]
        fin_cases c <;> fin_cases k <;> decide
    have hsum_le : ∑ w : V, ((if w ∈ Uset G v (c + 4) then 2 else 0) + (if w ∈ Uset G v (c + 7) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 1)) then 2 else 0) + (if G.Adj w (v (c + 2)) then 2 else 0) +
        (if w ∈ E0 c then 2 else 0)) ≤ 5 * n := by
      calc _ ≤ ∑ _w : V, 5 := Finset.sum_le_sum (fun w _ => hpt w)
        _ = 5 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_eq : ∑ w : V, ((if w ∈ Uset G v (c + 4) then 2 else 0) + (if w ∈ Uset G v (c + 7) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 1)) then 2 else 0) + (if G.Adj w (v (c + 2)) then 2 else 0) +
        (if w ∈ E0 c then 2 else 0)) =
        2 * #(Uset G v (c + 4)) + 2 * #(Uset G v (c + 7)) + #B +
        (∑ i : Fin 8, #(univ.filter (G.Adj (v i)))) +
        2 * #(univ.filter (G.Adj (v (c + 1)))) + 2 * #(univ.filter (G.Adj (v (c + 2)))) +
        2 * #(E0 c) := by
      simp_rw [Finset.sum_add_distrib]
      have hconst : ∀ (S : Finset V) (a : ℕ), ∑ w : V, (if w ∈ S then a else 0) = a * #S := by
        intro S a
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, smul_eq_mul, mul_comm]
      have hadj : ∀ (u : V) (a : ℕ), ∑ w : V, (if G.Adj w u then a else 0) = a * #(univ.filter (G.Adj u)) := by
        intro u a
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 2; ext w; simp [G.adj_comm]
      have hswap : ∑ w : V, #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) =
          ∑ i : Fin 8, #(univ.filter (G.Adj (v i))) := by
        simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
      rw [hconst, hconst, hconst, one_mul, hswap, hadj, hadj, hconst]
    have h8deg : 40 * n ≤ 14 * ∑ i : Fin 8, #(univ.filter (G.Adj (v i))) := by
      rw [Finset.mul_sum]
      calc 40 * n = ∑ _i : Fin 8, 5 * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hdeg (v i))
    have hd1 := hdeg (v (c + 1))
    have hd2 := hdeg (v (c + 2))
    omega
  -- Prove `B = ∅` via Mantel on `G[B]`
  have hB_empty : B = ∅ := by
    by_contra hBne
    have hBpos : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBne
    let Uall : Finset V := univ \ B
    have hUall_bound : ∀ x ∈ B, 14 * #(Uall.filter (G.Adj x)) + 7 * #B < 5 * n := by
      intro x hxB
      set c := cls x
      rcases hB_miss x hxB with hmiss1 | hmiss7
      · have hxE0 : x ∈ E0 c := Finset.mem_filter.mpr ⟨hxB, rfl, hmiss1⟩
        have hpos : 1 ≤ #(E0 c) := Finset.card_pos.mpr ⟨x, hxE0⟩
        have hsub : Uall.filter (G.Adj x) ⊆ Uset G v (c + 4) ∪ Uset G v (c + 7) := by
          intro y hy
          have ⟨hyU, hxy⟩ := Finset.mem_filter.mp hy
          have hy_notB : y ∉ B := (Finset.mem_sdiff.mp hyU).2
          have hexU : ∃ j : Fin 8, y ∈ Uset G v j := by
            by_contra hnone; push Not at hnone
            exact hy_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
          obtain ⟨j, hyj⟩ := hexU
          rcases hcls_spec x j y hyj hxy with rfl | rfl | rfl
          · exact (hmiss1 y hyj hxy).elim
          · exact Finset.mem_union_left _ hyj
          · exact Finset.mem_union_right _ hyj
        have hle : #(Uall.filter (G.Adj x)) ≤ #(Uset G v (c + 4)) + #(Uset G v (c + 7)) :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hb := hbound_E0 c
        omega
      · have hxE2 : x ∈ E2 c := Finset.mem_filter.mpr ⟨hxB, rfl, hmiss7⟩
        have hpos : 1 ≤ #(E2 c) := Finset.card_pos.mpr ⟨x, hxE2⟩
        have hsub : Uall.filter (G.Adj x) ⊆ Uset G v (c + 1) ∪ Uset G v (c + 4) := by
          intro y hy
          have ⟨hyU, hxy⟩ := Finset.mem_filter.mp hy
          have hy_notB : y ∉ B := (Finset.mem_sdiff.mp hyU).2
          have hexU : ∃ j : Fin 8, y ∈ Uset G v j := by
            by_contra hnone; push Not at hnone
            exact hy_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
          obtain ⟨j, hyj⟩ := hexU
          rcases hcls_spec x j y hyj hxy with rfl | rfl | rfl
          · exact Finset.mem_union_left _ hyj
          · exact Finset.mem_union_right _ hyj
          · exact (hmiss7 y hyj hxy).elim
        have hle : #(Uall.filter (G.Adj x)) ≤ #(Uset G v (c + 1)) + #(Uset G v (c + 4)) :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hb := hbound_E2 c
        omega
    have hsum_lt : ∑ x ∈ B, (14 * #(Uall.filter (G.Adj x)) + 7 * #B) < ∑ _x ∈ B, (5 * n) :=
      Finset.sum_lt_sum_of_nonempty hBpos hUall_bound
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.sum_const,
      smul_eq_mul, smul_eq_mul] at hsum_lt
    have hdeg_split : ∀ x ∈ B, #(univ.filter (G.Adj x)) = #(Uall.filter (G.Adj x)) + #(B.filter (G.Adj x)) := by
      intro x _
      have hunion : Uall ∪ B = univ := Finset.sdiff_union_of_subset (Finset.subset_univ B)
      have hdisj : Disjoint Uall B := Finset.sdiff_disjoint
      rw [← hunion, Finset.filter_union,
        Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    have hdeg_sum : #B * (5 * n) ≤ 14 * ∑ x ∈ B, #(Uall.filter (G.Adj x)) + 14 * ∑ x ∈ B, #(B.filter (G.Adj x)) := by
      calc #B * (5 * n) = ∑ _x ∈ B, 5 * n := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ x ∈ B, 14 * #(univ.filter (G.Adj x)) := Finset.sum_le_sum (fun x _ => hdeg x)
        _ = ∑ x ∈ B, (14 * #(Uall.filter (G.Adj x)) + 14 * #(B.filter (G.Adj x))) := by
            apply Finset.sum_congr rfl; intro x hx; rw [hdeg_split x hx, mul_add]
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hmantel := mantel_on_finset G hTF B
    have hsq : #B * (7 * #B) = 7 * (#B) ^ 2 := by ring
    omega
  -- Every vertex `x` lies in `Uset G v (cls x)`, so `cls` is a homomorphism `G → V_8`!
  have hall_U : ∀ x : V, x ∈ Uset G v (cls x) := by
    intro x
    have hx_notB : x ∉ B := by rw [hB_empty]; simp
    have hexU : ∃ j : Fin 8, x ∈ Uset G v j := by
      by_contra hnone; push Not at hnone
      exact hx_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
    obtain ⟨j, hxj⟩ := hexU
    have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hxj).2
    have h1 := hcls_spec x (j + 1) (v (j + 1)) (hmem_v (j + 1)) a1
    have h4 := hcls_spec x (j + 4) (v (j + 4)) (hmem_v (j + 4)) a4
    have h7 := hcls_spec x (j + 7) (v (j + 7)) (hmem_v (j + 7)) a7
    have heq : j = cls x := by
      generalize cls x = c at h1 h4 h7 ⊢
      fin_cases j <;> fin_cases c <;> simp at h1 h4 h7 ⊢
    rwa [← heq]
  have hcls_hom : ∀ x y : V, G.Adj x y → cls y = cls x + 1 ∨ cls y = cls x + 4 ∨ cls y = cls x + 7 :=
    fun x y hxy => hcls_spec x (cls y) y (hall_U y) hxy
  -- Convert Möbius labeling (`+1, +4, +7`) to consecutive `And(3)` (`+3, +4, +5`) via `3 * cls x`
  let φ : V → Fin 8 := fun x => 3 * cls x
  have hφ : ∀ x y : V, G.Adj x y →
      3 ≤ ((φ y).val + (3 * 3 - 1) - (φ x).val) % (3 * 3 - 1) ∧
      ((φ y).val + (3 * 3 - 1) - (φ x).val) % (3 * 3 - 1) < 2 * 3 := by
    intro x y hxy
    have h := hcls_hom x y hxy
    dsimp only [φ]
    rcases h with h | h | h <;> rw [h] <;> (generalize cls x = a; fin_cases a <;> decide)
  exact not_hom_andrasfai G h50 (fun H hHTF hHH => five_mul_edges_lt_sq H hHTF hHH) 3 (by decide) φ hφ

end Erdos128_R2_H1_R1_H1

theorem h1_proof : OMA.Erdos128H1R1.H1 :=
  Erdos128_R2_H1_R1_H1.main_proof
end H1Section

section H2Section
/-
# Proof of `Erdos128.erdos_128.R2.H1.R1.H2`

We eliminate the Band subcase containing a homomorphic image `φ : And(4) → G`
directly from triangle-freeness, `δ(G) ≥ (5 / 14) n`, and the half-vertex edge
lower bound `∀ V', 2 * |V'| + 1 ≥ n → 50 * e(G[V']) > n^2`.

Every vertex `v` is classified by its `φ`-neighborhood `I(v) ⊆ Fin 11`, which
must be one of the 89 independent sets of `And(4)`. For each of the 22 pairs
`(i, d) ∈ Fin 11 × {+1, -1}`, taking `S_i = N_G(φ i)` together with the first
`t_i = n / 2 - |S_i|` vertices from the disjoint independent set
`V'_{i + 2d} ∪ V'_{i + 5d}` yields a half-size set `V'` whose edge count is
bounded by `t_i * |D1_{i,d}| + max(0, t_i - |V'_{i+2d}|) * |DIFF_{i,d}|`.
Relaxing `max(0, U) * y ≤ (U + y)^2 / 4` and summing over all 22 pairs gives a
strictly positive quadratic form in the 89 type counts `x_a`, which is
contradicted by an exact `ℤ/11`-invariant linear multiplier certificate against
the 11 degree inequalities `14 * |S_k| - 5 * n ≥ 0`.
-/

namespace Erdos128_R2_H1_R1_H2

/-- Powers of 2 for `Fin 11`. -/
def pow2 (k : Fin 11) : ℕ :=
  match k.1 with
  | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 8 | 4 => 16 | 5 => 32
  | 6 => 64 | 7 => 128 | 8 => 256 | 9 => 512 | _ => 1024

/-- Bit test using kernel-reduced integer division and mod. -/
def hasBit (m : ℕ) (k : Fin 11) : Bool :=
  (m / pow2 k) % 2 == 1

/-- Test whether an 11-bit mask represents an independent set of `And(4)`. -/
def isIndepMask (m : ℕ) : Bool :=
  (List.finRange 11).all fun i =>
    !hasBit m i || (!hasBit m (i + 1) && !hasBit m (i + 4) && !hasBit m (i + 7) && !hasBit m (i + 10))

/-- The 89 bitmasks of independent sets of `And(4)`. -/
def maskOf (a : Fin 89) : ℕ :=
  match a.1 with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 8 | 5 => 16 | 6 => 32 | 7 => 64 | 8 => 128
  | 9 => 256 | 10 => 512 | 11 => 1024 | 12 => 5 | 13 => 9 | 14 => 33 | 15 => 65 | 16 => 257
  | 17 => 513 | 18 => 10 | 19 => 18 | 20 => 66 | 21 => 130 | 22 => 514 | 23 => 1026 | 24 => 20
  | 25 => 36 | 26 => 132 | 27 => 260 | 28 => 1028 | 29 => 40 | 30 => 72 | 31 => 264 | 32 => 520
  | 33 => 80 | 34 => 144 | 35 => 528 | 36 => 1040 | 37 => 160 | 38 => 288 | 39 => 1056 | 40 => 320
  | 41 => 576 | 42 => 640 | 43 => 1152 | 44 => 1280 | 45 => 37 | 46 => 261 | 47 => 41 | 48 => 73
  | 49 => 265 | 50 => 521 | 51 => 289 | 52 => 321 | 53 => 577 | 54 => 74 | 55 => 522 | 56 => 82
  | 57 => 146 | 58 => 530 | 59 => 1042 | 60 => 578 | 61 => 642 | 62 => 1154 | 63 => 148 | 64 => 1044
  | 65 => 164 | 66 => 292 | 67 => 1060 | 68 => 1156 | 69 => 1284 | 70 => 296 | 71 => 328 | 72 => 584
  | 73 => 592 | 74 => 656 | 75 => 1168 | 76 => 1184 | 77 => 1312 | 78 => 293 | 79 => 297 | 80 => 329
  | 81 => 585 | 82 => 586 | 83 => 594 | 84 => 658 | 85 => 1170 | 86 => 1172 | 87 => 1188 | _ => 1316

/-- Inverse lookup from an independent-set bitmask to `Fin 89`. -/
def idxOfMask (m : ℕ) : Fin 89 :=
  match m with
  | 0 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 8 => 4 | 16 => 5 | 32 => 6 | 64 => 7 | 128 => 8
  | 256 => 9 | 512 => 10 | 1024 => 11 | 5 => 12 | 9 => 13 | 33 => 14 | 65 => 15 | 257 => 16
  | 513 => 17 | 10 => 18 | 18 => 19 | 66 => 20 | 130 => 21 | 514 => 22 | 1026 => 23 | 20 => 24
  | 36 => 25 | 132 => 26 | 260 => 27 | 1028 => 28 | 40 => 29 | 72 => 30 | 264 => 31 | 520 => 32
  | 80 => 33 | 144 => 34 | 528 => 35 | 1040 => 36 | 160 => 37 | 288 => 38 | 1056 => 39 | 320 => 40
  | 576 => 41 | 640 => 42 | 1152 => 43 | 1280 => 44 | 37 => 45 | 261 => 46 | 41 => 47 | 73 => 48
  | 265 => 49 | 521 => 50 | 289 => 51 | 321 => 52 | 577 => 53 | 74 => 54 | 522 => 55 | 82 => 56
  | 146 => 57 | 530 => 58 | 1042 => 59 | 578 => 60 | 642 => 61 | 1154 => 62 | 148 => 63 | 1044 => 64
  | 164 => 65 | 292 => 66 | 1060 => 67 | 1156 => 68 | 1284 => 69 | 296 => 70 | 328 => 71 | 584 => 72
  | 592 => 73 | 656 => 74 | 1168 => 75 | 1184 => 76 | 1312 => 77 | 293 => 78 | 297 => 79 | 329 => 80
  | 585 => 81 | 586 => 82 | 594 => 83 | 658 => 84 | 1170 => 85 | 1172 => 86 | 1188 => 87 | 1316 => 88
  | _ => 0

/-- `+1` cyclic shift on `Fin 89`. -/
def sh1 (a : Fin 89) : Fin 89 :=
  match a.1 with
  | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 8 | 8 => 9
  | 9 => 10 | 10 => 11 | 11 => 1 | 12 => 18 | 13 => 19 | 14 => 20 | 15 => 21 | 16 => 22
  | 17 => 23 | 18 => 24 | 19 => 25 | 20 => 26 | 21 => 27 | 22 => 28 | 23 => 12 | 24 => 29
  | 25 => 30 | 26 => 31 | 27 => 32 | 28 => 13 | 29 => 33 | 30 => 34 | 31 => 35 | 32 => 36
  | 33 => 37 | 34 => 38 | 35 => 39 | 36 => 14 | 37 => 40 | 38 => 41 | 39 => 15 | 40 => 42
  | 41 => 43 | 42 => 44 | 43 => 16 | 44 => 17 | 45 => 54 | 46 => 55 | 47 => 56 | 48 => 57
  | 49 => 58 | 50 => 59 | 51 => 60 | 52 => 61 | 53 => 62 | 54 => 63 | 55 => 64 | 56 => 65
  | 57 => 66 | 58 => 67 | 59 => 45 | 60 => 68 | 61 => 69 | 62 => 46 | 63 => 70 | 64 => 47
  | 65 => 71 | 66 => 72 | 67 => 48 | 68 => 49 | 69 => 50 | 70 => 73 | 71 => 74 | 72 => 75
  | 73 => 76 | 74 => 77 | 75 => 51 | 76 => 52 | 77 => 53 | 78 => 82 | 79 => 83 | 80 => 84
  | 81 => 85 | 82 => 86 | 83 => 87 | 84 => 88 | 85 => 78 | 86 => 79 | 87 => 80 | _ => 81

/-- `-1` cyclic shift on `Fin 89`. -/
def invSh1 (a : Fin 89) : Fin 89 :=
  match a.1 with
  | 0 => 0 | 1 => 11 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 5 | 7 => 6 | 8 => 7
  | 9 => 8 | 10 => 9 | 11 => 10 | 12 => 23 | 13 => 28 | 14 => 36 | 15 => 39 | 16 => 43
  | 17 => 44 | 18 => 12 | 19 => 13 | 20 => 14 | 21 => 15 | 22 => 16 | 23 => 17 | 24 => 18
  | 25 => 19 | 26 => 20 | 27 => 21 | 28 => 22 | 29 => 24 | 30 => 25 | 31 => 26 | 32 => 27
  | 33 => 29 | 34 => 30 | 35 => 31 | 36 => 32 | 37 => 33 | 38 => 34 | 39 => 35 | 40 => 37
  | 41 => 38 | 42 => 40 | 43 => 41 | 44 => 42 | 45 => 59 | 46 => 62 | 47 => 64 | 48 => 67
  | 49 => 68 | 50 => 69 | 51 => 75 | 52 => 76 | 53 => 77 | 54 => 45 | 55 => 46 | 56 => 47
  | 57 => 48 | 58 => 49 | 59 => 50 | 60 => 51 | 61 => 52 | 62 => 53 | 63 => 54 | 64 => 55
  | 65 => 56 | 66 => 57 | 67 => 58 | 68 => 60 | 69 => 61 | 70 => 63 | 71 => 65 | 72 => 66
  | 73 => 70 | 74 => 71 | 75 => 72 | 76 => 73 | 77 => 74 | 78 => 85 | 79 => 86 | 80 => 87
  | 81 => 88 | 82 => 78 | 83 => 79 | 84 => 80 | 85 => 81 | 86 => 82 | 87 => 83 | _ => 84

def sh (k : Fin 11) (a : Fin 89) : Fin 89 := sh1^[k.1] a
def invSh (k : Fin 11) (a : Fin 89) : Fin 89 := invSh1^[k.1] a

/-- Representatives of the 9 `ℤ/11`-orbits on `Fin 89`. -/
def rep (r : Fin 9) : Fin 89 :=
  match r.1 with
  | 0 => 0 | 1 => 1 | 2 => 12 | 3 => 13 | 4 => 14 | 5 => 45 | 6 => 46 | 7 => 48 | _ => 78

def orbId (a : Fin 89) : Fin 9 :=
  match a.1 with
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1
  | 9 => 1 | 10 => 1 | 11 => 1 | 12 => 2 | 13 => 3 | 14 => 4 | 15 => 4 | 16 => 3 | 17 => 2
  | 18 => 2 | 19 => 3 | 20 => 4 | 21 => 4 | 22 => 3 | 23 => 2 | 24 => 2 | 25 => 3 | 26 => 4
  | 27 => 4 | 28 => 3 | 29 => 2 | 30 => 3 | 31 => 4 | 32 => 4 | 33 => 2 | 34 => 3 | 35 => 4
  | 36 => 4 | 37 => 2 | 38 => 3 | 39 => 4 | 40 => 2 | 41 => 3 | 42 => 2 | 43 => 3 | 44 => 2
  | 45 => 5 | 46 => 6 | 47 => 6 | 48 => 7 | 49 => 7 | 50 => 5 | 51 => 7 | 52 => 5 | 53 => 6
  | 54 => 5 | 55 => 6 | 56 => 6 | 57 => 7 | 58 => 7 | 59 => 5 | 60 => 7 | 61 => 5 | 62 => 6
  | 63 => 5 | 64 => 6 | 65 => 6 | 66 => 7 | 67 => 7 | 68 => 7 | 69 => 5 | 70 => 5 | 71 => 6
  | 72 => 7 | 73 => 5 | 74 => 6 | 75 => 7 | 76 => 5 | 77 => 6 | 78 => 8 | 79 => 8 | 80 => 8
  | 81 => 8 | 82 => 8 | 83 => 8 | 84 => 8 | 85 => 8 | 86 => 8 | 87 => 8 | _ => 8

def orbSh (a : Fin 89) : Fin 11 :=
  match a.1 with
  | 0 => 10 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 5 | 7 => 6 | 8 => 7
  | 9 => 8 | 10 => 9 | 11 => 10 | 12 => 0 | 13 => 0 | 14 => 0 | 15 => 6 | 16 => 8 | 17 => 9
  | 18 => 1 | 19 => 1 | 20 => 1 | 21 => 7 | 22 => 9 | 23 => 10 | 24 => 2 | 25 => 2 | 26 => 2
  | 27 => 8 | 28 => 10 | 29 => 3 | 30 => 3 | 31 => 3 | 32 => 9 | 33 => 4 | 34 => 4 | 35 => 4
  | 36 => 10 | 37 => 5 | 38 => 5 | 39 => 5 | 40 => 6 | 41 => 6 | 42 => 7 | 43 => 7 | 44 => 8
  | 45 => 0 | 46 => 0 | 47 => 3 | 48 => 0 | 49 => 8 | 50 => 9 | 51 => 5 | 52 => 6 | 53 => 9
  | 54 => 1 | 55 => 1 | 56 => 4 | 57 => 1 | 58 => 9 | 59 => 10 | 60 => 6 | 61 => 7 | 62 => 10
  | 63 => 2 | 64 => 2 | 65 => 5 | 66 => 2 | 67 => 10 | 68 => 7 | 69 => 8 | 70 => 3 | 71 => 6
  | 72 => 3 | 73 => 4 | 74 => 7 | 75 => 4 | 76 => 5 | 77 => 8 | 78 => 0 | 79 => 3 | 80 => 6
  | 81 => 9 | 82 => 1 | 83 => 4 | 84 => 7 | 85 => 10 | 86 => 2 | 87 => 5 | _ => 8

/-- Nonnegative integer multipliers for `k = 0` in the `ℤ/11`-equivariant certificate. -/
def Lval (a : Fin 89) : ℤ :=
  match a.1 with
  | 0 => 4121 | 1 => 3195 | 2 => 2874 | 3 => 2657 | 4 => 2550 | 5 => 2622 | 6 => 2693
  | 7 => 2693 | 8 => 2622 | 9 => 2550 | 10 => 2657 | 11 => 2874 | 12 => 1732 | 13 => 1921
  | 14 => 1791 | 15 => 1791 | 16 => 1921 | 17 => 1732 | 18 => 1322 | 19 => 1672 | 20 => 1470
  | 21 => 1399 | 22 => 1885 | 23 => 1660 | 24 => 1144 | 25 => 1494 | 26 => 1134 | 27 => 1078
  | 28 => 1885 | 29 => 1109 | 30 => 1405 | 31 => 957 | 32 => 1078 | 33 => 1181 | 34 => 1405
  | 35 => 1134 | 36 => 1399 | 37 => 1181 | 38 => 1405 | 39 => 1470 | 40 => 1109 | 41 => 1494
  | 42 => 1144 | 43 => 1672 | 44 => 1322 | 45 => 867 | 46 => 867 | 47 => 1117 | 48 => 918
  | 49 => 732 | 50 => 867 | 51 => 918 | 52 => 1117 | 53 => 867 | 54 => 761 | 55 => 867
  | 56 => 868 | 57 => 670 | 58 => 803 | 59 => 796 | 60 => 883 | 61 => 1081 | 62 => 796
  | 63 => 655 | 64 => 1081 | 65 => 619 | 66 => 421 | 67 => 883 | 68 => 803 | 69 => 867
  | 70 => 477 | 71 => 477 | 72 => 421 | 73 => 619 | 74 => 655 | 75 => 670 | 76 => 868
  | 77 => 761 | 78 => 71 | 79 => 107 | 80 => 107 | 81 => 71 | 82 => 107 | 83 => 179
  | 84 => 250 | 85 => 0 | 86 => 250 | 87 => 179 | _ => 107

def dir (d : Bool) : Fin 11 := if d then 1 else 10

def b2z (b : Bool) : ℤ := if b then 1 else 0

/-- Membership predicate for `V'_j = V_j ∪ Orb1(j) ∪ Orb2(j)`. -/
def inVp (j : Fin 11) (m : ℕ) : Bool :=
  hasBit m (j + 10) && hasBit m (j + 1) && (hasBit m (j + 4) || hasBit m (j + 7))

/-- Necessary condition for a vertex in `S_i` to be adjacent to a vertex in `V'_j`. -/
def canAdjVp (i j : Fin 11) (m : ℕ) : Bool :=
  hasBit m i && !hasBit m (j + 10) && !hasBit m (j + 1) && !(hasBit m (j + 4) && hasBit m (j + 7))

def d1Pred (i : Fin 11) (d : Bool) (a : Fin 89) : Bool :=
  canAdjVp i (i + 2 * dir d) (maskOf a)

def diffPred (i : Fin 11) (d : Bool) (a : Fin 89) : Bool :=
  canAdjVp i (i + 5 * dir d) (maskOf a) && !canAdjVp i (i + 2 * dir d) (maskOf a)

def gCoeff (k : Fin 11) (a : Fin 89) : ℤ :=
  14 * b2z (hasBit (maskOf a) k) - 5

def mTerm (i : Fin 11) (d : Bool) (a b : Fin 89) : ℤ :=
  let u0a := 1 - 2 * b2z (hasBit (maskOf a) i)
  let u0b := 1 - 2 * b2z (hasBit (maskOf b) i)
  let d1a := b2z (d1Pred i d a)
  let d1b := b2z (d1Pred i d b)
  let v2a := u0a - 2 * b2z (inVp (i + 2 * dir d) (maskOf a)) + b2z (diffPred i d a)
  let v2b := u0b - 2 * b2z (inVp (i + 2 * dir d) (maskOf b)) + b2z (diffPred i d b)
  50 * (u0a * d1b + d1a * u0b) + 25 * v2a * v2b - 4

def mInt (a b : Fin 89) : ℤ :=
  ∑ i : Fin 11, (mTerm i true a b + mTerm i false a b)

def symLG (a b : Fin 89) : ℤ :=
  ∑ k : Fin 11, (Lval (invSh k a) * gCoeff k b + gCoeff k a * Lval (invSh k b))

def certMat (a b : Fin 89) : ℤ :=
  20 * mInt a b + symLG a b

/- Finite decidable checks on `Fin 89` and `Fin 2048`. -/

lemma Lval_nonneg (a : Fin 89) : 0 ≤ Lval a := by
  revert a; decide

lemma maskOf_idxOfMask_chunk (q : Fin 32) (r : Fin 64) :
    isIndepMask (64 * q.1 + r.1) = true →
      maskOf (idxOfMask (64 * q.1 + r.1)) = 64 * q.1 + r.1 := by
  fin_cases q <;> (revert r; decide)

lemma maskOf_idxOfMask (m : ℕ) (hm : m < 2048) :
    isIndepMask m = true → maskOf (idxOfMask m) = m := by
  have hdiv : 64 * (m / 64) + m % 64 = m := Nat.div_add_mod m 64
  have hq : m / 64 < 32 := by omega
  have hr : m % 64 < 64 := Nat.mod_lt m (by decide)
  intro h
  have hchk := maskOf_idxOfMask_chunk ⟨m / 64, hq⟩ ⟨m % 64, hr⟩ (by simpa [hdiv] using h)
  simpa [hdiv] using hchk

lemma invSh1_sh1 (a : Fin 89) : invSh1 (sh1 a) = a := by
  revert a; decide

lemma sh1_invSh1 (a : Fin 89) : sh1 (invSh1 a) = a := by
  revert a; decide

lemma sh1_iter_11 (a : Fin 89) : sh1^[11] a = a := by
  revert a; decide

lemma invSh1_iter_11 (a : Fin 89) : invSh1^[11] a = a := by
  revert a; decide

lemma hasBit_sh1 (a : Fin 89) (k : Fin 11) :
    hasBit (maskOf (sh1 a)) (k + 1) = hasBit (maskOf a) k := by
  revert a k; decide

lemma sh_orb (a : Fin 89) : sh (orbSh a) (rep (orbId a)) = a := by
  revert a; decide

lemma size_cert_true (a : Fin 89) :
    (∑ m : Fin 7, gCoeff (Fin.ofNat 11 m.1) a) ≤
    7 * (2 * (b2z (hasBit (maskOf a) 0) + b2z (inVp 2 (maskOf a)) + b2z (inVp 5 (maskOf a))) - 1) := by
  revert a; decide

lemma size_cert_false (a : Fin 89) :
    (∑ m : Fin 7, gCoeff (Fin.ofNat 11 m.1 * 10) a) ≤
    7 * (2 * (b2z (hasBit (maskOf a) 0) + b2z (inVp 9 (maskOf a)) + b2z (inVp 6 (maskOf a))) - 1) := by
  revert a; decide

lemma certMat_rep_0 (b : Fin 89) : certMat (rep 0) b ≤ 0 := by revert b; decide
lemma certMat_rep_1 (b : Fin 89) : certMat (rep 1) b ≤ 0 := by revert b; decide
lemma certMat_rep_2 (b : Fin 89) : certMat (rep 2) b ≤ 0 := by revert b; decide
lemma certMat_rep_3 (b : Fin 89) : certMat (rep 3) b ≤ 0 := by revert b; decide
lemma certMat_rep_4 (b : Fin 89) : certMat (rep 4) b ≤ 0 := by revert b; decide
lemma certMat_rep_5 (b : Fin 89) : certMat (rep 5) b ≤ 0 := by revert b; decide
lemma certMat_rep_6 (b : Fin 89) : certMat (rep 6) b ≤ 0 := by revert b; decide
lemma certMat_rep_7 (b : Fin 89) : certMat (rep 7) b ≤ 0 := by revert b; decide
lemma certMat_rep_8 (b : Fin 89) : certMat (rep 8) b ≤ 0 := by revert b; decide

lemma certMat_rep (r : Fin 9) (b : Fin 89) : certMat (rep r) b ≤ 0 := by
  fin_cases r
  · exact certMat_rep_0 b
  · exact certMat_rep_1 b
  · exact certMat_rep_2 b
  · exact certMat_rep_3 b
  · exact certMat_rep_4 b
  · exact certMat_rep_5 b
  · exact certMat_rep_6 b
  · exact certMat_rep_7 b
  · exact certMat_rep_8 b

/- `ℤ/11`-invariance of `certMat` and `size_cert`. -/

lemma fin11_ofNat_succ (n : ℕ) : Fin.ofNat 11 (n + 1) = Fin.ofNat 11 n + 1 := by
  apply Fin.ext
  change (n + 1) % 11 = (n % 11 + 1 % 11) % 11
  rw [Nat.add_mod]

lemma fin11_ofNat_self (s : Fin 11) : Fin.ofNat 11 s.1 = s := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt s.2

lemma hasBit_sh1_iter (n : ℕ) (a : Fin 89) (k : Fin 11) :
    hasBit (maskOf (sh1^[n] a)) (k + Fin.ofNat 11 n) = hasBit (maskOf a) k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', fin11_ofNat_succ, ← add_assoc, hasBit_sh1]
    exact ih k

lemma hasBit_sh (s : Fin 11) (a : Fin 89) (k : Fin 11) :
    hasBit (maskOf (sh s a)) (k + s) = hasBit (maskOf a) k := by
  have h := hasBit_sh1_iter s.1 a k
  rwa [fin11_ofNat_self] at h

lemma invSh1_iter_sh1_iter (m n : ℕ) (a : Fin 89) :
    invSh1^[m] (sh1^[n] a) =
      if n ≤ m then invSh1^[m - n] a else sh1^[n - m] a := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    cases m with
    | zero => simp
    | succ m =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply', invSh1_sh1, ih m]
      by_cases h : n ≤ m
      · have h' : n + 1 ≤ m + 1 := by omega
        simp [h, h', Nat.succ_sub_succ]
      · have h' : ¬ n + 1 ≤ m + 1 := by omega
        simp [h, h', Nat.succ_sub_succ]

lemma sh_iter_mod (n : ℕ) (a : Fin 89) : sh1^[n] a = sh1^[n % 11] a := by
  have hdiv : n = n % 11 + 11 * (n / 11) := (Nat.mod_add_div n 11).symm
  conv_lhs => rw [hdiv, Function.iterate_add_apply]
  suffices h : ∀ q (x : Fin 89), sh1^[11 * q] x = x by rw [h]
  intro q x
  induction q generalizing x with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, sh1_iter_11, ih]

lemma invSh_iter_mod (n : ℕ) (a : Fin 89) : invSh1^[n] a = invSh1^[n % 11] a := by
  have hdiv : n = n % 11 + 11 * (n / 11) := (Nat.mod_add_div n 11).symm
  conv_lhs => rw [hdiv, Function.iterate_add_apply]
  suffices h : ∀ q (x : Fin 89), invSh1^[11 * q] x = x by rw [h]
  intro q x
  induction q generalizing x with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, invSh1_iter_11, ih]

lemma sh_invSh_cancel (s : Fin 11) (a : Fin 89) : sh s (invSh s a) = a := by
  have h : ∀ n (x : Fin 89), sh1^[n] (invSh1^[n] x) = x := by
    intro n x
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply', sh1_invSh1, ih]
  exact h s.1 a

lemma invSh_add_sh (k s : Fin 11) (a : Fin 89) :
    invSh (k + s) (sh s a) = invSh k a := by
  unfold invSh sh
  have h1 : (k + s).1 = (k.1 + s.1) % 11 := rfl
  rw [h1, ← invSh_iter_mod (k.1 + s.1), invSh1_iter_sh1_iter]
  simp

lemma inVp_sh (s j : Fin 11) (a : Fin 89) :
    inVp (j + s) (maskOf (sh s a)) = inVp j (maskOf a) := by
  unfold inVp
  rw [add_right_comm j s 10, add_right_comm j s 1, add_right_comm j s 4, add_right_comm j s 7,
    hasBit_sh, hasBit_sh, hasBit_sh, hasBit_sh]

lemma canAdjVp_sh (s i j : Fin 11) (a : Fin 89) :
    canAdjVp (i + s) (j + s) (maskOf (sh s a)) = canAdjVp i j (maskOf a) := by
  unfold canAdjVp
  rw [add_right_comm j s 10, add_right_comm j s 1, add_right_comm j s 4, add_right_comm j s 7,
    hasBit_sh, hasBit_sh, hasBit_sh, hasBit_sh, hasBit_sh]

lemma d1Pred_sh (s i : Fin 11) (d : Bool) (a : Fin 89) :
    d1Pred (i + s) d (sh s a) = d1Pred i d a := by
  unfold d1Pred
  rw [add_right_comm i s (2 * dir d), canAdjVp_sh]

lemma diffPred_sh (s i : Fin 11) (d : Bool) (a : Fin 89) :
    diffPred (i + s) d (sh s a) = diffPred i d a := by
  unfold diffPred
  rw [add_right_comm i s (5 * dir d), add_right_comm i s (2 * dir d), canAdjVp_sh, canAdjVp_sh]

lemma gCoeff_sh (s k : Fin 11) (a : Fin 89) :
    gCoeff (k + s) (sh s a) = gCoeff k a := by
  unfold gCoeff
  rw [hasBit_sh]

lemma mTerm_sh (s i : Fin 11) (d : Bool) (a b : Fin 89) :
    mTerm (i + s) d (sh s a) (sh s b) = mTerm i d a b := by
  unfold mTerm
  rw [add_right_comm i s (2 * dir d)]
  simp only [hasBit_sh, d1Pred_sh, diffPred_sh, inVp_sh]

lemma mInt_sh (s : Fin 11) (a b : Fin 89) :
    mInt (sh s a) (sh s b) = mInt a b := by
  unfold mInt
  symm
  refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun i => ?_
  change mTerm i true a b + mTerm i false a b =
    mTerm (i + s) true (sh s a) (sh s b) + mTerm (i + s) false (sh s a) (sh s b)
  rw [mTerm_sh, mTerm_sh]

lemma symLG_sh (s : Fin 11) (a b : Fin 89) :
    symLG (sh s a) (sh s b) = symLG a b := by
  unfold symLG
  symm
  refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun k => ?_
  change Lval (invSh k a) * gCoeff k b + gCoeff k a * Lval (invSh k b) =
    Lval (invSh (k + s) (sh s a)) * gCoeff (k + s) (sh s b) +
      gCoeff (k + s) (sh s a) * Lval (invSh (k + s) (sh s b))
  rw [invSh_add_sh, invSh_add_sh, gCoeff_sh, gCoeff_sh]

lemma certMat_sh (s : Fin 11) (a b : Fin 89) :
    certMat (sh s a) (sh s b) = certMat a b := by
  unfold certMat
  rw [mInt_sh, symLG_sh]

lemma certMat_nonpos (a b : Fin 89) : certMat a b ≤ 0 := by
  have ha : sh (orbSh a) (rep (orbId a)) = a := sh_orb a
  have hb : sh (orbSh a) (invSh (orbSh a) b) = b := sh_invSh_cancel (orbSh a) b
  rw [← ha, ← hb, certMat_sh]
  exact certMat_rep (orbId a) (invSh (orbSh a) b)

lemma size_cert_all (i : Fin 11) (d : Bool) (a : Fin 89) :
    (∑ m : Fin 7, gCoeff (i + Fin.ofNat 11 m.1 * dir d) a) ≤
    7 * (2 * (b2z (hasBit (maskOf a) i) +
      b2z (inVp (i + 2 * dir d) (maskOf a)) +
      b2z (inVp (i + 5 * dir d) (maskOf a))) - 1) := by
  set a0 := invSh i a
  have ha : sh i a0 = a := sh_invSh_cancel i a
  rw [← ha]
  have hsum : (∑ m : Fin 7, gCoeff (i + Fin.ofNat 11 m.1 * dir d) (sh i a0)) =
      ∑ m : Fin 7, gCoeff (Fin.ofNat 11 m.1 * dir d) a0 := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [add_comm i, gCoeff_sh]
  rw [hsum]
  have hb0 : hasBit (maskOf (sh i a0)) i = hasBit (maskOf a0) 0 := by
    simpa using hasBit_sh i a0 0
  have hb1 : inVp (i + 2 * dir d) (maskOf (sh i a0)) = inVp (2 * dir d) (maskOf a0) := by
    rw [add_comm i, inVp_sh]
  have hb2 : inVp (i + 5 * dir d) (maskOf (sh i a0)) = inVp (5 * dir d) (maskOf a0) := by
    rw [add_comm i, inVp_sh]
  rw [hb0, hb1, hb2]
  cases d
  · simpa [dir] using size_cert_false a0
  · simpa [dir] using size_cert_true a0

/- Binary mask decoding on `Fin 11`. -/

lemma pow2_eq (k : Fin 11) : pow2 k = 2 ^ k.1 := by
  fin_cases k <;> rfl

lemma sum_pow2_lt (f : Fin 11 → Bool) :
    (∑ k : Fin 11, if f k then pow2 k else 0) < 2048 := by
  have hle : (∑ k : Fin 11, if f k then pow2 k else 0) ≤ ∑ k : Fin 11, pow2 k := by
    refine Finset.sum_le_sum fun k _ => ?_
    cases f k <;> simp
  have hsum : (∑ k : Fin 11, pow2 k) = 2047 := by decide
  omega

lemma sum_pow2_lo_lt (k : Fin 11) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin 11 => j.1 < k.1), pow2 j) < pow2 k := by
  revert k; decide

lemma hasBit_sum_pow2 (f : Fin 11 → Bool) (k : Fin 11) :
    hasBit (∑ j : Fin 11, if f j then pow2 j else 0) k = f k := by
  let g : Fin 11 → ℕ := fun j => if f j then pow2 j else 0
  let lo : Finset (Fin 11) := Finset.univ.filter fun j => j.1 < k.1
  let hi : Finset (Fin 11) := Finset.univ.filter fun j => k.1 < j.1
  have hsplit : (∑ j : Fin 11, g j) = (∑ j ∈ lo, g j) + g k + ∑ j ∈ hi, g j := by
    have h1 : (Finset.univ : Finset (Fin 11)) = lo ∪ ({k} ∪ hi) := by
      ext j; simp only [lo, hi, Finset.mem_univ, Finset.mem_union, Finset.mem_filter,
        Finset.mem_singleton, true_and, true_iff]
      rcases lt_trichotomy j.1 k.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr h)
    have hd1 : Disjoint lo ({k} ∪ hi) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [lo, hi, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_univ, true_and] at hj1 hj2
      rcases hj2 with rfl | hj2 <;> omega
    have hd2 : Disjoint ({k} : Finset (Fin 11)) hi := by
      rw [Finset.disjoint_singleton_left]
      simp [hi]
    rw [h1, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton, add_assoc]
  have hlo : ∑ j ∈ lo, g j < pow2 k := by
    have hle : ∑ j ∈ lo, g j ≤ ∑ j ∈ lo, pow2 j :=
      Finset.sum_le_sum fun j _ => by dsimp [g]; cases f j <;> simp
    exact lt_of_le_of_lt hle (sum_pow2_lo_lt k)
  have hhi : 2 * pow2 k ∣ ∑ j ∈ hi, g j := by
    refine Finset.dvd_sum fun j hj => ?_
    simp only [hi, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    dsimp [g]
    cases f j
    · simp
    · rw [if_pos rfl, pow2_eq, pow2_eq]
      have hpow : 2 ^ (k.1 + 1) ∣ 2 ^ j.1 := Nat.pow_dvd_pow 2 (by omega)
      simpa [pow_succ, mul_comm] using hpow
  obtain ⟨q, hq⟩ := hhi
  have hpos : 0 < pow2 k := by rw [pow2_eq]; positivity
  rw [show (∑ j : Fin 11, if f j then pow2 j else 0) = (∑ j ∈ lo, g j) + g k + 2 * pow2 k * q from by
    rw [← hq]; exact hsplit]
  unfold hasBit
  have hdiv : ((∑ j ∈ lo, g j) + g k + 2 * pow2 k * q) / pow2 k =
      (if f k then 1 else 0) + 2 * q := by
    have h1 : (∑ j ∈ lo, g j) + g k + 2 * pow2 k * q =
        (∑ j ∈ lo, g j) + ((if f k then 1 else 0) + 2 * q) * pow2 k := by
      dsimp [g]; cases f k <;> simp <;> ring
    rw [h1, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlo, zero_add]
  rw [hdiv]
  cases f k <;> simp

/- Elementary bipartite edge count bound. -/

lemma induce_edgeSet_ncard_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A T1 T2 D1 D2 : Finset V)
    (hA_ind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (hT_ind : ∀ u ∈ T1 ∪ T2, ∀ v ∈ T1 ∪ T2, ¬ G.Adj u v)
    (hD1 : ∀ u ∈ A, ∀ v ∈ T1, G.Adj u v → u ∈ D1)
    (hD2 : ∀ u ∈ A, ∀ v ∈ T2, G.Adj u v → u ∈ D2) :
    (G.induce ((A ∪ T1 ∪ T2 : Finset V) : Set V)).edgeSet.ncard ≤
      T1.card * D1.card + T2.card * D2.card := by
  classical
  let W : Finset V := A ∪ T1 ∪ T2
  let emb : Sym2 W ↪ Sym2 V :=
    ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩
  let Eset : Finset (Sym2 W) := (G.induce (W : Set V)).edgeFinset
  have hncard : (G.induce (W : Set V)).edgeSet.ncard = Eset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hncard]
  let img : Finset (Sym2 V) := Eset.map emb
  have hcard_eq : Eset.card = img.card := (Finset.card_map emb).symm
  rw [hcard_eq]
  let B1 : Finset (Sym2 V) := (T1 ×ˢ D1).image fun p => s(p.1, p.2)
  let B2 : Finset (Sym2 V) := (T2 ×ˢ D2).image fun p => s(p.1, p.2)
  have hsub : img ⊆ B1 ∪ B2 := by
    intro e he
    rcases Finset.mem_map.mp he with ⟨e', he', rfl⟩
    rw [SimpleGraph.mem_edgeFinset] at he'
    induction e' using Sym2.ind with
    | _ x y =>
      have hadj : G.Adj x.1 y.1 := he'
      have hxW : x.1 ∈ W := x.2
      have hyW : y.1 ∈ W := y.2
      have hmem : ∀ z ∈ W, z ∈ A ∨ z ∈ T1 ∪ T2 := by
        intro z hz
        simp only [W, Finset.mem_union] at hz ⊢
        tauto
      have hsym : emb s(x, y) = s(x.1, y.1) := rfl
      rw [hsym]
      rcases hmem x.1 hxW with hxA | hxT <;> rcases hmem y.1 hyW with hyA | hyT
      · exact False.elim (hA_ind x.1 hxA y.1 hyA hadj)
      · rcases Finset.mem_union.mp hyT with hy1 | hy2
        · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(y.1, x.1), ?_, Sym2.eq_swap⟩)
          exact Finset.mem_product.mpr ⟨hy1, hD1 x.1 hxA y.1 hy1 hadj⟩
        · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(y.1, x.1), ?_, Sym2.eq_swap⟩)
          exact Finset.mem_product.mpr ⟨hy2, hD2 x.1 hxA y.1 hy2 hadj⟩
      · rcases Finset.mem_union.mp hxT with hx1 | hx2
        · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(x.1, y.1), ?_, rfl⟩)
          exact Finset.mem_product.mpr ⟨hx1, hD1 y.1 hyA x.1 hx1 hadj.symm⟩
        · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x.1, y.1), ?_, rfl⟩)
          exact Finset.mem_product.mpr ⟨hx2, hD2 y.1 hyA x.1 hx2 hadj.symm⟩
      · exact False.elim (hT_ind x.1 hxT y.1 hyT hadj)
  calc
    img.card ≤ (B1 ∪ B2).card := Finset.card_le_card hsub
    _ ≤ B1.card + B2.card := Finset.card_union_le B1 B2
    _ ≤ (T1 ×ˢ D1).card + (T2 ×ˢ D2).card := add_le_add Finset.card_image_le Finset.card_image_le
    _ = T1.card * D1.card + T2.card * D2.card := by rw [Finset.card_product, Finset.card_product]

/- Arithmetic helpers on `Fin 11`. -/

lemma fin11_j1_add1_false (i : Fin 11) : i + 2 * dir false + 1 = i + 10 := by
  fin_cases i <;> decide
lemma fin11_j1_add10_true (i : Fin 11) : i + 2 * dir true + 10 = i + 1 := by
  fin_cases i <;> decide
lemma fin11_j2_add1_false (i : Fin 11) : i + 5 * dir false + 1 = i + 7 := by
  fin_cases i <;> decide
lemma fin11_j2_add10_true (i : Fin 11) : i + 5 * dir true + 10 = i + 4 := by
  fin_cases i <;> decide
lemma fin11_j1_add10_false (i : Fin 11) : i + 2 * dir false + 10 = i + 8 := by
  fin_cases i <;> decide
lemma fin11_j1_add1_true (i : Fin 11) : i + 2 * dir true + 1 = i + 3 := by
  fin_cases i <;> decide
lemma fin11_j2_add10_false (i : Fin 11) : i + 5 * dir false + 10 = i + 5 := by
  fin_cases i <;> decide
lemma fin11_j2_add4_false (i : Fin 11) : i + 5 * dir false + 4 = i + 10 := by
  fin_cases i <;> decide
lemma fin11_j1_add4_false (i : Fin 11) : i + 2 * dir false + 4 = i + 2 := by
  fin_cases i <;> decide
lemma fin11_j2_add7_false (i : Fin 11) : i + 5 * dir false + 7 = i + 2 := by
  fin_cases i <;> decide
lemma fin11_j1_add7_false (i : Fin 11) : i + 2 * dir false + 7 = i + 5 := by
  fin_cases i <;> decide
lemma fin11_j2_add1_true (i : Fin 11) : i + 5 * dir true + 1 = i + 6 := by
  fin_cases i <;> decide
lemma fin11_j1_add4_true (i : Fin 11) : i + 2 * dir true + 4 = i + 6 := by
  fin_cases i <;> decide
lemma fin11_j1_add7_true (i : Fin 11) : i + 2 * dir true + 7 = i + 9 := by
  fin_cases i <;> decide
lemma fin11_j2_add4_true (i : Fin 11) : i + 5 * dir true + 4 = i + 9 := by
  fin_cases i <;> decide
lemma fin11_j2_add7_true (i : Fin 11) : i + 5 * dir true + 7 = i + 1 := by
  fin_cases i <;> decide
lemma fin11_add7_add1 (i : Fin 11) : i + 8 = (i + 7) + 1 := by
  fin_cases i <;> decide
lemma fin11_add3_add1 (i : Fin 11) : i + 4 = (i + 3) + 1 := by
  fin_cases i <;> decide

/- Graph classification and helper lemmas for the Band `And(4)` subcase. -/

lemma no_tri_of_cliqueFree3 {V : Type} {G : SimpleGraph V} (hTF : G.CliqueFree 3)
    {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w) : False := by
  classical
  have hcl : G.IsNClique 3 ({u, v, w} : Finset V) := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact (hab rfl).elim
      · exact huv
      · exact huw
      · exact huv.symm
      · exact (hab rfl).elim
      · exact hvw
      · exact huw.symm
      · exact hvw.symm
      · exact (hab rfl).elim
    · have hne1 : u ≠ v := G.ne_of_adj huv
      have hne2 : u ≠ w := G.ne_of_adj huw
      have hne3 : v ≠ w := G.ne_of_adj hvw
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hne3]
      · simp [hne1, hne2]
  exact hTF {u, v, w} hcl

lemma card_filter_vType {V : Type} [Fintype V] [DecidableEq V] (vType : V → Fin 89)
    (P : Fin 89 → Bool) :
    ((Finset.univ.filter fun v : V => P (vType v) = true).card : ℤ) =
    ∑ a : Fin 89, b2z (P a) * ((Finset.univ.filter fun v : V => vType v = a).card : ℤ) := by
  have h1 : (Finset.univ.filter fun v : V => P (vType v) = true).card =
      ∑ a : Fin 89, ((Finset.univ.filter fun v : V => vType v = a).filter fun v => P (vType v) = true).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      exact ⟨fun h => ⟨vType v, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
    · intro a _ b _ hab
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
      exact hab (hv1.1.symm.trans hv2.1)
  rw [h1, Nat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases hPa : P a
  · have hemp : ((Finset.univ.filter fun v : V => vType v = a).filter fun v => P (vType v) = true) = ∅ := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨rfl, h⟩; rw [hPa] at h; exact Bool.false_ne_true h
    rw [hemp]; simp [b2z]
  · have hfull : ((Finset.univ.filter fun v : V => vType v = a).filter fun v => P (vType v) = true) =
        (Finset.univ.filter fun v : V => vType v = a) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
      rintro rfl; exact hPa
    rw [hfull]; simp [b2z]

lemma pair_quad_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (h50 : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (φ : Fin 11 → V)
    (hφ : ∀ i j : Fin 11, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7 ∨ j = i + 10) → G.Adj (φ i) (φ j))
    (vType : V → Fin 89)
    (hadj_iff : ∀ (v : V) (k : Fin 11), G.Adj (φ k) v ↔ hasBit (maskOf (vType v)) k = true)
    (hg_nonneg : ∀ k : Fin 11,
      0 ≤ ∑ a : Fin 89, gCoeff k a * ((Finset.univ.filter fun v : V => vType v = a).card : ℤ))
    (i : Fin 11) (d : Bool) :
    let n := Fintype.card V
    let S := Finset.univ.filter fun v : V => hasBit (maskOf (vType v)) i = true
    let Vp1 := Finset.univ.filter fun v : V => inVp (i + 2 * dir d) (maskOf (vType v)) = true
    let D1 := Finset.univ.filter fun v : V => d1Pred i d (vType v) = true
    let DIFF := Finset.univ.filter fun v : V => diffPred i d (vType v) = true
    4 * (n : ℤ) ^ 2 <
      100 * ((n : ℤ) - 2 * (S.card : ℤ)) * (D1.card : ℤ) +
      25 * ((n : ℤ) - 2 * (S.card : ℤ) - 2 * (Vp1.card : ℤ) + (DIFF.card : ℤ)) ^ 2 := by
  classical
  dsimp only
  set n : ℕ := Fintype.card V
  set j1 : Fin 11 := i + 2 * dir d
  set j2 : Fin 11 := i + 5 * dir d
  set S : Finset V := Finset.univ.filter fun v => hasBit (maskOf (vType v)) i = true
  set Vp1 : Finset V := Finset.univ.filter fun v => inVp j1 (maskOf (vType v)) = true
  set Vp2 : Finset V := Finset.univ.filter fun v => inVp j2 (maskOf (vType v)) = true
  set D1 : Finset V := Finset.univ.filter fun v => d1Pred i d (vType v) = true
  set DIFF : Finset V := Finset.univ.filter fun v => diffPred i d (vType v) = true
  set D2 : Finset V := Finset.univ.filter fun v => canAdjVp i j2 (maskOf (vType v)) = true
  let x : Fin 89 → ℤ := fun a => ((Finset.univ.filter fun v : V => vType v = a).card : ℤ)
  have hx_nonneg : ∀ a : Fin 89, 0 ≤ x a := fun a => Nat.cast_nonneg _
  have hn_sum : (n : ℤ) = ∑ a : Fin 89, x a := by
    simpa [n, b2z, x] using card_filter_vType vType (fun _ => true)
  -- `S` is independent and has `2 * |S| + 1 < n`.
  have hS_ind : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact no_tri_of_cliqueFree3 hTF ((hadj_iff u i).mpr hu) huv ((hadj_iff v i).mpr hv)
  have hS_small : 2 * S.card + 1 < n := by
    by_contra! hge
    have h50i := h50 (S : Set V) (by rw [Set.ncard_coe_finset]; exact hge)
    have hzero : (G.induce (S : Set V)).edgeSet.ncard = 0 := by
      have hemp : (G.induce (S : Set V)).edgeSet = ∅ := by
        ext e
        simp only [Set.mem_empty_iff_false, iff_false]
        induction e using Sym2.ind with
        | _ a b => intro h; exact hS_ind a.1 a.2 b.1 b.2 h
      rw [hemp, Set.ncard_empty]
    rw [hzero] at h50i
    nlinarith
  -- Disjointness of `S`, `Vp1`, `Vp2`.
  have h_disj_S_j1 : Disjoint S Vp1 := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [S, Vp1, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hv1 hv2
    have hvi : G.Adj (φ i) v := (hadj_iff v i).mpr hv1
    cases d
    · have hvj : G.Adj (φ (i + 10)) v := by
        rw [← fin11_j1_add1_false i]; exact (hadj_iff v _).mpr hv2.1.2
      exact no_tri_of_cliqueFree3 hTF (hφ i (i + 10) (by simp)) hvj hvi
    · have hvj : G.Adj (φ (i + 1)) v := by
        rw [← fin11_j1_add10_true i]; exact (hadj_iff v _).mpr hv2.1.1
      exact no_tri_of_cliqueFree3 hTF (hφ i (i + 1) (by simp)) hvj hvi
  have h_disj_S_j2 : Disjoint S Vp2 := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [S, Vp2, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hv1 hv2
    have hvi : G.Adj (φ i) v := (hadj_iff v i).mpr hv1
    cases d
    · have hvj : G.Adj (φ (i + 7)) v := by
        rw [← fin11_j2_add1_false i]; exact (hadj_iff v _).mpr hv2.1.2
      exact no_tri_of_cliqueFree3 hTF (hφ i (i + 7) (by simp)) hvj hvi
    · have hvj : G.Adj (φ (i + 4)) v := by
        rw [← fin11_j2_add10_true i]; exact (hadj_iff v _).mpr hv2.1.1
      exact no_tri_of_cliqueFree3 hTF (hφ i (i + 4) (by simp)) hvj hvi
  have h_disj_j1_j2 : Disjoint Vp1 Vp2 := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Vp1, Vp2, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hv1 hv2
    cases d
    · have h1 : G.Adj (φ (i + 8)) v := by
        rw [← fin11_j1_add10_false i]; exact (hadj_iff v _).mpr hv1.1.1
      have h2 : G.Adj (φ (i + 7)) v := by
        rw [← fin11_j2_add1_false i]; exact (hadj_iff v _).mpr hv2.1.2
      have hphi : G.Adj (φ (i + 7)) (φ (i + 8)) := hφ (i + 7) (i + 8) (Or.inl (fin11_add7_add1 i))
      exact no_tri_of_cliqueFree3 hTF hphi h1 h2
    · have h1 : G.Adj (φ (i + 3)) v := by
        rw [← fin11_j1_add1_true i]; exact (hadj_iff v _).mpr hv1.1.2
      have h2 : G.Adj (φ (i + 4)) v := by
        rw [← fin11_j2_add10_true i]; exact (hadj_iff v _).mpr hv2.1.1
      have hphi : G.Adj (φ (i + 3)) (φ (i + 4)) := hφ (i + 3) (i + 4) (Or.inl (fin11_add3_add1 i))
      exact no_tri_of_cliqueFree3 hTF hphi h2 h1
  -- Independence of `Vp1 ∪ Vp2`.
  have hVp_ind : ∀ u ∈ Vp1 ∪ Vp2, ∀ v ∈ Vp1 ∪ Vp2, ¬ G.Adj u v := by
    have hcomm : ∀ u ∈ Vp1, ∀ v ∈ Vp2, ∃ k : Fin 11, G.Adj (φ k) u ∧ G.Adj (φ k) v := by
      intro u hu v hv
      simp only [Vp1, Vp2, Finset.mem_filter, Finset.mem_univ, true_and, inVp,
        Bool.and_eq_true, Bool.or_eq_true] at hu hv
      cases d
      · have hu10 : G.Adj (φ (i + 10)) u := by
          rw [← fin11_j1_add1_false i]; exact (hadj_iff u _).mpr hu.1.2
        have hv5 : G.Adj (φ (i + 5)) v := by
          rw [← fin11_j2_add10_false i]; exact (hadj_iff v _).mpr hv.1.1
        rcases hv.2 with hv10 | hv2
        · refine ⟨i + 10, hu10, ?_⟩
          rw [← fin11_j2_add4_false i]; exact (hadj_iff v _).mpr hv10
        · rcases hu.2 with hu2 | hu5
          · refine ⟨i + 2, ?_, ?_⟩
            · rw [← fin11_j1_add4_false i]; exact (hadj_iff u _).mpr hu2
            · rw [← fin11_j2_add7_false i]; exact (hadj_iff v _).mpr hv2
          · refine ⟨i + 5, ?_, hv5⟩
            rw [← fin11_j1_add7_false i]; exact (hadj_iff u _).mpr hu5
      · have hu1 : G.Adj (φ (i + 1)) u := by
          rw [← fin11_j1_add10_true i]; exact (hadj_iff u _).mpr hu.1.1
        have hv6 : G.Adj (φ (i + 6)) v := by
          rw [← fin11_j2_add1_true i]; exact (hadj_iff v _).mpr hv.1.2
        rcases hv.2 with hv9 | hv1
        · rcases hu.2 with hu6 | hu9
          · refine ⟨i + 6, ?_, hv6⟩
            rw [← fin11_j1_add4_true i]; exact (hadj_iff u _).mpr hu6
          · refine ⟨i + 9, ?_, ?_⟩
            · rw [← fin11_j1_add7_true i]; exact (hadj_iff u _).mpr hu9
            · rw [← fin11_j2_add4_true i]; exact (hadj_iff v _).mpr hv9
        · refine ⟨i + 1, hu1, ?_⟩
          rw [← fin11_j2_add7_true i]; exact (hadj_iff v _).mpr hv1
    intro u hu v hv huv
    rcases Finset.mem_union.mp hu with hu1 | hu2 <;> rcases Finset.mem_union.mp hv with hv1 | hv2
    · simp only [Vp1, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hu1 hv1
      exact no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr hu1.1.2) huv ((hadj_iff v _).mpr hv1.1.2)
    · obtain ⟨k, hku, hkv⟩ := hcomm u hu1 v hv2
      exact no_tri_of_cliqueFree3 hTF hku huv hkv
    · obtain ⟨k, hkv, hku⟩ := hcomm v hv1 u hu2
      exact no_tri_of_cliqueFree3 hTF hku huv hkv
    · simp only [Vp2, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hu2 hv2
      exact no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr hu2.1.2) huv ((hadj_iff v _).mpr hv2.1.2)
  -- Size bound `n ≤ 2 * (|S| + |Vp1| + |Vp2|)`.
  have hsize : n ≤ 2 * (S.card + Vp1.card + Vp2.card) := by
    have hsum_cert :
        (∑ m : Fin 7, ∑ a : Fin 89, gCoeff (i + Fin.ofNat 11 m.1 * dir d) a * x a) ≤
        ∑ a : Fin 89, 7 * (2 * (b2z (hasBit (maskOf a) i) +
          b2z (inVp j1 (maskOf a)) + b2z (inVp j2 (maskOf a))) - 1) * x a := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (size_cert_all i d a) (hx_nonneg a)
    have hlhs : 0 ≤ ∑ m : Fin 7, ∑ a : Fin 89, gCoeff (i + Fin.ofNat 11 m.1 * dir d) a * x a :=
      Finset.sum_nonneg fun m _ => hg_nonneg _
    have hrhs : (∑ a : Fin 89, 7 * (2 * (b2z (hasBit (maskOf a) i) +
          b2z (inVp j1 (maskOf a)) + b2z (inVp j2 (maskOf a))) - 1) * x a) =
        7 * (2 * ((S.card : ℤ) + (Vp1.card : ℤ) + (Vp2.card : ℤ)) - (n : ℤ)) := by
      have hS := card_filter_vType vType (fun a => hasBit (maskOf a) i)
      have hV1 := card_filter_vType vType (fun a => inVp j1 (maskOf a))
      have hV2 := card_filter_vType vType (fun a => inVp j2 (maskOf a))
      have hlin : ∀ a : Fin 89,
          7 * (2 * (b2z (hasBit (maskOf a) i) + b2z (inVp j1 (maskOf a)) +
            b2z (inVp j2 (maskOf a))) - 1) * x a =
          14 * (b2z (hasBit (maskOf a) i) * x a) +
          14 * (b2z (inVp j1 (maskOf a)) * x a) +
          14 * (b2z (inVp j2 (maskOf a)) * x a) - 7 * x a := fun a => by ring
      simp_rw [hlin, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      change 14 * (∑ a : Fin 89, b2z (hasBit (maskOf a) i) * x a) +
        14 * (∑ a : Fin 89, b2z (inVp j1 (maskOf a)) * x a) +
        14 * (∑ a : Fin 89, b2z (inVp j2 (maskOf a)) * x a) - 7 * (∑ a : Fin 89, x a) = _
      rw [← hS, ← hV1, ← hV2, ← hn_sum]
      ring
    have hge := hlhs.trans (hsum_cert.trans_eq hrhs)
    omega
  -- Adjacency containment in `D1` and `D2`.
  have hadj_vp : ∀ (j : Fin 11) (u : V), u ∈ S →
      ∀ v : V, inVp j (maskOf (vType v)) = true → G.Adj u v →
        canAdjVp i j (maskOf (vType u)) = true := by
    intro j u hu v hv huv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [inVp, Bool.and_eq_true, Bool.or_eq_true] at hv
    unfold canAdjVp
    have hn10 : hasBit (maskOf (vType u)) (j + 10) = false := by
      cases h : hasBit (maskOf (vType u)) (j + 10)
      · rfl
      · exact False.elim (no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr h) huv ((hadj_iff v _).mpr hv.1.1))
    have hn1 : hasBit (maskOf (vType u)) (j + 1) = false := by
      cases h : hasBit (maskOf (vType u)) (j + 1)
      · rfl
      · exact False.elim (no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr h) huv ((hadj_iff v _).mpr hv.1.2))
    have hn47 : (hasBit (maskOf (vType u)) (j + 4) && hasBit (maskOf (vType u)) (j + 7)) = false := by
      cases h4 : hasBit (maskOf (vType u)) (j + 4)
      · simp
      · cases h7 : hasBit (maskOf (vType u)) (j + 7)
        · simp
        · rcases hv.2 with hv4 | hv7
          · exact False.elim (no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr h4) huv ((hadj_iff v _).mpr hv4))
          · exact False.elim (no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr h7) huv ((hadj_iff v _).mpr hv7))
    simp [hu, hn10, hn1, hn47]
  -- Pick subsets `T1 ⊆ Vp1` and `T2 ⊆ Vp2` of total size `t = n / 2 - |S|`.
  let t : ℕ := n / 2 - S.card
  let r1 : ℕ := min t Vp1.card
  let r2 : ℕ := t - r1
  have hr1_le : r1 ≤ Vp1.card := min_le_right _ _
  have hr2_le : r2 ≤ Vp2.card := by omega
  obtain ⟨T1, hT1_sub, hT1_card⟩ := Finset.exists_subset_card_eq hr1_le
  obtain ⟨T2, hT2_sub, hT2_card⟩ := Finset.exists_subset_card_eq hr2_le
  have hdisj_ST1 : Disjoint S T1 := Disjoint.mono_right hT1_sub h_disj_S_j1
  have hdisj_ST2 : Disjoint S T2 := Disjoint.mono_right hT2_sub h_disj_S_j2
  have hdisj_T12 : Disjoint T1 T2 := Disjoint.mono hT1_sub hT2_sub h_disj_j1_j2
  have hW_card : (S ∪ T1 ∪ T2).card = n / 2 := by
    have hdisj_ST1_T2 : Disjoint (S ∪ T1) T2 := Finset.disjoint_union_left.mpr ⟨hdisj_ST2, hdisj_T12⟩
    rw [Finset.card_union_of_disjoint hdisj_ST1_T2, Finset.card_union_of_disjoint hdisj_ST1,
      hT1_card, hT2_card]
    omega
  have hW_half : 2 * ((S ∪ T1 ∪ T2 : Finset V) : Set V).ncard + 1 ≥ n := by
    rw [Set.ncard_coe_finset, hW_card]; omega
  have h50W := h50 ((S ∪ T1 ∪ T2 : Finset V) : Set V) hW_half
  have hedge : (G.induce ((S ∪ T1 ∪ T2 : Finset V) : Set V)).edgeSet.ncard ≤
      T1.card * D1.card + T2.card * D2.card := by
    refine induce_edgeSet_ncard_le G S T1 T2 D1 D2 hS_ind ?_ ?_ ?_
    · intro u hu v hv
      exact hVp_ind u (Finset.union_subset_union hT1_sub hT2_sub hu)
        v (Finset.union_subset_union hT1_sub hT2_sub hv)
    · intro u hu v hv huv
      have hv1 := (Finset.mem_filter.mp (hT1_sub hv)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hadj_vp j1 u hu v hv1 huv⟩
    · intro u hu v hv huv
      have hv2 := (Finset.mem_filter.mp (hT2_sub hv)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hadj_vp j2 u hu v hv2 huv⟩
  have hD2_le : D2.card ≤ D1.card + DIFF.card := by
    have hsub : D2 ⊆ D1 ∪ DIFF := by
      intro v hv
      have hv2 : canAdjVp i j2 (maskOf (vType v)) = true := (Finset.mem_filter.mp hv).2
      cases h1 : canAdjVp i j1 (maskOf (vType v))
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩)
        dsimp only [diffPred]
        rw [show i + 5 * dir d = j2 from rfl, show i + 2 * dir d = j1 from rfl, hv2, h1]
        rfl
      · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩)
        exact h1
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hgt : n ^ 2 < 50 * (t * D1.card + r2 * DIFF.card) := by
    have hr : r1 + r2 = t := by omega
    have h1 : T1.card * D1.card + T2.card * D2.card ≤ t * D1.card + r2 * DIFF.card := by
      rw [hT1_card, hT2_card]
      calc
        r1 * D1.card + r2 * D2.card
            ≤ r1 * D1.card + r2 * (D1.card + DIFF.card) :=
              Nat.add_le_add_left (Nat.mul_le_mul_left r2 hD2_le) _
        _ = (r1 + r2) * D1.card + r2 * DIFF.card := by ring
        _ = t * D1.card + r2 * DIFF.card := by rw [hr]
    omega
  have hgtZ : (n : ℤ) ^ 2 < 50 * ((t : ℤ) * (D1.card : ℤ) + (r2 : ℤ) * (DIFF.card : ℤ)) := by
    exact_mod_cast hgt
  have htZ : 2 * (t : ℤ) ≤ (n : ℤ) - 2 * (S.card : ℤ) := by omega
  have hr2_bound : 8 * (r2 : ℤ) * (DIFF.card : ℤ) ≤
      ((n : ℤ) - 2 * (S.card : ℤ) - 2 * (Vp1.card : ℤ) + (DIFF.card : ℤ)) ^ 2 := by
    set U : ℤ := (n : ℤ) - 2 * (S.card : ℤ) - 2 * (Vp1.card : ℤ)
    set Y : ℤ := (DIFF.card : ℤ)
    have hY : 0 ≤ Y := Nat.cast_nonneg _
    have hr2_0 : 0 ≤ (r2 : ℤ) := Nat.cast_nonneg _
    by_cases hcase : t ≤ Vp1.card
    · have hr2_zero : (r2 : ℤ) = 0 := by omega
      rw [hr2_zero]; nlinarith
    · have h2r2 : 2 * (r2 : ℤ) ≤ U := by omega
      nlinarith [sq_nonneg (U - Y)]
  have hD1_nonneg : (0 : ℤ) ≤ (D1.card : ℤ) := Nat.cast_nonneg _
  have h100 : 200 * (t : ℤ) * (D1.card : ℤ) ≤ 100 * ((n : ℤ) - 2 * (S.card : ℤ)) * (D1.card : ℤ) := by
    nlinarith
  linarith

lemma mTerm_sum_identity {V : Type} [Fintype V] [DecidableEq V] (vType : V → Fin 89)
    (i : Fin 11) (d : Bool) :
    let n := Fintype.card V
    let x : Fin 89 → ℤ := fun a => ((Finset.univ.filter fun v : V => vType v = a).card : ℤ)
    let S := Finset.univ.filter fun v : V => hasBit (maskOf (vType v)) i = true
    let Vp1 := Finset.univ.filter fun v : V => inVp (i + 2 * dir d) (maskOf (vType v)) = true
    let D1 := Finset.univ.filter fun v : V => d1Pred i d (vType v) = true
    let DIFF := Finset.univ.filter fun v : V => diffPred i d (vType v) = true
    100 * ((n : ℤ) - 2 * (S.card : ℤ)) * (D1.card : ℤ) +
    25 * ((n : ℤ) - 2 * (S.card : ℤ) - 2 * (Vp1.card : ℤ) + (DIFF.card : ℤ)) ^ 2 - 4 * (n : ℤ) ^ 2 =
    ∑ a : Fin 89, ∑ b : Fin 89, mTerm i d a b * x a * x b := by
  dsimp only
  set n : ℕ := Fintype.card V
  let x : Fin 89 → ℤ := fun a => ((Finset.univ.filter fun v : V => vType v = a).card : ℤ)
  have hn_sum : (n : ℤ) = ∑ a : Fin 89, x a := by
    simpa [n, b2z, x] using card_filter_vType vType (fun _ => true)
  let u0 : Fin 89 → ℤ := fun a => 1 - 2 * b2z (hasBit (maskOf a) i)
  let d1 : Fin 89 → ℤ := fun a => b2z (d1Pred i d a)
  let v2 : Fin 89 → ℤ := fun a => u0 a - 2 * b2z (inVp (i + 2 * dir d) (maskOf a)) + b2z (diffPred i d a)
  have hU0 : (n : ℤ) - 2 * ((Finset.univ.filter fun v : V => hasBit (maskOf (vType v)) i = true).card : ℤ) =
      ∑ a : Fin 89, u0 a * x a := by
    have hS := card_filter_vType vType (fun a => hasBit (maskOf a) i)
    rw [hn_sum, hS]
    simp only [u0, sub_mul, one_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, x]
  have hD1 : ((Finset.univ.filter fun v : V => d1Pred i d (vType v) = true).card : ℤ) =
      ∑ a : Fin 89, d1 a * x a := card_filter_vType vType (d1Pred i d)
  have hV2 : (n : ℤ) - 2 * ((Finset.univ.filter fun v : V => hasBit (maskOf (vType v)) i = true).card : ℤ) -
      2 * ((Finset.univ.filter fun v : V => inVp (i + 2 * dir d) (maskOf (vType v)) = true).card : ℤ) +
      ((Finset.univ.filter fun v : V => diffPred i d (vType v) = true).card : ℤ) =
      ∑ a : Fin 89, v2 a * x a := by
    have hVp := card_filter_vType vType (fun a => inVp (i + 2 * dir d) (maskOf a))
    have hDf := card_filter_vType vType (diffPred i d)
    rw [hU0, hVp, hDf]
    simp only [v2, add_mul, sub_mul, mul_assoc, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, x]
  rw [hV2, hU0, hD1, hn_sum]
  have hbilin : ∀ f g : Fin 89 → ℤ,
      (∑ a : Fin 89, f a * x a) * (∑ b : Fin 89, g b * x b) =
      ∑ a : Fin 89, ∑ b : Fin 89, (f a * g b) * x a * x b := by
    intro f g
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => by ring
  have h100 : 100 * (∑ a : Fin 89, u0 a * x a) * (∑ b : Fin 89, d1 b * x b) =
      50 * ((∑ a : Fin 89, u0 a * x a) * (∑ b : Fin 89, d1 b * x b)) +
      50 * ((∑ a : Fin 89, d1 a * x a) * (∑ b : Fin 89, u0 b * x b)) := by
    have hsym : (∑ a : Fin 89, u0 a * x a) * (∑ b : Fin 89, d1 b * x b) =
        (∑ a : Fin 89, d1 a * x a) * (∑ b : Fin 89, u0 b * x b) := mul_comm _ _
    linarith
  rw [h100, sq, sq, hbilin u0 d1, hbilin d1 u0, hbilin v2 v2]
  have h11 : (∑ a : Fin 89, x a) * (∑ b : Fin 89, x b) =
      ∑ a : Fin 89, ∑ b : Fin 89, (1 : ℤ) * x a * x b := by
    simpa using hbilin (fun _ => 1) (fun _ => 1)
  rw [h11]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  dsimp [mTerm, u0, d1, v2]; ring

/- Main proof of `H2`. -/

theorem main_proof : OMA.Erdos128H1R1.H2 := by
  classical
  intro V _ G hTF _hmax h50 hδ _h3 _hnoG ⟨φ, hφ⟩
  let vMask : V → ℕ := fun v => ∑ k : Fin 11, if decide (G.Adj (φ k) v) then pow2 k else 0
  have hvMask_lt : ∀ v : V, vMask v < 2048 := fun v => sum_pow2_lt (fun k => decide (G.Adj (φ k) v))
  have hbit_vMask : ∀ (v : V) (k : Fin 11), hasBit (vMask v) k = decide (G.Adj (φ k) v) :=
    fun v k => hasBit_sum_pow2 (fun j => decide (G.Adj (φ j) v)) k
  have hisIndep : ∀ v : V, isIndepMask (vMask v) = true := by
    intro v
    unfold isIndepMask
    rw [List.all_eq_true]
    intro i _
    by_cases hi : G.Adj (φ i) v
    · have hb_i : hasBit (vMask v) i = true := by rw [hbit_vMask]; simp [hi]
      have hnot : ∀ d : Fin 11, (d = 1 ∨ d = 4 ∨ d = 7 ∨ d = 10) →
          hasBit (vMask v) (i + d) = false := by
        intro d hd
        rw [hbit_vMask, decide_eq_false_iff_not]
        intro h2
        have hphi : G.Adj (φ i) (φ (i + d)) := by
          apply hφ i (i + d)
          rcases hd with rfl | rfl | rfl | rfl <;> simp
        exact no_tri_of_cliqueFree3 hTF hphi h2 hi
      rw [hb_i, hnot 1 (by simp), hnot 4 (by simp), hnot 7 (by simp), hnot 10 (by simp)]
      rfl
    · have hb_i : hasBit (vMask v) i = false := by rw [hbit_vMask]; simp [hi]
      rw [hb_i]; rfl
  let vType : V → Fin 89 := fun v => idxOfMask (vMask v)
  have hmask_eq : ∀ v : V, maskOf (vType v) = vMask v := fun v =>
    maskOf_idxOfMask (vMask v) (hvMask_lt v) (hisIndep v)
  have hadj_iff : ∀ (v : V) (k : Fin 11), G.Adj (φ k) v ↔ hasBit (maskOf (vType v)) k = true := by
    intro v k
    rw [hmask_eq, hbit_vMask, decide_eq_true_eq]
  let x : Fin 89 → ℤ := fun a => ((Finset.univ.filter fun v : V => vType v = a).card : ℤ)
  have hx_nonneg : ∀ a : Fin 89, 0 ≤ x a := fun a => Nat.cast_nonneg _
  have hn_sum : (Fintype.card V : ℤ) = ∑ a : Fin 89, x a := by
    simpa [b2z, x] using card_filter_vType vType (fun _ => true)
  have hg_nonneg : ∀ k : Fin 11, 0 ≤ ∑ a : Fin 89, gCoeff k a * x a := by
    intro k
    let Sk : Finset V := Finset.univ.filter fun v => hasBit (maskOf (vType v)) k = true
    have hset : (Sk : Set V) = G.neighborSet (φ k) := by
      ext v
      simp only [Sk, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborSet]
      exact (hadj_iff v k).symm
    have hdeg : 5 * Fintype.card V ≤ 14 * Sk.card := by
      have hcard : (G.neighborSet (φ k)).ncard = Sk.card := by rw [← hset, Set.ncard_coe_finset]
      rw [← hcard]; exact hδ (φ k)
    have h1 : (∑ a : Fin 89, gCoeff k a * x a) = 14 * (Sk.card : ℤ) - 5 * (Fintype.card V : ℤ) := by
      have hS := card_filter_vType vType (fun a => hasBit (maskOf a) k)
      change (∑ a : Fin 89, (14 * b2z (hasBit (maskOf a) k) - 5) * x a) = _
      simp_rw [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
      change 14 * (∑ a : Fin 89, b2z (hasBit (maskOf a) k) * x a) - 5 * (∑ a : Fin 89, x a) = _
      rw [← hS, ← hn_sum]
    rw [h1]
    omega
  have hsum_pos : (0 : ℤ) < ∑ a : Fin 89, ∑ b : Fin 89, mInt a b * x a * x b := by
    have h22 : (0 : ℤ) < ∑ i : Fin 11,
        ((∑ a : Fin 89, ∑ b : Fin 89, mTerm i true a b * x a * x b) +
         (∑ a : Fin 89, ∑ b : Fin 89, mTerm i false a b * x a * x b)) := by
      refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
      have ht := pair_quad_bound G hTF h50 φ hφ vType hadj_iff hg_nonneg i true
      have hf := pair_quad_bound G hTF h50 φ hφ vType hadj_iff hg_nonneg i false
      have hteq := mTerm_sum_identity vType i true
      have hfeq := mTerm_sum_identity vType i false
      dsimp only at ht hf hteq hfeq
      linarith
    refine lt_of_lt_of_eq h22 ?_
    simp_rw [← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold mInt
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hLG_nonneg : (0 : ℤ) ≤ ∑ a : Fin 89, ∑ b : Fin 89, symLG a b * x a * x b := by
    have heq : (∑ a : Fin 89, ∑ b : Fin 89, symLG a b * x a * x b) =
        2 * ∑ k : Fin 11, (∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b) := by
      have hterm : ∀ k : Fin 11,
          2 * ((∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b)) =
          ∑ a : Fin 89, ∑ b : Fin 89,
            (Lval (invSh k a) * gCoeff k b + gCoeff k a * Lval (invSh k b)) * x a * x b := by
        intro k
        have h1 : (∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b) =
            ∑ a : Fin 89, ∑ b : Fin 89, (Lval (invSh k a) * gCoeff k b) * x a * x b := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => by ring
        have h2 : (∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b) =
            ∑ a : Fin 89, ∑ b : Fin 89, (gCoeff k a * Lval (invSh k b)) * x a * x b := by
          rw [mul_comm, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => by ring
        calc
          2 * ((∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b))
              = (∑ a : Fin 89, ∑ b : Fin 89, (Lval (invSh k a) * gCoeff k b) * x a * x b) +
                (∑ a : Fin 89, ∑ b : Fin 89, (gCoeff k a * Lval (invSh k b)) * x a * x b) := by
                  rw [← h1, ← h2]; ring
          _ = _ := by
                simp only [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      rw [Finset.mul_sum]
      simp_rw [hterm]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      unfold symLG
      simp only [Finset.sum_mul]
    rw [heq]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => ?_)
    exact mul_nonneg
      (Finset.sum_nonneg fun a _ => mul_nonneg (Lval_nonneg _) (hx_nonneg a))
      (hg_nonneg k)
  have hcomb_pos : (0 : ℤ) < ∑ a : Fin 89, ∑ b : Fin 89, certMat a b * x a * x b := by
    have heq : (∑ a : Fin 89, ∑ b : Fin 89, certMat a b * x a * x b) =
        20 * (∑ a : Fin 89, ∑ b : Fin 89, mInt a b * x a * x b) +
        (∑ a : Fin 89, ∑ b : Fin 89, symLG a b * x a * x b) := by
      simp only [certMat, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [heq]
    linarith
  have hcomb_nonpos : (∑ a : Fin 89, ∑ b : Fin 89, certMat a b * x a * x b) ≤ 0 := by
    refine Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => ?_
    have hxy : 0 ≤ x a * x b := mul_nonneg (hx_nonneg a) (hx_nonneg b)
    have hmul : certMat a b * (x a * x b) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (certMat_nonpos a b) hxy
    linarith
  linarith

end Erdos128_R2_H1_R1_H2

theorem h2_proof : OMA.Erdos128H1R1.H2 :=
  Erdos128_R2_H1_R1_H2.main_proof
end H2Section

theorem OMA.solution : OMA.R_Erdos128_erdos_128_R2.H1 :=
  OMA.Erdos128H1R1.main h1_proof h2_proof
