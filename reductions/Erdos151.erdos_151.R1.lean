import FormalConjectures.ErdosProblems.«151»

-- Reduction Erdos151.erdos_151.R1 of Erdős Problem 151
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Reduction to Ramsey-type graphs at the jumps of `H`

The target is `τ(G) ≤ n - H n` for every graph on `n` vertices, where `τ` is the clique
transversal number and `H n` the largest `k` such that every triangle-free graph on `n` vertices
has an independent set of size `k`. This file does not prove it. It proves two things.

* If some triangle-free graph `F` on the same vertices has an edge inside every maximal clique
  of `G` with at least two vertices, then `τ(G) ≤ n - H n`: an independent set of `F` of size
  `H n` contains no such clique, so its complement is a clique transversal. For a `K₄`-free `G`
  such an `F` exists exactly when the edges of `G` can be coloured red and blue without a
  monochromatic triangle. The triangle-free case `F = G` is the argument of the merged proof of
  `Erdos151.erdos_151.variants.cliqueFree_three` by @Genbox.
* If `H (n + 1) ≤ H n`, the bound for `n + 1` vertices follows from the bound for `n` vertices
  by deleting a vertex, since `τ(G) ≤ τ(G - v) + 1`.

So only graphs with no such `F`, on a number of vertices where `H` jumps (the Ramsey numbers
`R(3, k)`), remain. `H1` is that remainder for `K₄`-free graphs, where it concerns exactly the
graphs in which every red and blue colouring of the edges has a monochromatic triangle.
`H2` is the remainder for graphs containing a `K₄`. Both are open.
-/

namespace OMA.R_Erdos151_erdos_151_R1

open SimpleGraph

/-- The remainder for `K₄`-free graphs. -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))), Erdos151.H n < Erdos151.H (n + 1) →
    G.CliqueFree 4 →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) →
    cliqueTransversalNumber G ≤ (n + 1) - Erdos151.H (n + 1)

/-- The remainder for graphs containing a `K₄`. -/
def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))), Erdos151.H n < Erdos151.H (n + 1) →
    ¬ G.CliqueFree 4 →
    (¬ ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
      ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) →
    cliqueTransversalNumber G ≤ (n + 1) - Erdos151.H (n + 1)

/-- Every triangle-free graph on `n` vertices has an independent set of size `H n`. -/
lemma exists_indep_H (n : ℕ) (F : SimpleGraph (Fin n)) (hF : F.CliqueFree 3) :
    ∃ s, F.IsNIndepSet (Erdos151.H n) s := by
  let sizes : Set ℕ :=
    {k | ∀ F : SimpleGraph (Fin n), F.CliqueFree 3 → ∃ s, F.IsNIndepSet k s}
  have hnonempty : sizes.Nonempty := by
    refine ⟨0, ?_⟩
    change ∀ F : SimpleGraph (Fin n), F.CliqueFree 3 → ∃ s, F.IsNIndepSet 0 s
    intro F _
    exact ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩
  have hfinite : sizes.Finite := by
    refine (Set.finite_Iic n).subset ?_
    intro k hk
    change (∀ F : SimpleGraph (Fin n), F.CliqueFree 3 → ∃ s, F.IsNIndepSet k s) at hk
    obtain ⟨s, hs⟩ := hk F hF
    simpa [hs.card_eq] using Finset.card_le_univ s
  have hmem : Erdos151.H n ∈ sizes := hnonempty.csSup_mem hfinite
  exact hmem F hF

lemma H_le (n : ℕ) : Erdos151.H n ≤ n := by
  obtain ⟨s, hs⟩ := exists_indep_H n ⊥ (cliqueFree_bot (by norm_num))
  simpa [hs.card_eq] using Finset.card_le_univ s

/-- A triangle-free graph with an edge in every big maximal clique of `G` gives the bound. -/
lemma bound_of_hitting (n : ℕ) (G F : SimpleGraph (Fin n)) (hF : F.CliqueFree 3)
    (hit : ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v) :
    cliqueTransversalNumber G ≤ n - Erdos151.H n := by
  obtain ⟨s, hs⟩ := exists_indep_H n F hF
  have htransversal : G.IsCliqueTransversal sᶜ := by
    intro t ht
    obtain ⟨u, hu, v, hv, huv⟩ := hit t ht
    by_cases hsu : u ∈ s
    · by_cases hsv : v ∈ s
      · exact (hs.isIndepSet hsu hsv huv.ne huv).elim
      · exact ⟨v, hv, Finset.mem_compl.mpr hsv⟩
    · exact ⟨u, hu, Finset.mem_compl.mpr hsu⟩
  apply csInf_le'
  exact ⟨sᶜ, htransversal, by rw [Finset.card_compl, Fintype.card_fin, hs.card_eq]⟩

/-- Deleting the last vertex lowers the clique transversal number by at most one. -/
lemma transversal_delete (n : ℕ) (G : SimpleGraph (Fin (n + 1))) :
    cliqueTransversalNumber G ≤
      cliqueTransversalNumber (G.comap (Fin.castSucc : Fin n → Fin (n + 1))) + 1 := by
  classical
  set G' : SimpleGraph (Fin n) := G.comap (Fin.castSucc : Fin n → Fin (n + 1)) with hG'
  have hne : {k | ∃ T : Finset (Fin n), G'.IsCliqueTransversal T ∧ T.card = k}.Nonempty :=
    ⟨Finset.univ.card, Finset.univ, fun s hs => by
      obtain ⟨a, -, ha, -⟩ := Finset.one_lt_card_iff.mp hs.2
      exact ⟨a, ha, Finset.mem_univ a⟩, rfl⟩
  obtain ⟨T', hT', hcard⟩ := Nat.sInf_mem hne
  have hcard' : T'.card = cliqueTransversalNumber G' := hcard
  let T : Finset (Fin (n + 1)) := insert (Fin.last n) (T'.map Fin.castSuccEmb)
  have hT : G.IsCliqueTransversal T := by
    intro s hs
    by_cases hl : Fin.last n ∈ s
    · exact ⟨Fin.last n, hl, Finset.mem_insert_self _ _⟩
    · let s' : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.castSucc ∈ s)
      have hmem' : ∀ i : Fin n, i ∈ s' ↔ i.castSucc ∈ s := by
        intro i; simp [s']
      have hsurj : ∀ x ∈ s, ∃ i : Fin n, i.castSucc = x := by
        intro x hx
        have hx' : x ≠ Fin.last n := fun h => hl (h ▸ hx)
        exact ⟨x.castPred hx', Fin.castSucc_castPred x hx'⟩
      have hclique : G'.IsClique (s' : Set (Fin n)) := by
        intro a ha b hb hab
        have ha' := (hmem' a).mp (Finset.mem_coe.mp ha)
        have hb' := (hmem' b).mp (Finset.mem_coe.mp hb)
        exact hs.1.1 (Finset.mem_coe.mpr ha') (Finset.mem_coe.mpr hb')
          (fun h => hab (Fin.castSucc_injective n h))
      have hmax : Maximal (fun t : Finset (Fin n) => G'.IsClique (t : Set (Fin n))) s' := by
        refine ⟨hclique, ?_⟩
        intro t' ht' hst' i hi
        let t : Finset (Fin (n + 1)) := t'.map Fin.castSuccEmb
        have htc : G.IsClique (t : Set (Fin (n + 1))) := by
          intro a ha b hb hab
          simp only [t, Finset.coe_map, Set.mem_image, Finset.mem_coe] at ha hb
          obtain ⟨a', ha', rfl⟩ := ha
          obtain ⟨b', hb', rfl⟩ := hb
          exact ht' (Finset.mem_coe.mpr ha') (Finset.mem_coe.mpr hb')
            (fun h => hab (by rw [h]))
        have hst : s ≤ t := by
          intro x hx
          obtain ⟨j, rfl⟩ := hsurj x hx
          exact Finset.mem_map.mpr ⟨j, hst' ((hmem' j).mpr hx), rfl⟩
        have hts : t ≤ s := hs.1.2 htc hst
        have : i.castSucc ∈ s := hts (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
        exact (hmem' i).mpr this
      have hcard2 : 2 ≤ s'.card := by
        have hmap : s'.map Fin.castSuccEmb = s := by
          ext x
          constructor
          · intro hx
            obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
            exact (hmem' j).mp hj
          · intro hx
            obtain ⟨j, rfl⟩ := hsurj x hx
            exact Finset.mem_map.mpr ⟨j, (hmem' j).mpr hx, rfl⟩
        have := hs.2
        rw [← hmap, Finset.card_map] at this
        exact this
      obtain ⟨v, hv, hvT⟩ := hT' s' ⟨hmax, hcard2⟩
      exact ⟨v.castSucc, (hmem' v).mp hv,
        Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨v, hvT, rfl⟩)⟩
  have h1 : cliqueTransversalNumber G ≤ T.card := csInf_le' ⟨T, hT, rfl⟩
  have h2 : T.card ≤ T'.card + 1 := by
    have := Finset.card_insert_le (Fin.last n) (T'.map Fin.castSuccEmb)
    rw [Finset.card_map] at this
    exact this
  omega

theorem main : H1 → H2 → type_of% @Erdos151.erdos_151 := by
  intro h1 h2 n
  induction n with
  | zero =>
    intro G
    have : cliqueTransversalNumber G ≤ 0 := by
      apply csInf_le'
      refine ⟨∅, ?_, rfl⟩
      intro s hs
      obtain ⟨a, -, -, -⟩ := Finset.one_lt_card_iff.mp hs.2
      exact a.elim0
    omega
  | succ n ih =>
    intro G
    by_cases hjump : Erdos151.H n < Erdos151.H (n + 1)
    · by_cases hgood : ∃ F : SimpleGraph (Fin (n + 1)), F.CliqueFree 3 ∧
          ∀ s, G.IsBigMaximalClique s → ∃ u ∈ s, ∃ v ∈ s, F.Adj u v
      · obtain ⟨F, hF, hit⟩ := hgood
        exact bound_of_hitting (n + 1) G F hF hit
      · by_cases hK : G.CliqueFree 4
        · exact h1 n G hjump hK hgood
        · exact h2 n G hjump hK hgood
    · have hdel := transversal_delete n G
      have hih := ih (G.comap (Fin.castSucc : Fin n → Fin (n + 1)))
      have hHn := H_le n
      omega

end OMA.R_Erdos151_erdos_151_R1
