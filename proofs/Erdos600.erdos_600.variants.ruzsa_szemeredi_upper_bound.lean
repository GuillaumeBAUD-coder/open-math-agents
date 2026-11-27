import FormalConjectures.ErdosProblems.«600»

-- Problem: Erdős Problem 600 — ruzsa szemeredi upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/600.lean:71 (declaration Erdos600.erdos_600.variants.ruzsa_szemeredi_upper_bound)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter
open scoped Topology

namespace OMA.W15b
open Erdos600 SimpleGraph


open Classical in
lemma core {n r : ℕ} {ε : ℝ} (G : SimpleGraph (Fin n))
    (hall : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty)
    (hfew : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r)
    (hT : ((G.cliqueFinset 3).card : ℝ) < triangleRemovalBound ε * (n : ℝ) ^ 3) :
    (G.edgeFinset.card : ℝ) ≤ 6 * r * (ε * (n : ℝ) ^ 2) := by
  have hT' : ((G.cliqueFinset 3).card : ℝ) <
      triangleRemovalBound ε * (Fintype.card (Fin n) : ℝ) ^ 3 := by simpa using hT
  obtain ⟨G', hG'le, _, hcard, hfree⟩ := triangle_removal hT'
  set R := G.edgeFinset \ G'.edgeFinset with hR
  have hsub : G'.edgeFinset ⊆ G.edgeFinset := edgeFinset_mono hG'le
  have hRcard : (R.card : ℝ) < ε * (n : ℝ) ^ 2 := by
    rw [hR, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    simpa using hcard
  have hcover : G.edgeFinset ⊆
      R.biUnion fun f => (G.trianglesContaining f).biUnion fun t => t.sym2 := by
    intro e he
    obtain ⟨t, ht⟩ := hall e he
    have ht' := ht
    simp only [trianglesContaining, Finset.mem_filter, mem_cliqueFinset_iff] at ht'
    obtain ⟨htc, hes⟩ := ht'
    have hnc : ¬ G'.IsNClique 3 t := fun h => hfree t h
    have hnclq : ¬ G'.IsClique (t : Set (Fin n)) := fun h => hnc ⟨h, htc.2⟩
    rw [SimpleGraph.IsClique, Set.Pairwise] at hnclq
    push Not at hnclq
    obtain ⟨x, hx, y, hy, hxy, hnadj⟩ := hnclq
    rw [Finset.mem_biUnion]
    refine ⟨s(x, y), ?_, ?_⟩
    · rw [hR, Finset.mem_sdiff, mem_edgeFinset, mem_edgeFinset]
      exact ⟨htc.1 hx hy hxy, hnadj⟩
    · rw [Finset.mem_biUnion]
      refine ⟨t, ?_, ?_⟩
      · simp only [trianglesContaining, Finset.mem_filter, mem_cliqueFinset_iff]
        refine ⟨htc, ?_⟩
        intro z hz
        simp only [Sym2.mem_toFinset, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
      · induction e using Sym2.ind with
        | h u v =>
          rw [Finset.mk_mem_sym2_iff]
          exact ⟨hes (by simp), hes (by simp)⟩
  have hle := Finset.card_le_card hcover
  have hb : (R.biUnion fun f => (G.trianglesContaining f).biUnion fun t => t.sym2).card ≤
      R.card * (r * 6) := by
    refine Finset.card_biUnion_le_card_mul _ _ _ fun f hf => ?_
    have hfE : f ∈ G.edgeFinset := (Finset.mem_sdiff.1 hf).1
    refine (Finset.card_biUnion_le_card_mul _ _ 6 fun t ht => ?_).trans ?_
    · simp only [trianglesContaining, Finset.mem_filter, mem_cliqueFinset_iff] at ht
      rw [Finset.card_sym2, ht.1.2]; decide
    · exact Nat.mul_le_mul_right _ (hfew f hfE).le
  have : (G.edgeFinset.card : ℝ) ≤ R.card * (r * 6) := by exact_mod_cast hle.trans hb
  nlinarith [(by positivity : (0 : ℝ) ≤ r)]

open Classical in
lemma triangles_le {n r : ℕ} (G : SimpleGraph (Fin n))
    (hfew : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r) :
    ((G.cliqueFinset 3).card : ℝ) ≤ r * (n : ℝ) ^ 2 := by
  have hcov : G.cliqueFinset 3 ⊆ G.edgeFinset.biUnion fun e => G.trianglesContaining e := by
    intro t ht
    have ht' := ht
    rw [mem_cliqueFinset_iff] at ht'
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := (is3Clique_iff.1 ht')
    rw [Finset.mem_biUnion]
    refine ⟨s(x, y), (mem_edgeFinset).2 hxy, ?_⟩
    simp only [trianglesContaining, Finset.mem_filter]
    refine ⟨by convert ht, ?_⟩
    intro w hw
    simp only [Sym2.mem_toFinset, Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> simp
  have h1 := (Finset.card_le_card hcov).trans
    (Finset.card_biUnion_le_card_mul _ _ r fun e he => (hfew e he).le)
  have h2 : G.edgeFinset.card ≤ n ^ 2 := by
    refine (card_edgeFinset_le_card_choose_two).trans ?_
    simp only [Fintype.card_fin]
    exact (Nat.choose_le_pow n 2).trans le_rfl
  have h3 : (G.cliqueFinset 3).card ≤ r * n ^ 2 := by
    calc _ ≤ G.edgeFinset.card * r := by convert h1
      _ ≤ n ^ 2 * r := Nat.mul_le_mul_right _ h2
      _ = r * n ^ 2 := by ring
  exact_mod_cast h3

open Classical in
theorem main : ∀ r : ℕ, (fun (n : ℕ) ↦ (eFunction n r : ℝ)) =o[atTop] (fun (n : ℕ) ↦ (n : ℝ)^2) := by
  intro r
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set ε : ℝ := c / (12 * (r + 1)) with hε
  have hε0 : 0 < ε := by positivity
  set δ := triangleRemovalBound ε
  have hδ : 0 < δ := triangleRemovalBound_pos hε0
  obtain ⟨N1, hN1⟩ := exists_nat_gt (r / δ)
  obtain ⟨N2, hN2⟩ := exists_nat_gt (2 / c)
  rw [eventually_atTop]
  refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
  have hn1 : (N1 : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn2 : (N2 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by linarith
  -- c n^2 ≥ 2
  have hcn : 2 ≤ c * (n : ℝ) ^ 2 := by
    have h1 : 2 / c < n := lt_of_lt_of_le hN2 hn2
    have h2 : 2 < c * n := by rwa [div_lt_iff₀ hc, mul_comm] at h1
    nlinarith
  -- triangle count small
  have hrn : (r : ℝ) < δ * n := by
    have h1 : r / δ < n := lt_of_lt_of_le hN1 hn1
    rwa [div_lt_iff₀ hδ, mul_comm] at h1
  have hprop : Erdos600Prop n ⌊c * (n : ℝ) ^ 2⌋₊ r := by
    intro G hcard hall
    by_contra hno
    push Not at hno
    have hT : ((G.cliqueFinset 3).card : ℝ) < triangleRemovalBound ε * (n : ℝ) ^ 3 := by
      have := triangles_le G hno
      have : (r : ℝ) * n ^ 2 < δ * n ^ 3 := by
        have : (r : ℝ) * n ^ 2 < δ * n * n ^ 2 := by
          exact mul_lt_mul_of_pos_right hrn (by positivity)
        nlinarith
      linarith
    have hE := core G hall hno hT
    have hfl : c * (n : ℝ) ^ 2 - 1 < ⌊c * (n : ℝ) ^ 2⌋₊ := Nat.sub_one_lt_floor _
    have hc' : (G.edgeFinset.card : ℝ) ≥ ⌊c * (n : ℝ) ^ 2⌋₊ := by exact_mod_cast hcard
    have hr6 : 6 * (r : ℝ) * ε ≤ c / 2 := by
      rw [hε]
      have hr0 : (0 : ℝ) ≤ r := by positivity
      rw [show 6 * (r : ℝ) * (c / (12 * (r + 1))) = c / 2 * (r / (r + 1)) by field_simp; ring]
      have : (r : ℝ) / (r + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith
    have : 6 * (r : ℝ) * (ε * (n : ℝ) ^ 2) ≤ c / 2 * (n : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hr6 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)
      linarith
    nlinarith
  have hle : eFunction n r ≤ ⌊c * (n : ℝ) ^ 2⌋₊ := Nat.sInf_le hprop
  have hle' : (eFunction n r : ℝ) ≤ c * (n : ℝ) ^ 2 :=
    (Nat.cast_le.2 hle).trans (Nat.floor_le (by positivity))
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (eFunction n r : ℝ)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
  exact hle'

end OMA.W15b

theorem OMA.solution : type_of% @Erdos600.erdos_600.variants.ruzsa_szemeredi_upper_bound := by
  exact OMA.W15b.main
