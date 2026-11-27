import FormalConjectures.ErdosProblems.«165»

-- Credit: @skytracker404

open Filter SimpleGraph
open scoped Asymptotics Topology

namespace OMA.R_Erdos165_erdos_165_variants_conjecture_R1

/-- The lower bound of Hefty, Horn, King and Pfender, arXiv:2510.19718. -/
def H1 : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
    (1 - δ) * ((k : ℝ) ^ 2 / (2 * Real.log k)) ≤ (classicalRamsey 3 k : ℝ)

/-- Shearer's bound handles graphs of average degree at most `k / 2`. -/
def H2 : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (1 + δ) * ((k : ℝ) ^ 2 / (2 * Real.log k)) < n →
      G.CliqueFree 3 → 4 * G.edgeSet.ncard ≤ n * k → ¬G.IndepSetFree k

/-- The open case concerns maximal triangle-free graphs with maximum degree below `k`
and average degree above `k / 2` in every induced subgraph whose order exceeds the lower
threshold with slack `δ / 2`. -/
def H3 : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (1 + δ) * ((k : ℝ) ^ 2 / (2 * Real.log k)) < n →
      Maximal (fun H : SimpleGraph (Fin n) ↦ H.CliqueFree 3) G →
      (∀ v, (G.neighborSet v).ncard < k) →
      (∀ (m : ℕ) (e : Fin m ↪ Fin n),
        (1 + δ / 2) * ((k : ℝ) ^ 2 / (2 * Real.log k)) < m →
        m * k < 4 * (G.comap e).edgeSet.ncard) →
      ¬G.IndepSetFree k

lemma degree_lt_of_indepSetFree {n k : ℕ} {G : SimpleGraph (Fin n)}
    (htriangle : G.CliqueFree 3) (hindep : G.IndepSetFree k) (v : Fin n) :
    (G.neighborSet v).ncard < k := by
  classical
  by_contra! hdegree
  rw [← G.coe_neighborFinset v, Set.ncard_coe_finset] at hdegree
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hdegree
  apply hindep s
  refine ⟨Set.Pairwise.mono ?_ (G.isIndepSet_neighborSet_of_triangleFree htriangle v), hcard⟩
  intro w hw
  rw [← G.coe_neighborFinset v]
  exact hs hw

lemma eventually_ramsey_property (hsparse : H2) (hdense : H3) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      (1 + δ) * ((k : ℝ) ^ 2 / (2 * Real.log k)) < n →
      (∀ G : SimpleGraph (Fin n),
        (completeGraph (Fin 3)).IsContained G ∨ (completeGraph (Fin k)).IsContained Gᶜ) := by
  classical
  have hhalf : 0 < δ / 2 := by positivity
  filter_upwards [hsparse (δ / 2) hhalf, hdense δ hδ] with k hs hd
  intro n hn G
  by_cases htriangle : G.CliqueFree 3
  · right
    apply (not_cliqueFree_iff_top_isContained k).mp
    rw [cliqueFree_compl]
    intro hindep
    obtain ⟨H, hGH, hmax⟩ := Finite.exists_le_maximal
      (p := fun H : SimpleGraph (Fin n) ↦ H.CliqueFree 3) htriangle
    have hcompl : Hᶜ.CliqueFree k := (G.cliqueFree_compl.mpr hindep).anti (compl_le_compl hGH)
    have hHindep := H.cliqueFree_compl.mp hcompl
    apply hd n H hn hmax (degree_lt_of_indepSetFree hmax.prop hHindep) _ hHindep
    intro m e hm
    by_contra! hedge
    have hsub := SimpleGraph.Embedding.comap e H
    have hsubtriangle : (H.comap e).CliqueFree 3 := hmax.prop.comap hsub.isContained
    have hsubcompl : (H.comap e)ᶜ.CliqueFree k :=
      hcompl.comap (SimpleGraph.Embedding.complEquiv hsub).isContained
    exact hs m (H.comap e) hm hsubtriangle hedge ((H.comap e).cliqueFree_compl.mp hsubcompl)
  · exact Or.inl ((not_cliqueFree_iff_top_isContained 3).mp htriangle)

theorem main : H1 → H2 → H3 → type_of% @Erdos165.erdos_165.variants.conjecture := by
  intro hlower hsparse hdense
  apply Asymptotics.isEquivalent_of_tendsto_one
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / 4 := by positivity
  have hlarge : ∀ᶠ k : ℕ in atTop, 8 / ε ≤ (k : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (8 / ε)
  filter_upwards [hlower (ε / 4) hδ, eventually_ramsey_property hsparse hdense (ε / 4) hδ,
    eventually_ge_atTop (2 : ℕ), hlarge] with k hlow hproperty hk hlargek
  let g : ℝ := (k : ℝ) ^ 2 / (2 * Real.log k)
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
  have hg : 0 < g := by dsimp [g]; positivity
  have hgk : (k : ℝ) / 2 ≤ g := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log (k : ℝ))).2
    have hlogk := Real.log_le_sub_one_of_pos (show 0 < (k : ℝ) by linarith)
    nlinarith
  have hround : 1 ≤ ε / 4 * g := by
    have hbig := (div_le_iff₀ hε).mp hlargek
    have hscale := mul_le_mul_of_nonneg_left hgk hε.le
    nlinarith
  let t : ℝ := (1 + ε / 4) * g
  let n := ⌊t⌋₊ + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htn : t < (n : ℝ) := by simpa [n] using Nat.lt_floor_add_one t
  have hnt : (n : ℝ) ≤ t + 1 := by
    simpa [n] using add_le_add_right (Nat.floor_le ht) (1 : ℝ)
  have hramsey : classicalRamsey 3 k ≤ n := Nat.sInf_le (hproperty n htn)
  have hramseyReal : (classicalRamsey 3 k : ℝ) ≤ n := by exact_mod_cast hramsey
  have hup : (classicalRamsey 3 k : ℝ) ≤ (1 + ε / 2) * g := by
    dsimp [t] at hnt
    linarith
  have hrlo : 1 - ε / 4 ≤ (classicalRamsey 3 k : ℝ) / g := (le_div_iff₀ hg).2 hlow
  have hrup : (classicalRamsey 3 k : ℝ) / g ≤ 1 + ε / 2 := (div_le_iff₀ hg).2 hup
  change dist ((classicalRamsey 3 k : ℝ) / g) 1 < ε
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end OMA.R_Erdos165_erdos_165_variants_conjecture_R1
