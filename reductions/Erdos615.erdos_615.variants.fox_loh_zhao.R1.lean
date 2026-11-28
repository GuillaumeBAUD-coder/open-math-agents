import FormalConjectures.ErdosProblems.«615»

-- Reduction Erdos615.erdos_615.variants.fox_loh_zhao.R1 of the Fox-Loh-Zhao lower bound
-- Source: J. Fox, P.-S. Loh, Y. Zhao, The critical window for the classical Ramsey-Turan
--   problem, Combinatorica 35 (2015), 435-476, arXiv:1208.3276, Theorem 8.1 and the proof of
--   Theorem 1.10.
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The Fox-Loh-Zhao lower bound from the quantitative Bollobas-Erdos graph

Fox, Loh and Zhao derive their Theorem 1.10 (the target) from their Theorem 8.1, a quantitative
form of the Bollobas-Erdos construction, by choosing the dimension `h` about
`log n / log log n`. This file records exactly that derivation.

* `H1` (Fox-Loh-Zhao, Theorem 8.1): there is a universal constant `C > 0` such that for every
  `0 < ε < 1`, every integer `h ≥ 16` and every even `n ≥ (C √h / ε) ^ h` there is a nice
  graph on `n` vertices (`K_4`-free, with a bipartition into two triangle-free halves) with
  independence number at most `2 n exp (-ε √h / 4)` and minimum degree at least `(1/4 - 2ε) n`.
  This is the only deep input: the Bollobas-Erdos graph on a Feige-Schechtman partition of the
  sphere `S^(h-1)`, analysed with the isoperimetric inequality on the sphere (measure
  concentration) and Schmidt's theorem.
* `H2` (padding, elementary): a `K_4`-free graph on `m` vertices extends by `n - m` isolated
  vertices to a `K_4`-free graph on `n` vertices; the independence number grows by at most
  `n - m` and no edge is lost. This handles odd `n`.
* `H3` (choice of parameters, elementary real analysis): for `f = o(√(log n / log log n))`, a
  fixed small `δ`, `h = ⌊log n / log log n⌋` and `m` the largest even number at most `n`, the
  size condition of `H1` holds and its bounds imply the ones required by the target.

`main` glues the three and turns the minimum degree bound into an edge count by the handshake
lemma.
-/

namespace OMA.R_Erdos615_erdos_615_variants_fox_loh_zhao_R1

open Filter SimpleGraph

/-- Fox-Loh-Zhao, Theorem 8.1: the quantitative Bollobas-Erdos graph. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ h : ℕ, 16 ≤ h → ∀ n : ℕ, Even n →
    (C * Real.sqrt h / ε) ^ h ≤ (n : ℝ) →
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
      (∃ X : Set (Fin n), X.ncard = n / 2 ∧
        (G.induce X).CliqueFree 3 ∧ (G.induce Xᶜ).CliqueFree 3) ∧
      (G.indepNum : ℝ) ≤ 2 * n * Real.exp (-ε * Real.sqrt h / 4) ∧
      ∀ v, (1 / 4 - 2 * ε) * n ≤ ((G.neighborSet v).ncard : ℝ)

/-- Padding with isolated vertices. -/
def H2 : Prop :=
  ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G.CliqueFree 4 → ∀ n : ℕ, m ≤ n →
    ∃ G' : SimpleGraph (Fin n), G'.CliqueFree 4 ∧ G'.indepNum ≤ G.indepNum + (n - m) ∧
      G.edgeSet.ncard ≤ G'.edgeSet.ncard

/-- The choice of parameters in the proof of Theorem 1.10 of Fox-Loh-Zhao. -/
def H3 : Prop :=
  ∀ C : ℝ, 0 < C → ∀ f : ℕ → ℝ, (∀ n, 0 ≤ f n) →
    Tendsto (fun n : ℕ => f n / Real.sqrt (Real.log n / Real.log (Real.log n))) atTop (nhds 0) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ᶠ (n : ℕ) in atTop, ∃ h m : ℕ,
      16 ≤ h ∧ Even m ∧ m ≤ n ∧ (C * Real.sqrt h / δ) ^ h ≤ (m : ℝ) ∧
      2 * m * Real.exp (-δ * Real.sqrt h / 4) + ((n : ℝ) - m) ≤ n * Real.exp (-f n) ∧
      (1 / 8 - ε) * (n : ℝ) ^ 2 ≤ (1 / 4 - 2 * δ) * (m : ℝ) ^ 2 / 2

/-- Handshake lemma: minimum degree at least `d` forces at least `m d / 2` edges. -/
lemma edges_of_min_degree {m : ℕ} (G : SimpleGraph (Fin m)) (d : ℝ)
    (hdeg : ∀ v, d ≤ ((G.neighborSet v).ncard : ℝ)) : d * m / 2 ≤ (G.edgeSet.ncard : ℝ) := by
  classical
  have h2E : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hdeg' : ∀ v, d ≤ (G.degree v : ℝ) := by
    intro v
    have h := hdeg v
    rw [Set.ncard_eq_toFinset_card'] at h
    exact h
  have hE : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have hsum : (m : ℝ) * d ≤ ∑ v : Fin m, (G.degree v : ℝ) := by
    calc (m : ℝ) * d = ∑ _v : Fin m, d := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hdeg' v)
  have hcast : (∑ v : Fin m, (G.degree v : ℝ)) = 2 * (G.edgeSet.ncard : ℝ) := by
    rw [← hE]
    exact_mod_cast h2E
  linarith

theorem main : H1 → H2 → H3 → type_of% @Erdos615.erdos_615.variants.fox_loh_zhao := by
  intro h1 h2 h3 f hf hfo ε hε
  obtain ⟨C, hC, hBE⟩ := h1
  obtain ⟨δ, hδ0, hδ1, hev⟩ := h3 C hC f hf hfo ε hε
  filter_upwards [hev] with n hn
  obtain ⟨h, m, hh, hm, hmn, hsize, hα, hedge⟩ := hn
  obtain ⟨G, hK4, _, hind, hdeg⟩ := hBE δ hδ0 hδ1 h hh m hm hsize
  obtain ⟨G', hK4', hind', hedge'⟩ := h2 m G hK4 n hmn
  refine ⟨G', hK4', ?_, ?_⟩
  · have h1' : (G'.indepNum : ℝ) ≤ (G.indepNum : ℝ) + ((n : ℝ) - m) := by
      have : (G'.indepNum : ℝ) ≤ ((G.indepNum + (n - m) : ℕ) : ℝ) := by exact_mod_cast hind'
      rw [Nat.cast_add, Nat.cast_sub hmn] at this
      exact this
    linarith
  · have hE := edges_of_min_degree G _ hdeg
    have hE' : (G.edgeSet.ncard : ℝ) ≤ (G'.edgeSet.ncard : ℝ) := by exact_mod_cast hedge'
    rw [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card']
    nlinarith

end OMA.R_Erdos615_erdos_615_variants_fox_loh_zhao_R1
