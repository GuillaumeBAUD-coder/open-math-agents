import OMAStatements.S_wp_1_factorization_conjecture

-- Reduction wp-1-factorization-conjecture.R1 of 1-factorization conjecture
-- Credit: @PandaWill
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- A k-regular graph is 1-factorable iff its edges have a proper k-colouring (proved below: every colour
-- class is a perfect matching). The split is by density:
--   H1: the dense range 7k ≥ 12n, a known theorem (Chetwynd–Hilton 1985, "Regular graphs of high degree
--       are 1-factorizable", Proc. LMS 50, 193–206).
--   H2: the open middle range of the conjecture, n (or n - 1) ≤ k < 12n/7. Proved for all sufficiently large n
--       by Csaba–Kühn–Lo–Osthus–Treglown (Mem. AMS 2016), open in general.

namespace OMA.R_wp_1_factorization_conjecture_R1

open SimpleGraph

def H1 : Prop :=
  ∀ n k : ℕ, 12 * n ≤ 7 * k →
    ∀ (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj],
      G.IsRegularOfDegree k → Nonempty (G.lineGraph.Coloring (Fin k))

def H2 : Prop :=
  ∀ n k : ℕ, ((Odd n ∧ n ≤ k) ∨ (Even n ∧ n - 1 ≤ k)) → 7 * k < 12 * n →
    ∀ (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj],
      G.IsRegularOfDegree k → Nonempty (G.lineGraph.Coloring (Fin k))

lemma factorable_of_coloring {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hG : G.IsRegularOfDegree k) (c : G.lineGraph.Coloring (Fin k)) :
    OMA.S_wp_1_factorization_conjecture.IsOneFactorable G := by
  classical
  let col : ∀ v w, G.Adj v w → Fin k := fun v w h => c ⟨s(v, w), h⟩
  have colsymm : ∀ v w (h : G.Adj v w), col w v h.symm = col v w h := by
    intro v w h; simp only [col, Sym2.eq_swap]
  let M : Fin k → G.Subgraph := fun i =>
    { verts := Set.univ
      Adj := fun v w => ∃ h : G.Adj v w, col v w h = i
      adj_sub := fun ⟨h, _⟩ => h
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun v w ⟨h, e⟩ => ⟨h.symm, (colsymm v w h).trans e⟩⟩ }
  -- the colours at a vertex are distinct
  have inj : ∀ v w w' (h : G.Adj v w) (h' : G.Adj v w'), col v w h = col v w' h' → w = w' := by
    intro v w w' h h' e
    by_contra hne
    have hadj : G.lineGraph.Adj ⟨s(v, w), h⟩ ⟨s(v, w'), h'⟩ := by
      rw [lineGraph_adj_iff_exists]
      refine ⟨?_, v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
      intro heq
      have := congrArg Subtype.val heq
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at this
      rcases this with ⟨-, h2⟩ | ⟨h1, h2⟩
      · exact hne h2
      · exact hne (h2.trans h1)
    exact c.valid hadj e
  refine ⟨Fin k, M, ?_, ?_, ?_⟩
  · intro i
    rw [Subgraph.isPerfectMatching_iff]
    intro v
    let f : ∀ w, w ∈ G.neighborFinset v → Fin k := fun w hw => col v w ((mem_neighborFinset _ _ _).1 hw)
    obtain ⟨w, hw, e⟩ := Finset.surj_on_of_inj_on_of_card_le f (fun _ _ => Finset.mem_univ _)
      (fun a b ha hb hab => inj v a b _ _ hab) (by simp [card_neighborFinset_eq_degree, hG v]) i
      (Finset.mem_univ _)
    refine ⟨w, ⟨(mem_neighborFinset _ _ _).1 hw, e.symm⟩, ?_⟩
    rintro y ⟨hy, ey⟩
    exact inj v y w hy _ (ey.trans e)
  · intro i j hij
    rw [Set.disjoint_left]
    intro e
    induction e using Sym2.ind with
    | _ v w =>
      simp only [Subgraph.mem_edgeSet]
      rintro ⟨h, hi⟩ ⟨h', hj⟩
      exact hij (hi.symm.trans hj)
  · intro e he
    induction e using Sym2.ind with
    | _ v w => exact ⟨col v w he, by simp only [Subgraph.mem_edgeSet]; exact ⟨he, rfl⟩⟩

theorem main : H1 → H2 → type_of% @OMA.S_wp_1_factorization_conjecture.main := by
  intro h1 h2 n k hk G _ hG
  by_cases h : 12 * n ≤ 7 * k
  · exact factorable_of_coloring G k hG (h1 n k h G hG).some
  · exact factorable_of_coloring G k hG (h2 n k hk (by omega) G hG).some

end OMA.R_wp_1_factorization_conjecture_R1
