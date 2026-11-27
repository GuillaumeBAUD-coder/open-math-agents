import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1
import Mathlib

/-! A finite certificate covers all triangle-free links on six labelled
vertices. Every leaf either forces a triangle or exhibits a vertex
two-coloring with at most one monochromatic edge. Flipping the labels if
necessary lets this coloring extend an arbitrary old edge coloring over one
more vertex. -/

open Finset SimpleGraph

namespace OMA.SmallTriangleFree

private abbrev Pair := Fin 6 × Fin 6

private inductive Certificate
  | triangle (a b c : Fin 6)
  | color (mask : ℕ)
  | split (a b : Fin 6) (edge missing : Certificate)

private def orderedPairs : Finset Pair := univ.filter (fun e => e.1 < e.2)

private def maskColor (m : ℕ) (v : Fin 6) : Bool := m.testBit v.val

private def valid : Certificate → Finset Pair → Finset Pair → Bool
  | .triangle a b c, yes, _ => decide ((a,b) ∈ yes ∧ (a,c) ∈ yes ∧ (b,c) ∈ yes)
  | .color m, _, no =>
      decide (((orderedPairs \ no).filter
        (fun e => maskColor m e.1 = maskColor m e.2)).card ≤ 1)
  | .split a b l r, yes, no => valid l (insert (a,b) yes) no && valid r yes (insert (a,b) no)

private theorem valid_sound (G : SimpleGraph (Fin 6)) (hG : G.CliqueFree 3) (t : Certificate)
    (yes no : Finset Pair) (h : valid t yes no = true)
    (hy : ∀ e ∈ yes, G.Adj e.1 e.2) (hn : ∀ e ∈ no, ¬ G.Adj e.1 e.2) :
    ∃ f : Fin 6 → Bool, ∀ a b c d : Fin 6, a < b → c < d →
      G.Adj a b → G.Adj c d → f a = f b → f c = f d → (a,b) = (c,d) := by
  induction t generalizing yes no with
  | triangle a b c =>
    have ht : (a,b) ∈ yes ∧ (a,c) ∈ yes ∧ (b,c) ∈ yes := of_decide_eq_true h
    exact (hG _ (is3Clique_triple_iff.mpr ⟨hy (a,b) ht.1,hy (a,c) ht.2.1,hy (b,c) ht.2.2⟩)).elim
  | color m =>
    have hcard : ((orderedPairs \ no).filter
        (fun e => maskColor m e.1 = maskColor m e.2)).card ≤ 1 := of_decide_eq_true h
    refine ⟨maskColor m,?_⟩
    intro a b c d hab hcd habG hcdG habF hcdF
    have hmem (a b : Fin 6) (hAB : a < b) (hG' : G.Adj a b)
        (hF : maskColor m a = maskColor m b) :
        (a,b) ∈ (orderedPairs \ no).filter (fun e => maskColor m e.1 = maskColor m e.2) :=
      mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,hAB⟩,
        fun hx => hn _ hx hG'⟩,hF⟩
    exact (card_le_one.mp hcard) (a,b) (hmem a b hab habG habF) (c,d) (hmem c d hcd hcdG hcdF)
  | split a b l r ihl ihr =>
    change (valid l (insert (a,b) yes) no && valid r yes (insert (a,b) no)) = true at h
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp h
    by_cases hAB : G.Adj a b
    · apply ihl _ _ hl _ hn
      intro e he
      rcases mem_insert.mp he with he|he
      · simpa only [he] using hAB
      · exact hy e he
    · apply ihr _ _ hr hy
      intro e he
      rcases mem_insert.mp he with he|he
      · simpa only [he] using hAB
      · exact hn e he

-- A branch fixes one edge. A leaf exhibits a triangle in the forced edges
-- or a coloring with at most one same-color edge among the remaining possibilities.
private def sixCertificate : Certificate :=
  .split 0 1
    (
      .split 0 2
        (
          .split 1 2
            (
              .triangle 0 1 2
            )
            (
              .split 0 3
                (
                  .split 1 3
                    (
                      .triangle 0 1 3
                    )
                    (
                      .split 2 3
                        (
                          .triangle 0 2 3
                        )
                        (
                          .split 0 4
                            (
                              .split 1 4
                                (
                                  .triangle 0 1 4
                                )
                                (
                                  .split 2 4
                                    (
                                      .triangle 0 2 4
                                    )
                                    (
                                      .split 3 4
                                        (
                                          .triangle 0 3 4
                                        )
                                        (
                                          .color 30
                                        )
                                    )
                                )
                            )
                            (
                              .split 0 5
                                (
                                  .split 1 5
                                    (
                                      .triangle 0 1 5
                                    )
                                    (
                                      .split 2 5
                                        (
                                          .triangle 0 2 5
                                        )
                                        (
                                          .color 17
                                        )
                                    )
                                )
                                (
                                  .color 14
                                )
                            )
                        )
                    )
                )
                (
                  .split 0 4
                    (
                      .split 1 4
                        (
                          .triangle 0 1 4
                        )
                        (
                          .split 2 4
                            (
                              .triangle 0 2 4
                            )
                            (
                              .split 0 5
                                (
                                  .split 1 5
                                    (
                                      .triangle 0 1 5
                                    )
                                    (
                                      .split 2 5
                                        (
                                          .triangle 0 2 5
                                        )
                                        (
                                          .color 9
                                        )
                                    )
                                )
                                (
                                  .color 22
                                )
                            )
                        )
                    )
                    (
                      .split 0 5
                        (
                          .split 1 5
                            (
                              .triangle 0 1 5
                            )
                            (
                              .split 2 5
                                (
                                  .triangle 0 2 5
                                )
                                (
                                  .color 25
                                )
                            )
                        )
                        (
                          .split 3 4
                            (
                              .split 3 5
                                (
                                  .split 4 5
                                    (
                                      .triangle 3 4 5
                                    )
                                    (
                                      .split 1 3
                                        (
                                          .split 1 4
                                            (
                                              .triangle 1 3 4
                                            )
                                            (
                                              .split 1 5
                                                (
                                                  .triangle 1 3 5
                                                )
                                                (
                                                  .split 2 3
                                                    (
                                                      .split 2 4
                                                        (
                                                          .triangle 2 3 4
                                                        )
                                                        (
                                                          .color 9
                                                        )
                                                    )
                                                    (
                                                      .color 12
                                                    )
                                                )
                                            )
                                        )
                                        (
                                          .color 14
                                        )
                                    )
                                )
                                (
                                  .split 1 4
                                    (
                                      .split 1 3
                                        (
                                          .triangle 1 3 4
                                        )
                                        (
                                          .split 4 5
                                            (
                                              .split 1 5
                                                (
                                                  .triangle 1 4 5
                                                )
                                                (
                                                  .split 2 4
                                                    (
                                                      .split 2 3
                                                        (
                                                          .triangle 2 3 4
                                                        )
                                                        (
                                                          .color 14
                                                        )
                                                    )
                                                    (
                                                      .color 20
                                                    )
                                                )
                                            )
                                            (
                                              .color 6
                                            )
                                        )
                                    )
                                    (
                                      .color 22
                                    )
                                )
                            )
                            (
                              .split 1 5
                                (
                                  .split 3 5
                                    (
                                      .split 1 3
                                        (
                                          .triangle 1 3 5
                                        )
                                        (
                                          .split 4 5
                                            (
                                              .split 1 4
                                                (
                                                  .triangle 1 4 5
                                                )
                                                (
                                                  .split 2 5
                                                    (
                                                      .split 2 3
                                                        (
                                                          .triangle 2 3 5
                                                        )
                                                        (
                                                          .color 14
                                                        )
                                                    )
                                                    (
                                                      .color 25
                                                    )
                                                )
                                            )
                                            (
                                              .color 6
                                            )
                                        )
                                    )
                                    (
                                      .color 6
                                    )
                                )
                                (
                                  .color 25
                                )
                            )
                        )
                    )
                )
            )
        )
        (
          .split 1 3
            (
              .split 0 3
                (
                  .triangle 0 1 3
                )
                (
                  .split 1 4
                    (
                      .split 3 4
                        (
                          .triangle 1 3 4
                        )
                        (
                          .split 0 4
                            (
                              .triangle 0 1 4
                            )
                            (
                              .split 1 5
                                (
                                  .split 3 5
                                    (
                                      .triangle 1 3 5
                                    )
                                    (
                                      .split 4 5
                                        (
                                          .triangle 1 4 5
                                        )
                                        (
                                          .split 0 5
                                            (
                                              .triangle 0 1 5
                                            )
                                            (
                                              .color 6
                                            )
                                        )
                                    )
                                )
                                (
                                  .split 1 2
                                    (
                                      .split 2 3
                                        (
                                          .triangle 1 2 3
                                        )
                                        (
                                          .color 29
                                        )
                                    )
                                    (
                                      .color 25
                                    )
                                )
                            )
                        )
                    )
                    (
                      .split 1 5
                        (
                          .split 3 5
                            (
                              .triangle 1 3 5
                            )
                            (
                              .split 0 5
                                (
                                  .triangle 0 1 5
                                )
                                (
                                  .split 1 2
                                    (
                                      .split 2 3
                                        (
                                          .triangle 1 2 3
                                        )
                                        (
                                          .color 18
                                        )
                                    )
                                    (
                                      .color 22
                                    )
                                )
                            )
                        )
                        (
                          .split 2 3
                            (
                              .split 1 2
                                (
                                  .triangle 1 2 3
                                )
                                (
                                  .split 2 4
                                    (
                                      .split 3 4
                                        (
                                          .triangle 2 3 4
                                        )
                                        (
                                          .split 2 5
                                            (
                                              .split 4 5
                                                (
                                                  .triangle 2 4 5
                                                )
                                                (
                                                  .color 13
                                                )
                                            )
                                            (
                                              .color 25
                                            )
                                        )
                                    )
                                    (
                                      .split 3 5
                                        (
                                          .split 2 5
                                            (
                                              .triangle 2 3 5
                                            )
                                            (
                                              .color 9
                                            )
                                        )
                                        (
                                          .color 22
                                        )
                                    )
                                )
                            )
                            (
                              .color 13
                            )
                        )
                    )
                )
            )
            (
              .split 0 4
                (
                  .split 1 4
                    (
                      .triangle 0 1 4
                    )
                    (
                      .split 0 5
                        (
                          .split 4 5
                            (
                              .triangle 0 4 5
                            )
                            (
                              .split 1 5
                                (
                                  .triangle 0 1 5
                                )
                                (
                                  .split 0 3
                                    (
                                      .split 3 4
                                        (
                                          .triangle 0 3 4
                                        )
                                        (
                                          .color 5
                                        )
                                    )
                                    (
                                      .color 13
                                    )
                                )
                            )
                        )
                        (
                          .split 3 4
                            (
                              .split 0 3
                                (
                                  .triangle 0 3 4
                                )
                                (
                                  .split 2 3
                                    (
                                      .split 2 4
                                        (
                                          .triangle 2 3 4
                                        )
                                        (
                                          .split 3 5
                                            (
                                              .split 2 5
                                                (
                                                  .triangle 2 3 5
                                                )
                                                (
                                                  .color 26
                                                )
                                            )
                                            (
                                              .color 22
                                            )
                                        )
                                    )
                                    (
                                      .split 4 5
                                        (
                                          .split 3 5
                                            (
                                              .triangle 3 4 5
                                            )
                                            (
                                              .color 18
                                            )
                                        )
                                        (
                                          .color 13
                                        )
                                    )
                                )
                            )
                            (
                              .color 26
                            )
                        )
                    )
                )
                (
                  .split 1 5
                    (
                      .split 0 5
                        (
                          .triangle 0 1 5
                        )
                        (
                          .split 2 5
                            (
                              .split 1 2
                                (
                                  .triangle 1 2 5
                                )
                                (
                                  .split 4 5
                                    (
                                      .split 2 4
                                        (
                                          .triangle 2 4 5
                                        )
                                        (
                                          .split 1 4
                                            (
                                              .triangle 1 4 5
                                            )
                                            (
                                              .split 3 5
                                                (
                                                  .split 2 3
                                                    (
                                                      .triangle 2 3 5
                                                    )
                                                    (
                                                      .color 14
                                                    )
                                                )
                                                (
                                                  .color 21
                                                )
                                            )
                                        )
                                    )
                                    (
                                      .color 14
                                    )
                                )
                            )
                            (
                              .split 1 4
                                (
                                  .split 4 5
                                    (
                                      .triangle 1 4 5
                                    )
                                    (
                                      .color 10
                                    )
                                )
                                (
                                  .color 26
                                )
                            )
                        )
                    )
                    (
                      .split 2 4
                        (
                          .split 2 3
                            (
                              .split 3 4
                                (
                                  .triangle 2 3 4
                                )
                                (
                                  .split 2 5
                                    (
                                      .split 3 5
                                        (
                                          .triangle 2 3 5
                                        )
                                        (
                                          .color 21
                                        )
                                    )
                                    (
                                      .split 1 2
                                        (
                                          .split 1 4
                                            (
                                              .triangle 1 2 4
                                            )
                                            (
                                              .color 26
                                            )
                                        )
                                        (
                                          .color 25
                                        )
                                    )
                                )
                            )
                            (
                              .split 4 5
                                (
                                  .split 2 5
                                    (
                                      .triangle 2 4 5
                                    )
                                    (
                                      .split 3 5
                                        (
                                          .split 3 4
                                            (
                                              .triangle 3 4 5
                                            )
                                            (
                                              .split 0 3
                                                (
                                                  .split 0 5
                                                    (
                                                      .triangle 0 3 5
                                                    )
                                                    (
                                                      .color 26
                                                    )
                                                )
                                                (
                                                  .color 25
                                                )
                                            )
                                        )
                                        (
                                          .color 17
                                        )
                                    )
                                )
                                (
                                  .split 1 2
                                    (
                                      .split 1 4
                                        (
                                          .triangle 1 2 4
                                        )
                                        (
                                          .color 13
                                        )
                                    )
                                    (
                                      .color 14
                                    )
                                )
                            )
                        )
                        (
                          .color 21
                        )
                    )
                )
            )
        )
    )
    (
      .split 2 3
        (
          .split 2 4
            (
              .split 3 4
                (
                  .triangle 2 3 4
                )
                (
                  .split 2 5
                    (
                      .split 3 5
                        (
                          .triangle 2 3 5
                        )
                        (
                          .split 4 5
                            (
                              .triangle 2 4 5
                            )
                            (
                              .split 0 2
                                (
                                  .split 0 3
                                    (
                                      .triangle 0 2 3
                                    )
                                    (
                                      .split 0 4
                                        (
                                          .triangle 0 2 4
                                        )
                                        (
                                          .split 0 5
                                            (
                                              .triangle 0 2 5
                                            )
                                            (
                                              .color 6
                                            )
                                        )
                                    )
                                )
                                (
                                  .color 7
                                )
                            )
                        )
                    )
                    (
                      .split 0 2
                        (
                          .split 0 3
                            (
                              .triangle 0 2 3
                            )
                            (
                              .split 0 4
                                (
                                  .triangle 0 2 4
                                )
                                (
                                  .split 1 2
                                    (
                                      .split 1 3
                                        (
                                          .triangle 1 2 3
                                        )
                                        (
                                          .color 27
                                        )
                                    )
                                    (
                                      .color 25
                                    )
                                )
                            )
                        )
                        (
                          .split 1 2
                            (
                              .split 1 3
                                (
                                  .triangle 1 2 3
                                )
                                (
                                  .split 1 4
                                    (
                                      .triangle 1 2 4
                                    )
                                    (
                                      .color 26
                                    )
                                )
                            )
                            (
                              .split 0 5
                                (
                                  .split 3 5
                                    (
                                      .split 0 3
                                        (
                                          .triangle 0 3 5
                                        )
                                        (
                                          .split 1 5
                                            (
                                              .split 1 3
                                                (
                                                  .triangle 1 3 5
                                                )
                                                (
                                                  .split 4 5
                                                    (
                                                      .split 0 4
                                                        (
                                                          .triangle 0 4 5
                                                        )
                                                        (
                                                          .color 25
                                                        )
                                                    )
                                                    (
                                                      .color 7
                                                    )
                                                )
                                            )
                                            (
                                              .color 24
                                            )
                                        )
                                    )
                                    (
                                      .color 7
                                    )
                                )
                                (
                                  .color 24
                                )
                            )
                        )
                    )
                )
            )
            (
              .split 3 5
                (
                  .split 2 5
                    (
                      .triangle 2 3 5
                    )
                    (
                      .split 0 3
                        (
                          .split 0 5
                            (
                              .triangle 0 3 5
                            )
                            (
                              .split 0 2
                                (
                                  .triangle 0 2 3
                                )
                                (
                                  .split 1 3
                                    (
                                      .split 1 5
                                        (
                                          .triangle 1 3 5
                                        )
                                        (
                                          .split 1 2
                                            (
                                              .triangle 1 2 3
                                            )
                                            (
                                              .color 24
                                            )
                                        )
                                    )
                                    (
                                      .split 3 4
                                        (
                                          .split 4 5
                                            (
                                              .triangle 3 4 5
                                            )
                                            (
                                              .color 10
                                            )
                                        )
                                        (
                                          .color 26
                                        )
                                    )
                                )
                            )
                        )
                        (
                          .split 1 3
                            (
                              .split 1 5
                                (
                                  .triangle 1 3 5
                                )
                                (
                                  .split 1 2
                                    (
                                      .triangle 1 2 3
                                    )
                                    (
                                      .split 3 4
                                        (
                                          .split 4 5
                                            (
                                              .triangle 3 4 5
                                            )
                                            (
                                              .color 9
                                            )
                                        )
                                        (
                                          .color 25
                                        )
                                    )
                                )
                            )
                            (
                              .color 11
                            )
                        )
                    )
                )
                (
                  .split 0 2
                    (
                      .split 0 3
                        (
                          .triangle 0 2 3
                        )
                        (
                          .split 0 5
                            (
                              .split 2 5
                                (
                                  .triangle 0 2 5
                                )
                                (
                                  .split 1 3
                                    (
                                      .split 1 2
                                        (
                                          .triangle 1 2 3
                                        )
                                        (
                                          .split 1 4
                                            (
                                              .split 3 4
                                                (
                                                  .triangle 1 3 4
                                                )
                                                (
                                                  .split 4 5
                                                    (
                                                      .split 0 4
                                                        (
                                                          .triangle 0 4 5
                                                        )
                                                        (
                                                          .color 25
                                                        )
                                                    )
                                                    (
                                                      .color 3
                                                    )
                                                )
                                            )
                                            (
                                              .color 22
                                            )
                                        )
                                    )
                                    (
                                      .color 11
                                    )
                                )
                            )
                            (
                              .split 1 2
                                (
                                  .split 1 3
                                    (
                                      .triangle 1 2 3
                                    )
                                    (
                                      .color 20
                                    )
                                )
                                (
                                  .color 22
                                )
                            )
                        )
                    )
                    (
                      .split 1 2
                        (
                          .split 1 3
                            (
                              .triangle 1 2 3
                            )
                            (
                              .split 1 5
                                (
                                  .split 2 5
                                    (
                                      .triangle 1 2 5
                                    )
                                    (
                                      .split 4 5
                                        (
                                          .split 1 4
                                            (
                                              .triangle 1 4 5
                                            )
                                            (
                                              .split 0 4
                                                (
                                                  .split 0 5
                                                    (
                                                      .triangle 0 4 5
                                                    )
                                                    (
                                                      .color 26
                                                    )
                                                )
                                                (
                                                  .color 19
                                                )
                                            )
                                        )
                                        (
                                          .color 11
                                        )
                                    )
                                )
                                (
                                  .color 21
                                )
                            )
                        )
                        (
                          .split 0 4
                            (
                              .split 3 4
                                (
                                  .split 0 3
                                    (
                                      .triangle 0 3 4
                                    )
                                    (
                                      .split 1 4
                                        (
                                          .split 1 3
                                            (
                                              .triangle 1 3 4
                                            )
                                            (
                                              .split 4 5
                                                (
                                                  .split 0 5
                                                    (
                                                      .triangle 0 4 5
                                                    )
                                                    (
                                                      .color 20
                                                    )
                                                )
                                                (
                                                  .color 7
                                                )
                                            )
                                        )
                                        (
                                          .color 22
                                        )
                                    )
                                )
                                (
                                  .color 7
                                )
                            )
                            (
                              .color 23
                            )
                        )
                    )
                )
            )
        )
        (
          .split 4 5
            (
              .split 0 4
                (
                  .split 0 5
                    (
                      .triangle 0 4 5
                    )
                    (
                      .split 2 4
                        (
                          .split 2 5
                            (
                              .triangle 2 4 5
                            )
                            (
                              .split 0 2
                                (
                                  .triangle 0 2 4
                                )
                                (
                                  .split 1 4
                                    (
                                      .split 1 5
                                        (
                                          .triangle 1 4 5
                                        )
                                        (
                                          .split 1 2
                                            (
                                              .triangle 1 2 4
                                            )
                                            (
                                              .color 24
                                            )
                                        )
                                    )
                                    (
                                      .split 3 4
                                        (
                                          .split 3 5
                                            (
                                              .triangle 3 4 5
                                            )
                                            (
                                              .color 18
                                            )
                                        )
                                        (
                                          .color 26
                                        )
                                    )
                                )
                            )
                        )
                        (
                          .split 3 4
                            (
                              .split 3 5
                                (
                                  .triangle 3 4 5
                                )
                                (
                                  .split 0 3
                                    (
                                      .triangle 0 3 4
                                    )
                                    (
                                      .split 1 4
                                        (
                                          .split 1 5
                                            (
                                              .triangle 1 4 5
                                            )
                                            (
                                              .color 20
                                            )
                                        )
                                        (
                                          .color 22
                                        )
                                    )
                                )
                            )
                            (
                              .color 28
                            )
                        )
                    )
                )
                (
                  .split 1 4
                    (
                      .split 1 5
                        (
                          .triangle 1 4 5
                        )
                        (
                          .split 2 4
                            (
                              .split 2 5
                                (
                                  .triangle 2 4 5
                                )
                                (
                                  .split 1 2
                                    (
                                      .triangle 1 2 4
                                    )
                                    (
                                      .split 3 4
                                        (
                                          .split 3 5
                                            (
                                              .triangle 3 4 5
                                            )
                                            (
                                              .color 17
                                            )
                                        )
                                        (
                                          .color 25
                                        )
                                    )
                                )
                            )
                            (
                              .split 3 4
                                (
                                  .split 3 5
                                    (
                                      .triangle 3 4 5
                                    )
                                    (
                                      .split 1 3
                                        (
                                          .triangle 1 3 4
                                        )
                                        (
                                          .color 21
                                        )
                                    )
                                )
                                (
                                  .color 28
                                )
                            )
                        )
                    )
                    (
                      .split 2 5
                        (
                          .split 2 4
                            (
                              .triangle 2 4 5
                            )
                            (
                              .split 3 5
                                (
                                  .split 3 4
                                    (
                                      .triangle 3 4 5
                                    )
                                    (
                                      .split 0 5
                                        (
                                          .split 0 2
                                            (
                                              .triangle 0 2 5
                                            )
                                            (
                                              .split 0 3
                                                (
                                                  .triangle 0 3 5
                                                )
                                                (
                                                  .color 29
                                                )
                                            )
                                        )
                                        (
                                          .color 28
                                        )
                                    )
                                )
                                (
                                  .color 19
                                )
                            )
                        )
                        (
                          .color 19
                        )
                    )
                )
            )
            (
              .split 0 2
                (
                  .split 0 4
                    (
                      .split 2 4
                        (
                          .triangle 0 2 4
                        )
                        (
                          .split 0 3
                            (
                              .split 3 4
                                (
                                  .triangle 0 3 4
                                )
                                (
                                  .split 0 5
                                    (
                                      .split 2 5
                                        (
                                          .triangle 0 2 5
                                        )
                                        (
                                          .color 3
                                        )
                                    )
                                    (
                                      .color 28
                                    )
                                )
                            )
                            (
                              .split 2 5
                                (
                                  .split 0 5
                                    (
                                      .triangle 0 2 5
                                    )
                                    (
                                      .split 1 5
                                        (
                                          .split 1 2
                                            (
                                              .triangle 1 2 5
                                            )
                                            (
                                              .split 1 3
                                                (
                                                  .split 3 5
                                                    (
                                                      .triangle 1 3 5
                                                    )
                                                    (
                                                      .color 22
                                                    )
                                                )
                                                (
                                                  .color 11
                                                )
                                            )
                                        )
                                        (
                                          .color 28
                                        )
                                    )
                                )
                                (
                                  .color 11
                                )
                            )
                        )
                    )
                    (
                      .split 0 5
                        (
                          .split 2 5
                            (
                              .triangle 0 2 5
                            )
                            (
                              .split 3 5
                                (
                                  .split 0 3
                                    (
                                      .triangle 0 3 5
                                    )
                                    (
                                      .split 1 3
                                        (
                                          .split 1 5
                                            (
                                              .triangle 1 3 5
                                            )
                                            (
                                              .split 1 4
                                                (
                                                  .split 3 4
                                                    (
                                                      .triangle 1 3 4
                                                    )
                                                    (
                                                      .color 25
                                                    )
                                                )
                                                (
                                                  .color 12
                                                )
                                            )
                                        )
                                        (
                                          .color 11
                                        )
                                    )
                                )
                                (
                                  .color 19
                                )
                            )
                        )
                        (
                          .split 1 2
                            (
                              .split 1 4
                                (
                                  .split 2 4
                                    (
                                      .triangle 1 2 4
                                    )
                                    (
                                      .split 1 5
                                        (
                                          .split 2 5
                                            (
                                              .triangle 1 2 5
                                            )
                                            (
                                              .split 1 3
                                                (
                                                  .split 3 4
                                                    (
                                                      .triangle 1 3 4
                                                    )
                                                    (
                                                      .color 3
                                                    )
                                                )
                                                (
                                                  .color 10
                                                )
                                            )
                                        )
                                        (
                                          .color 12
                                        )
                                    )
                                )
                                (
                                  .color 12
                                )
                            )
                            (
                              .color 14
                            )
                        )
                    )
                )
                (
                  .split 0 3
                    (
                      .split 3 4
                        (
                          .split 0 4
                            (
                              .triangle 0 3 4
                            )
                            (
                              .split 1 3
                                (
                                  .split 1 4
                                    (
                                      .triangle 1 3 4
                                    )
                                    (
                                      .split 3 5
                                        (
                                          .split 1 5
                                            (
                                              .triangle 1 3 5
                                            )
                                            (
                                              .color 12
                                            )
                                        )
                                        (
                                          .color 19
                                        )
                                    )
                                )
                                (
                                  .split 0 5
                                    (
                                      .split 3 5
                                        (
                                          .triangle 0 3 5
                                        )
                                        (
                                          .split 1 2
                                            (
                                              .split 1 4
                                                (
                                                  .split 2 4
                                                    (
                                                      .triangle 1 2 4
                                                    )
                                                    (
                                                      .color 21
                                                    )
                                                )
                                                (
                                                  .color 19
                                                )
                                            )
                                            (
                                              .color 7
                                            )
                                        )
                                    )
                                    (
                                      .color 14
                                    )
                                )
                            )
                        )
                        (
                          .split 3 5
                            (
                              .split 0 5
                                (
                                  .triangle 0 3 5
                                )
                                (
                                  .split 1 5
                                    (
                                      .split 1 3
                                        (
                                          .triangle 1 3 5
                                        )
                                        (
                                          .split 1 2
                                            (
                                              .split 2 5
                                                (
                                                  .triangle 1 2 5
                                                )
                                                (
                                                  .color 26
                                                )
                                            )
                                            (
                                              .color 7
                                            )
                                        )
                                    )
                                    (
                                      .color 28
                                    )
                                )
                            )
                            (
                              .color 7
                            )
                        )
                    )
                    (
                      .split 1 2
                        (
                          .split 1 4
                            (
                              .split 2 4
                                (
                                  .triangle 1 2 4
                                )
                                (
                                  .split 1 3
                                    (
                                      .split 3 4
                                        (
                                          .triangle 1 3 4
                                        )
                                        (
                                          .split 1 5
                                            (
                                              .split 2 5
                                                (
                                                  .triangle 1 2 5
                                                )
                                                (
                                                  .color 3
                                                )
                                            )
                                            (
                                              .color 13
                                            )
                                        )
                                    )
                                    (
                                      .color 11
                                    )
                                )
                            )
                            (
                              .color 13
                            )
                        )
                        (
                          .color 15
                        )
                    )
                )
            )
        )
    )

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem good_certificate : valid sixCertificate ∅ ∅ = true := by
  decide +kernel

private theorem near_bipartite_six (G : SimpleGraph (Fin 6)) (hG : G.CliqueFree 3) :
    ∃ f : Fin 6 → Bool, ∀ a b c d : Fin 6, a < b → c < d →
      G.Adj a b → G.Adj c d → f a = f b → f c = f d → (a,b) = (c,d) :=
  valid_sound G hG sixCertificate ∅ ∅ good_certificate (by simp) (by simp)

theorem link_coloring (k : ℕ) (L : SimpleGraph (Fin k)) (hk : k ≤ 6) (hL : L.CliqueFree 3)
    (c : Fin k → Fin k → Bool) (hs : ∀ x y, c x y = c y x) :
    ∃ d : Fin k → Bool, ∀ x y, L.Adj x y → ¬ (d x = c x y ∧ d y = c x y) := by
  let e : Fin k ↪ Fin 6 := Fin.castLEEmb hk
  let G := L.map e
  have hG : G.CliqueFree 3 := by
    intro S hS
    obtain ⟨T,hT,-⟩ := (isNClique_map_iff (by decide : 1 < 3)).mp hS
    exact hL T hT
  obtain ⟨label,hlabel⟩ := near_bipartite_six G hG
  let d (x : Fin k) := label (e x)
  have hUnique {a b x y : Fin k} (hab : a < b) (hxy : x < y)
      (hAB : L.Adj a b) (hXY : L.Adj x y) (h₁ : d a = d b) (h₂ : d x = d y) :
      (a,b) = (x,y) := by
    have h := hlabel (e a) (e b) (e x) (e y) hab hxy
      (map_adj_apply.mpr hAB) (map_adj_apply.mpr hXY) h₁ h₂
    exact Prod.ext (e.injective (congrArg Prod.fst h)) (e.injective (congrArg Prod.snd h))
  have sufficient (f : Fin k → Bool) (hf : ∀ x y, x < y → L.Adj x y →
      ¬ (f x = c x y ∧ f y = c x y)) :
      ∀ x y, L.Adj x y → ¬ (f x = c x y ∧ f y = c x y) := by
    intro x y hxy h
    rcases lt_or_gt_of_ne hxy.ne with hlt|hlt
    · exact hf x y hlt hxy h
    · exact hf y x hlt hxy.symm ⟨h.2.trans (hs x y), h.1.trans (hs x y)⟩
  by_cases hBad : ∃ a b : Fin k, a < b ∧ L.Adj a b ∧ d a = d b
  swap
  · refine ⟨d,sufficient d (fun x y hxy hAd ⟨hx,hy⟩ => ?_)⟩
    exact hBad ⟨x,y,hxy,hAd,hx.trans hy.symm⟩
  obtain ⟨a,b,hab,hAB,hd⟩ := hBad
  by_cases hz : d a = c a b
  · refine ⟨fun x => !d x,sufficient _ ?_⟩
    intro x y hxy hAd ⟨hx,hy⟩
    have heq : d x = d y := Bool.not_inj (hx.trans hy.symm)
    have hp := hUnique hab hxy hAB hAd hd heq
    have hxa : x = a := (Prod.mk.inj hp).1.symm
    have hyb : y = b := (Prod.mk.inj hp).2.symm
    subst x
    subst y
    rw [← hz] at hx
    exact (Bool.not_eq_self _).mp hx
  · refine ⟨d,sufficient _ ?_⟩
    intro x y hxy hAd ⟨hx,hy⟩
    have hp := hUnique hab hxy hAB hAd hd (hx.trans hy.symm)
    have hxa : x = a := (Prod.mk.inj hp).1.symm
    have hyb : y = b := (Prod.mk.inj hp).2.symm
    subst x
    subst y
    exact hz hx

end OMA.SmallTriangleFree


theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1.H2 :=
  OMA.SmallTriangleFree.link_coloring
