import OMAReductions.R_erdos_811_R1

/-!
Proof of `OMA.R_erdos_811_R1.H1`.
Fix the colour 0 and let G be the graph of edges of colour 0. In a balanced colouring every
vertex has degree n / 6 in G. For n = 12a + 7 this is 2a + 1, so the degree sum
(12a + 7)(2a + 1) is odd, contradicting the handshake lemma (the degree sum is twice the
number of edges).
-/

namespace OMAProof.Erdos811H1

/-- The graph of the edges of colour `j`. -/
def colourGraph {n : ℕ} (c : Sym2 (Fin n) → Fin 6) (j : Fin 6) : SimpleGraph (Fin n) where
  Adj v w := v ≠ w ∧ c s(v, w) = j
  symm := ⟨fun v w h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

end OMAProof.Erdos811H1

open OMAProof.Erdos811H1 in
theorem OMA.solution : OMA.R_erdos_811_R1.H1 := by
  classical
  intro n hn c hc
  let G := colourGraph c 0
  have hdeg : ∀ v, G.degree v = n / 6 := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hc v 0]
    congr 1
    ext w
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    simp [G, colourGraph, ne_comm]
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  obtain ⟨a, rfl⟩ : ∃ a, n = 12 * a + 7 := ⟨n / 12, by omega⟩
  have hq : (12 * a + 7) / 6 = 2 * a + 1 := by omega
  rw [hq] at hsum
  have hodd : (12 * a + 7) * (2 * a + 1) = 2 * (12 * a ^ 2 + 13 * a + 3) + 1 := by ring
  omega
