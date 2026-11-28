import OMAReductions.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1

/-! Reduction of the even case (k >= 8) of Dean's conjecture (Luo-Ma-Zhao 2026)
to the Chiba-Ota-Yamashita (2023) rooted admissible-path theorem for all k >= 5 (H1)
and the Luo-Ma-Zhao conditional even-cycle theorem given that rooted-path theorem (H2). -/

namespace OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1_H2_R1

open SimpleGraph

/-- Chiba-Ota-Yamashita (2023) rooted admissible-path theorem for every k >= 5. -/
def H1 : Prop :=
  ∀ (k : ℕ), 5 ≤ k →
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V),
      x ≠ y → 4 ≤ Fintype.card V →
      (H ⊔ SimpleGraph.fromEdgeSet {s(x, y)}).Connected →
      (∀ r : V, ((H ⊔ SimpleGraph.fromEdgeSet {s(x, y)}).induce {v | v ≠ r}).Connected) →
      (∀ u v : V, u ≠ x → u ≠ y → v ≠ x → v ≠ y → u ≠ v → k ≤ H.degree u ∨ k ≤ H.degree v) →
      ∃ a d : ℕ, (d = 1 ∨ d = 2) ∧ ∀ i < k - 1, ∃ p : H.Walk x y, p.IsPath ∧ p.length = a + d * i

/-- Luo-Ma-Zhao (2026) even case (k >= 8) conditional on the rooted admissible-path theorem. -/
def H2 : Prop :=
  (∀ (k : ℕ), 5 ≤ k →
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V),
      x ≠ y → 4 ≤ Fintype.card V →
      (H ⊔ SimpleGraph.fromEdgeSet {s(x, y)}).Connected →
      (∀ r : V, ((H ⊔ SimpleGraph.fromEdgeSet {s(x, y)}).induce {v | v ≠ r}).Connected) →
      (∀ u v : V, u ≠ x → u ≠ y → v ≠ x → v ≠ y → u ≠ v → k ≤ H.degree u ∨ k ≤ H.degree v) →
      ∃ a d : ℕ, (d = 1 ∨ d = 2) ∧ ∀ i < k - 1, ∃ p : H.Walk x y, p.IsPath ∧ p.length = a + d * i) →
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ},
    8 ≤ k → Even k → ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → k ≤ G.minDegree → ∃ m ∈ G.cycleLengths, k ∣ m

theorem main : H1 → H2 →
    OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1.H2 :=
  fun h1 h2 => h2 h1

end OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1_H2_R1
