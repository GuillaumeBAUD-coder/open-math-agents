import OMAStatements.S_arxiv_1809_10088

-- Reduction arxiv-1809.10088.R1 of arxiv-1809.10088: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_arxiv_1809_10088_R1

open OMA.S_arxiv_1809_10088

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
      (c : Sym2 V → Fin k),
      Fintype.card V ^ 2 + 2 * Finset.univ.sup (classSize G c) < 4 * G.edgeFinset.card →
      HasNonMonoTriangle G c)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
      (c : Sym2 V → Fin k), 1 ≤ k →
      (∀ i, Fintype.card V ^ 2 < (4 * k - 2) * classSize G c i) →
      HasNonMonoTriangle G c)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_arxiv_1809_10088.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_arxiv_1809_10088_R1
