import FormalConjectures.Arxiv.«2507.17780».«1»

-- Reduction Arxiv.2507.17780.tx_graffiti_conjecture_1.R1 of TxGraffiti Conjecture 1: independence, annihilation, and residue
-- Credit: @zhongguojwj
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1

/-- Caro–Wei: the independence number is at least the sum over vertices of `1 / (degree + 1)`. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ∑ v, (1 : ℝ) / ((G.degree v : ℝ) + 1) ≤ (G.indepNum : ℝ)

/-- Degree-sequence form of the conjecture: the Caro–Wei bound dominates the
annihilation-residue ratio. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → 2 ≤ G.maxDegree →
      (((G.annihilationNumber : ℕ) : ℝ) + (G.residue : ℝ)) / ((G.maxDegree : ℕ) : ℝ) ≤
        ∑ v, (1 : ℝ) / ((G.degree v : ℝ) + 1)

theorem main : H1 → H2 → type_of% @Arxiv.«2507.17780».tx_graffiti_conjecture_1 := by
  intro h1 h2 V _ _ G _ hconn hdeg
  exact (h2 G hconn hdeg).trans (h1 G)

end OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1
