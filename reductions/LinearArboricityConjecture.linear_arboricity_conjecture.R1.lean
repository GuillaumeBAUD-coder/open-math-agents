import FormalConjectures.Wikipedia.LinearArboricityConjecture

-- Reduction LinearArboricityConjecture.linear_arboricity_conjecture.R1 of The linear arboricity conjecture
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: split the conjecture la(G) <= (D + 2) / 2 by the maximum degree D of G.
--   H1: D <= 2. Elementary: G is a disjoint union of paths and cycles; for D <= 1 it is itself a
--       linear forest, for D = 2 remove one edge from each cycle to get two linear forests.
--   H2: 3 <= D <= 6. Known: Akiyama-Exoo-Harary (1980/81) for D = 3, 4 and Enomoto-Peroche (1984)
--       for D = 5, 6; these are not in Mathlib (the upstream file only has the cubic case).
--   H3: D >= 7. Open in general (Guldan settled D = 8, 10; Alon proved an asymptotic version).
-- Different degree ranges are independent statements, so the split separates the known cases from
-- the open core. main is a case split on G.maxDegree.

open LinearArboricityConjecture

namespace OMA.R_LinearArboricityConjecture_linear_arboricity_conjecture_R1

/-- Maximum degree at most 2. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.maxDegree ≤ 2 → linearArboricity G ≤ (G.maxDegree + 2) / 2

/-- Maximum degree between 3 and 6 (Akiyama–Exoo–Harary, Enomoto–Péroche). -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    3 ≤ G.maxDegree → G.maxDegree ≤ 6 → linearArboricity G ≤ (G.maxDegree + 2) / 2

/-- Maximum degree at least 7. -/
def H3 : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    7 ≤ G.maxDegree → linearArboricity G ≤ (G.maxDegree + 2) / 2

theorem main : H1 → H2 → H3 →
    type_of% @LinearArboricityConjecture.linear_arboricity_conjecture := by
  intro h1 h2 h3 V _ G _
  rcases (by omega : G.maxDegree ≤ 2 ∨ (3 ≤ G.maxDegree ∧ G.maxDegree ≤ 6) ∨ 7 ≤ G.maxDegree)
    with h | ⟨ha, hb⟩ | h
  · exact h1 G h
  · exact h2 G ha hb
  · exact h3 G h

end OMA.R_LinearArboricityConjecture_linear_arboricity_conjecture_R1
