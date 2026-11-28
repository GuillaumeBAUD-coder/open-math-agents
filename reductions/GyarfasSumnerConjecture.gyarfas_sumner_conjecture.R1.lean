import FormalConjectures.Wikipedia.GyarfasSumnerConjecture

-- Reduction GyarfasSumnerConjecture.gyarfas_sumner_conjecture.R1 of The Gyárfás–Sumner conjecture (Gyárfás 1975, Sumner 1981).
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: split the forbidden tree T by its shape.
--   H1: T has radius at most 2. Known (Kierstead-Penrice 1994); this is exactly the solved
--       companion variants.radius_two of the upstream file.
--   H2: every vertex of T has degree at most 2, i.e. T is a path. Known (Gyarfas 1987, the
--       companion variants.path, stated there for pathGraph n; here for trees of max degree 2,
--       which are isomorphic to paths).
--   H3: T has radius at least 3 and a vertex of degree at least 3: the open core of the
--       conjecture.
-- main: case split on the radius condition, then on the existence of a vertex of degree >= 3.

open GyarfasSumnerConjecture

namespace OMA.R_GyarfasSumnerConjecture_gyarfas_sumner_conjecture_R1

/-- Trees of radius at most two (Kierstead–Penrice). -/
def H1 : Prop :=
  ∀ {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj],
    T.IsTree → (∃ c : W, ∀ w : W, T.dist c w ≤ 2) → ∃ f : ℕ → ℕ, IsChiBoundedBy T f

/-- Trees of maximum degree at most two, i.e. paths (Gyárfás). -/
def H2 : Prop :=
  ∀ {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj],
    T.IsTree → (∀ w : W, T.degree w ≤ 2) → ∃ f : ℕ → ℕ, IsChiBoundedBy T f

/-- Trees of radius at least three with a vertex of degree at least three (open). -/
def H3 : Prop :=
  ∀ {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj],
    T.IsTree → (¬ ∃ c : W, ∀ w : W, T.dist c w ≤ 2) → (∃ w : W, 3 ≤ T.degree w) →
      ∃ f : ℕ → ℕ, IsChiBoundedBy T f

theorem main : H1 → H2 → H3 →
    type_of% @GyarfasSumnerConjecture.gyarfas_sumner_conjecture := by
  intro h1 h2 h3 W _ _ T _ hT
  by_cases hr : ∃ c : W, ∀ w : W, T.dist c w ≤ 2
  · exact h1 T hT hr
  · by_cases hd : ∃ w : W, 3 ≤ T.degree w
    · exact h3 T hT hr hd
    · push_neg at hd
      exact h2 T hT (fun w => by have := hd w; omega)

end OMA.R_GyarfasSumnerConjecture_gyarfas_sumner_conjecture_R1
