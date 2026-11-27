import Mathlib

/-!
# Minimum number of arc-disjoint transitive subtournaments of order 3 in a tournament

Source: https://www.openproblemgarden.org/op/minimum_number_of_transitive_subtournaments_of_order_3_in_a_tournament
Credit: @ishaanzee

**Conjecture** (R. Yuster). If `T` is a tournament of order `n`, then it contains
`⌈n(n-1)/6 - n/3⌉` arc-disjoint transitive subtournaments of order 3.

If true the bound is tight (take three nearly equal parts `V₁ → V₂ → V₃ → V₁`).

Formalization:
* A tournament on `Fin n` is a relation `T` (`T x y` means the arc `x → y`) that is irreflexive and
  has exactly one of `x → y`, `y → x` for every pair of distinct vertices.
* A transitive subtournament of order 3 (`TT₃`) is a triple `(a, b, c)` with arcs `a → b`, `b → c`
  and `a → c`; its arc set is `{(a, b), (b, c), (a, c)}`.
* A family of `TT₃`s is arc-disjoint when the arc sets of distinct members are disjoint. The
  bound `⌈n(n-1)/6 - n/3⌉` is computed with `Int.ceil` in `ℚ`.
-/

namespace OMA.S_opg_minimum_number_of_transitive_subtournaments_of_order_3_in_a_tournament

/-- `T` is a tournament on `Fin n`. -/
def IsTournament {n : ℕ} (T : Fin n → Fin n → Prop) : Prop :=
  (∀ x, ¬ T x x) ∧ ∀ x y, x ≠ y → (T x y ↔ ¬ T y x)

/-- The triple `(a, b, c)` spans a transitive subtournament `a → b → c`, `a → c`. -/
def IsTT3 {n : ℕ} (T : Fin n → Fin n → Prop) (t : Fin n × Fin n × Fin n) : Prop :=
  T t.1 t.2.1 ∧ T t.2.1 t.2.2 ∧ T t.1 t.2.2

/-- The three arcs of the triple `(a, b, c)`. -/
def arcs {n : ℕ} (t : Fin n × Fin n × Fin n) : Finset (Fin n × Fin n) :=
  {(t.1, t.2.1), (t.2.1, t.2.2), (t.1, t.2.2)}

/-- **Yuster's conjecture**: every tournament of order `n` contains `⌈n(n-1)/6 - n/3⌉`
arc-disjoint transitive subtournaments of order 3. -/
theorem main : ∀ (n : ℕ) (T : Fin n → Fin n → Prop), IsTournament T →
    ∃ P : Finset (Fin n × Fin n × Fin n), (∀ t ∈ P, IsTT3 T t) ∧
      (P : Set (Fin n × Fin n × Fin n)).PairwiseDisjoint arcs ∧
      ⌈(n : ℚ) * (n - 1) / 6 - n / 3⌉ ≤ (P.card : ℤ) := by
  sorry

end OMA.S_opg_minimum_number_of_transitive_subtournaments_of_order_3_in_a_tournament
