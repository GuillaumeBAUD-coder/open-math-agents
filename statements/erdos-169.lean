import Mathlib

/-!
# Erdős Problem 169

Source: https://www.erdosproblems.com/169
Credit: @joshuadc11

Let `k ≥ 3` and `f(k)` be the supremum of `∑_{n ∈ A} 1/n` as `A` ranges over all sets of positive
integers which do not contain a `k`-term arithmetic progression. Is
`lim_{k → ∞} f(k) / log W(k) = ∞`, where `W(k)` is the (2-color) van der Waerden number?

Formalization notes:
- `f(k)` is taken in `ℝ≥0∞` (`ENNReal`) so the supremum and harmonic sums are well-defined without
  assuming finiteness of `f(k)` (which is itself equivalent to Erdős Problem 3).
- `vanDerWaerden k` is the 2-color van der Waerden number `W(2, k)`: the least `N` such that every
  2-coloring of `{1, ..., N}` contains a monochromatic `k`-term arithmetic progression.
- Convergence to `∞` is expressed as `Filter.Tendsto ... Filter.atTop (nhds ⊤)` in `ENNReal`.
-/

namespace OMA.S_erdos_169

/-- A set of natural numbers contains a non-trivial `k`-term arithmetic progression. -/
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- The 2-color van der Waerden number `W(k)`: the least `N` such that every 2-coloring
of `{1, ..., N}` contains a monochromatic `k`-term arithmetic progression. -/
noncomputable def vanDerWaerden (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ c : ℕ → Bool, ∃ b : Bool,
    HasAP {n : ℕ | 1 ≤ n ∧ n ≤ N ∧ c n = b} k}

/-- `f k` is the supremum of `∑_{n ∈ A} 1 / n` over all sets `A` of positive integers
containing no `k`-term arithmetic progression. -/
noncomputable def f (k : ℕ) : ENNReal :=
  sSup {s : ENNReal | ∃ A : Set ℕ, (∀ n ∈ A, 0 < n) ∧ ¬ HasAP A k ∧
    s = ∑' n : A, ((n : ℕ) : ENNReal)⁻¹}

theorem main :
    Filter.Tendsto
      (fun k : ℕ => f k / ENNReal.ofReal (Real.log (vanDerWaerden k)))
      Filter.atTop (nhds ⊤) := by
  sorry

end OMA.S_erdos_169
