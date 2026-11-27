import Mathlib

namespace A257104

/-- The unique first-return representation of a Motzkin excursion.
The constructors represent the empty word, H followed by a tail,
and U followed by an interior, D and a tail, respectively. -/
inductive Excursion where
  | empty
  | horizontal (tail : Excursion)
  | arch (interior tail : Excursion)
  deriving DecidableEq

/-- All length-`n` excursions based at height `h`. State 3 means any base
height at least three. An empty arch interior is forbidden precisely at
base height two, where it would create a peak at height three. -/
def paths (n h : ℕ) : List Excursion :=
  match n with
  | 0 => [.empty]
  | 1 => [.horizontal .empty]
  | k + 2 =>
    (paths (k+1) h).map .horizontal ++
      (List.ofFn fun i : Fin (k+1) =>
        if h = 2 ∧ i.val = 0 then [] else
          (((paths i.val (min (h+1) 3)).product (paths (k-i.val) h)).map
            fun p => Excursion.arch p.1 p.2)).flatten
termination_by n
decreasing_by all_goals omega

/-- The number of length-`n` ground-based Motzkin excursions with no peak
at height three. -/
def pathCount (n : ℕ) : ℕ := (paths n 0).length

noncomputable def seriesAt (h : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((paths n h).length : ℚ)

end A257104

namespace OMA.S_oeis_a257104

open A257104

/-- A rational power series is D-finite if it satisfies a homogeneous linear
differential equation over the rational polynomials with nonzero leading coefficient. -/
def DFinite (f : PowerSeries ℚ) : Prop :=
  ∃ (k : ℕ) (p : Fin (k+1) → Polynomial ℚ), p (Fin.last k) ≠ 0 ∧
    ∑ i, (p i : PowerSeries ℚ) * ((PowerSeries.derivative ℚ)^[i.val]) f = 0

/-- The path count is coerced before any signed arithmetic. -/
def a (n : ℕ) : ℚ := pathCount n

/-- R. J. Mathar's conjecture for OEIS A257104. At length six the residual is three. -/
theorem main :
    DFinite (seriesAt 0) ∧
    (∀ n : ℕ, 7 ≤ n →
      (2-(n : ℚ)) * a n + (7*(n : ℚ)-17) * a (n-1) + (34-14*(n : ℚ)) * a (n-2)
        + ((n : ℚ)+22) * a (n-3) + (16*(n : ℚ)-89) * a (n-4)
        + (23-4*(n : ℚ)) * a (n-5) + 3*((n : ℚ)-5) * a (n-6) = 0) := by
  sorry

end OMA.S_oeis_a257104
