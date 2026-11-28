import Mathlib

/-!
# Is this 2x2 determinant sequence positive and increasing?

Source: https://mathoverflow.net/questions/217457 (asked in 2015 by the user Fancier of Mathematica; no answer).

`X₁, X₂, X₃` are random variables with values in the nonnegative integers, with local probabilities
`a k = P(X₁ = k)`, `b k = P(X₂ = k)`, `c k = P(X₃ = k)` and `s k = P(X₁ + X₂ + X₃ = k)`.
The source defines two sequences by recurrence,

* `α 0 = 1`, `α 1 = 0`, `α 2 = -1 / (b 0 * c 0)` and, for `n ≥ 3`,
  `α n = (1 / s 0) * (α (n - 3) - a (n - 2) - ∑_{k=1}^{n-1} s k * α (n - k))`;
* `β 0 = 0`, `β 1 = 1`, `β 2 = -c 1 / c 0 - 1 / b 0` and, for `n ≥ 3`,
  `β n = (1 / s 0) * (β (n - 3) - ∑_{k=1}^{n-1} s k * β (n - k) - a (n - 2) * c 0
    + c 0 * ∑_{k=0}^{n-1} a k * b (n - 1 - k))`;

and the determinant `D n = α n * β (n + 1) - α (n + 1) * β n`. It asks: can one show that
`D (n + 1) > D n > 0` for every `n = 0, 1, 2, …`?

Hypotheses, as in the source: `s 0 > 0` (the recurrences divide by `s 0`), and the case in which all three
variables vanish almost surely is excluded (there are then no claims at all, which the source calls not a
problem to solve).

Choices of reading.
* The three variables are independent. The source does not say this in so many words. It is the setting
  of the paper the question comes from (Grigutis, Korvel and Šiaulys, Ruin probability in the
  three-seasonal discrete-time risk model, 2015: Definition 1 and Theorem 5, where the same two sequences
  appear), and the last sum in the recurrence of `β` is the convolution of `a` and `b`.
* The source adds, as a remark based on numerical calculations, a second observation about the
  determinants built from the rows `n` and `n + 2`. It is not part of the question and is not stated here.

In the definitions below the recurrences are written for the index `n + 3`, and the sums
`∑_{k=1}^{n+2}` are indexed by `k - 1`.
-/

namespace OMA.S_mo_217457

open MeasureTheory

/-- The first recurrent sequence of the source. -/
noncomputable def alpha (a b c s : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => -(1 / (b 0 * c 0))
  | n + 3 => 1 / s 0 * (alpha a b c s n - a (n + 1) -
      ∑ k : Fin (n + 2), s (k.val + 1) * alpha a b c s (n + 2 - k.val))
termination_by n => n
decreasing_by all_goals omega

/-- The second recurrent sequence of the source. -/
noncomputable def beta (a b c s : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => -(c 1 / c 0) - 1 / b 0
  | n + 3 => 1 / s 0 * (beta a b c s n -
      ∑ k : Fin (n + 2), s (k.val + 1) * beta a b c s (n + 2 - k.val) -
      a (n + 1) * c 0 + c 0 * ∑ k ∈ Finset.range (n + 3), a k * b (n + 2 - k))
termination_by n => n
decreasing_by all_goals omega

/-- The determinant `D n` of the source. -/
noncomputable def D (a b c s : ℕ → ℝ) (n : ℕ) : ℝ :=
  alpha a b c s n * beta a b c s (n + 1) - alpha a b c s (n + 1) * beta a b c s n

theorem main : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ X₃ : Ω → ℕ), Measurable X₁ → Measurable X₂ → Measurable X₃ →
    ProbabilityTheory.iIndepFun ![X₁, X₂, X₃] P →
    0 < P.real {ω | X₁ ω + X₂ ω + X₃ ω = 0} →
    ¬ (P {ω | X₁ ω = 0} = 1 ∧ P {ω | X₂ ω = 0} = 1 ∧ P {ω | X₃ ω = 0} = 1) →
    ∀ n : ℕ,
      0 < D (fun k => P.real {ω | X₁ ω = k}) (fun k => P.real {ω | X₂ ω = k})
        (fun k => P.real {ω | X₃ ω = k}) (fun k => P.real {ω | X₁ ω + X₂ ω + X₃ ω = k}) n ∧
      D (fun k => P.real {ω | X₁ ω = k}) (fun k => P.real {ω | X₂ ω = k})
        (fun k => P.real {ω | X₃ ω = k}) (fun k => P.real {ω | X₁ ω + X₂ ω + X₃ ω = k}) n <
      D (fun k => P.real {ω | X₁ ω = k}) (fun k => P.real {ω | X₂ ω = k})
        (fun k => P.real {ω | X₃ ω = k}) (fun k => P.real {ω | X₁ ω + X₂ ω + X₃ ω = k}) (n + 1) := by
  sorry

end OMA.S_mo_217457
