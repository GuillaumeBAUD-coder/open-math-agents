import Mathlib

/-!
# Euler's constant

Source: https://en.wikipedia.org/wiki/Euler's_constant
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source (Wikipedia, "Euler's constant"): γ is the limiting difference between the harmonic
series and the natural logarithm,
γ = limₙ (Σ_{k=1}^n 1/k − log n),
and the page records its rationality as "Unknown" — it is a classical open problem whether γ
is irrational (indeed whether it is irrational is not even known).

Mathlib's `Real.eulerMascheroniConstant` is this constant (Mathlib/NumberTheory/Harmonic/GammaDeriv.lean
characterizes it by γ = −Γ'(1), the standard analytic characterization of the same constant).
-/

namespace OMA.S_wp_euler_s_constant

/--
Euler's constant is irrational — the open question of the source, stated as the expected answer.
-/
theorem main : Irrational Real.eulerMascheroniConstant := by
  sorry

end OMA.S_wp_euler_s_constant
