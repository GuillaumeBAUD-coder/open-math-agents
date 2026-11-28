import Mathlib

namespace OMA.S_arxiv_2609_28509

open scoped BigOperators Topology

/-- The finite factor (q to the step; q to the step) with n terms. -/
def qPochhammer (q : ℂ) (step n : ℕ) : ℂ :=
  ∏ j ∈ Finset.range n, (1 - q ^ (step * (j + 1)))

/-- The mixed-base rank-two sums at the nonnegative integral shifts used here. -/
noncomputable def nahm (q : ℂ) (a b : ℕ) : ℂ :=
  ∑' rs : ℕ × ℕ,
    let (r, s) := rs
    q ^ (3 * r ^ 2 + 31 * r * s + 93 * s ^ 2 + a * r + b * s) /
      (qPochhammer q 1 r * qPochhammer q 31 s)

/-- Shift zero gives the first Rogers–Ramanujan function and shift one the second. -/
noncomputable def rogersRamanujan (q : ℂ) (shift : ℕ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2 + shift * n) / qPochhammer q 1 n

/-- Conjecture 1.2 in its equivalent positive four-shift form. -/
theorem main :
    ∀ q : ℂ, ‖q‖ < 1 →
      nahm q 0 0 + q ^ 2 * nahm q 5 31 + q ^ 8 * nahm q 9 62 +
        q ^ 9 * nahm q 11 62 =
      rogersRamanujan q 1 * rogersRamanujan (q ^ 31) 0 -
        q ^ 6 * rogersRamanujan q 0 * rogersRamanujan (q ^ 31) 1 := by
  sorry

end OMA.S_arxiv_2609_28509
