import Mathlib

/-!
# OEIS A371835: lattice points in a cube intersected with an octahedron

Source: https://oeis.org/A371835
Credit: Sudharsan Rajendiran

A371835 is the triangle `T(n, k)` (`0 ≤ k ≤ n`) counting the points `(x, y, z) ∈ ℤ³` with
`|x| + |y| + |z| ≤ n` and `max(|x|, |y|, |z|) ≤ k`. Sela Fried conjectured the closed forms
`T(n,k) = (-84k^3 + 108k^2n - 72k^2 - 36kn^2 + 72kn - 6k + 4n^3 - 12n^2 + 8n + 3)/3` for
`(n-2)/3 ≤ k ≤ n/2` and `T(n,k) = (12k^3 - 36k^2n + 36kn^2 + 6k - 8n^3 + 6n^2 + 2n + 3)/3` for
`(n-1)/2 ≤ k ≤ n`; the entry records that both conjectures are true (Sela Fried, Jul 2024). We
state both (multiplied by 3, in `ℤ`), with the range conditions taken over `ℚ` as written.
-/

namespace OMA.S_oeis_a371835

/-- `T n k`: the number of points `(x, y, z) ∈ ℤ³` with `|x| + |y| + |z| ≤ n` and
`max(|x|, |y|, |z|) ≤ k` (such points lie in the box `[-n, n]³`). -/
noncomputable def T (n k : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun v : ℤ × ℤ × ℤ =>
      |v.1| + |v.2.1| + |v.2.2| ≤ n ∧ max (max |v.1| |v.2.1|) |v.2.2| ≤ k)).card

theorem main :
    (∀ n k : ℕ, ((n : ℚ) - 2) / 3 ≤ k → (k : ℚ) ≤ n / 2 →
      3 * (T n k : ℤ) = -84 * k ^ 3 + 108 * k ^ 2 * n - 72 * k ^ 2 - 36 * k * n ^ 2 + 72 * k * n
        - 6 * k + 4 * n ^ 3 - 12 * n ^ 2 + 8 * n + 3) ∧
    (∀ n k : ℕ, ((n : ℚ) - 1) / 2 ≤ k → k ≤ n →
      3 * (T n k : ℤ) = 12 * k ^ 3 - 36 * k ^ 2 * n + 36 * k * n ^ 2 + 6 * k - 8 * n ^ 3
        + 6 * n ^ 2 + 2 * n + 3) := by
  sorry

end OMA.S_oeis_a371835
