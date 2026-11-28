import Mathlib

namespace OMA.S_oeis_a369802

open scoped Classical

/-- In-order traversal of the 1-indexed complete binary tree on `{1, ..., n}` rooted at `k`
(producing the node indices in sorted value order of the Eytzinger array layout). -/
def eytzingerOrder (n : ℕ) (k : ℕ) : List ℕ :=
  if _h : 1 ≤ k ∧ k ≤ n then
    eytzingerOrder n (2 * k) ++ [k] ++ eytzingerOrder n (2 * k + 1)
  else
    []
termination_by n + 1 - k
decreasing_by
  all_goals simp_wf; omega

/-- Inversion count of the Eytzinger array layout of `n` elements (`A369802(n)`):
a pair `(i, j)` with `1 ≤ i < j ≤ n` is an inversion in the Eytzinger array iff node `j` appears
before node `i` in `eytzingerOrder n 1` (i.e., `j` gets a smaller sorted value than `i`). -/
def a369802 (n : ℕ) : ℕ :=
  ((eytzingerOrder n 1).tails.map fun l =>
    match l with
    | [] => 0
    | j :: rest => (rest.filter (fun i => j > i)).length).sum

/-- Number of cells turned ON at stage `k ≥ 1` in the 90-degree wedge cellular automaton
(`A261693(k)`): `2 * k - 1` if `k` is a power of `2`, else `rowON (k - 1) - 2`. -/
noncomputable def a261693 : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      if ∃ m : ℕ, k + 1 = 2 ^ m then 2 * (k + 1) - 1
      else a261693 k - 2

/-- Total number of ON cells after stage `n` in the 90-degree wedge cellular automaton
(`A261692(n)`). -/
noncomputable def a261692 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, a261693 k

/-- OEIS A369802 Conjecture: For all `n : ℕ`, `A369802(n) = (A261692(n) - n) / 2`
(equivalently `2 * A369802(n) + n = A261692(n)`). -/
theorem main :
    ∀ n : ℕ, 2 * a369802 n + n = a261692 n ∧ a369802 n = (a261692 n - n) / 2 := by
  sorry

end OMA.S_oeis_a369802
