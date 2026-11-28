import Mathlib

/-!
# arXiv 1803.00671: topological quandle structures on the closed unit interval

Source: https://arxiv.org/abs/1803.00671
Credit: @xor2k

Row text (On the Classification of Topological Quandles):
For the closed unit interval $[0, 1]$, we conjecture that there exists only one topological quandle
structure on it, i.e. the trivial one.

Reading choices:
* The space is `Set.Icc (0 : ℝ) 1` with the subspace topology of `ℝ`; `X × X` carries the product
  topology.
* A topological quandle structure on a topological space `X` is a binary operation
  `op x y` (written `x * y` in the paper, right-action convention) such that
  (1) `(x, y) ↦ op x y` is continuous on `X × X`,
  (2) `op x x = x` for all `x`,
  (3) for every `y`, the right multiplication `x ↦ op x y` is a homeomorphism of `X`,
  (4) `op (op x y) z = op (op x z) (op y z)` for all `x y z` (right self-distributivity).
  Some authors additionally require the inverse operation `(x, y) ↦ R_y⁻¹ x` to be jointly
  continuous. On a compact Hausdorff space such as `[0, 1]` this follows from (1) and (3), since
  `(x, y) ↦ (op x y, y)` is then a continuous bijection of the compact Hausdorff space `X × X`,
  so both readings give the same notion here.
* The trivial quandle structure is `op x y = x` for all `x y`. A structure isomorphic to the
  trivial one is itself trivial, so the claim reads: every topological quandle structure on
  `[0, 1]` is the trivial one.
-/

namespace OMA.S_arxiv_1803_00671

/-- `op` is a topological quandle structure on `X` (right-action convention). -/
def IsTopologicalQuandle {X : Type*} [TopologicalSpace X] (op : X → X → X) : Prop :=
  Continuous (fun p : X × X => op p.1 p.2) ∧
  (∀ x, op x x = x) ∧
  (∀ y, IsHomeomorph (fun x => op x y)) ∧
  (∀ x y z, op (op x y) z = op (op x z) (op y z))

/-- Conjecture: the only topological quandle structure on `[0, 1]` is the trivial one. -/
theorem main :
    ∀ op : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1,
      IsTopologicalQuandle op → ∀ x y, op x y = x := by
  sorry

end OMA.S_arxiv_1803_00671
