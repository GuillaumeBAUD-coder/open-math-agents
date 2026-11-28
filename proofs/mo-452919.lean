import OMAStatements.S_mo_452919
import Mathlib

/-!
# MathOverflow 452919: a digraph with every edge on a cycle and a non-diagonalizable adjacency matrix

The answer to the question is negative. The counterexample is the one given on the source page by
Benjamin Steinberg (https://mathoverflow.net/a/452979): the digraph on four vertices with edges
0 → 1, 0 → 3, 1 → 2, 2 → 1, 2 → 3, 3 → 0. It is strongly connected, so every edge lies on a cycle.
Its adjacency matrix sends `x = (-1, 0, 1, 0)` to `y = (0, 1, 0, -1)` and sends `y` to zero.
If `z` and `t` are the coordinates of `x` and `y` in a diagonalizing basis, then
`tᵢ = dᵢ * zᵢ` and `dᵢ * tᵢ = 0`. Thus every coordinate of `y` would be zero.
-/

namespace MO452919

open Matrix

/-- The adjacency matrix of the counterexample, with integer entries. -/
def M : Matrix (Fin 4) (Fin 4) ℤ := !![0, 1, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 0, 0]

/-- The counterexample digraph. -/
def G : Digraph (Fin 4) := ⟨fun i j => M i j = 1⟩

instance decAdj : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (M i j = 1))

/-- For each edge `u → v`, a directed path from `v` back to `u` through distinct vertices. -/
def pth : Fin 4 → Fin 4 → List (Fin 4)
  | 0, 1 => [1, 2, 3, 0]
  | 0, 3 => [3, 0]
  | 1, 2 => [2, 1]
  | 2, 1 => [1, 2]
  | 2, 3 => [3, 0, 1, 2]
  | 3, 0 => [0, 3]
  | _, _ => []

theorem edges : ∀ u v : Fin 4, G.Adj u v → OMA.S_mo_452919.EdgeOnCycle G u v := by
  intro u v h
  refine ⟨pth u v, ?_⟩
  revert u v
  decide

theorem not_diag [DecidableRel G.Adj] (P : Matrix (Fin 4) (Fin 4) ℂ) (d : Fin 4 → ℂ)
    (hP : IsUnit P.det)
    (h : OMA.S_mo_452919.adjMatrix G * P = P * Matrix.diagonal d) : False := by
  let A := OMA.S_mo_452919.adjMatrix G
  let x : Fin 4 → ℂ := ![-1, 0, 1, 0]
  let y : Fin 4 → ℂ := ![0, 1, 0, -1]
  have ⟨hx, hy⟩ : A *ᵥ x = y ∧ A *ᵥ y = 0 := by
    constructor <;> funext i <;> fin_cases i <;>
      norm_num [A, OMA.S_mo_452919.adjMatrix, G, M, x, y, mulVec, dotProduct,
        Fin.sum_univ_four, cons_val_two, cons_val_three]
  have hmap (v : Fin 4 → ℂ) : A *ᵥ (P *ᵥ v) = P *ᵥ (fun i => d i * v i) := by
    change A * P = P * Matrix.diagonal d at h
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]
    exact congrArg P.mulVec (funext (Matrix.mulVec_diagonal d v))
  have hunit : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hP
  obtain ⟨z, hz⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit x
  let t : Fin 4 → ℂ := fun i => d i * z i
  have ht : P *ᵥ t = y := by
    change P *ᵥ (fun i => d i * z i) = y
    rw [← hmap, hz, hx]
  have hnull : P *ᵥ (fun i => d i * t i) = 0 := by
    rw [← hmap, ht, hy]
  have hzero : (fun i => d i * t i) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit (hnull.trans (Matrix.mulVec_zero P).symm)
  have ht0 : t = 0 := by
    funext i
    rcases mul_eq_zero.mp (congrFun hzero i) with hdi | hti
    · simp [t, hdi]
    · exact hti
  have hy0 : y = 0 := by simpa [ht0] using ht.symm
  have hy1 := congrFun hy0 (1 : Fin 4)
  norm_num [y] at hy1

end MO452919

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_452919.main) := by
  intro h
  obtain ⟨P, d, hP, hPD⟩ := h (Fin 4) MO452919.G MO452919.edges
  exact MO452919.not_diag P d hP hPD
