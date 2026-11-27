import OMAStatements.S_mo_452919
import Mathlib

/-!
# MathOverflow 452919: a digraph with every edge on a cycle and a non-diagonalizable adjacency matrix

The answer to the question is negative. The counterexample is the one given on the source page by
Benjamin Steinberg (https://mathoverflow.net/a/452979): the digraph on four vertices with edges
0 → 1, 0 → 3, 1 → 2, 2 → 1, 2 → 3, 3 → 0. It is strongly connected, so every edge lies on a cycle.
Its adjacency matrix `M` satisfies `M ^ 4 = 2 M ^ 2` but `M ^ 3 ≠ 2 M`.

If `M P = P D` with `P` invertible and `D` diagonal, then `M ^ k P = P D ^ k` for all `k`, so
`D ^ 4 = 2 D ^ 2`. Entrywise this gives `x ^ 4 = 2 x ^ 2`, hence `x ^ 3 = 2 x`, so `D ^ 3 = 2 D`
and therefore `M ^ 3 = 2 M`, which is false.
-/

namespace MO452919

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

theorem pow_four : M ^ 4 = M ^ 2 + M ^ 2 := by decide

theorem pow_three : (M ^ 3) 1 0 ≠ (M + M) 1 0 := by decide

theorem adj_eq [DecidableRel G.Adj] :
    OMA.S_mo_452919.adjMatrix G = (Int.castRingHom ℂ).mapMatrix M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [OMA.S_mo_452919.adjMatrix, G, M]

theorem pow_mul_eq {A P D : Matrix (Fin 4) (Fin 4) ℂ} (h : A * P = P * D) (k : ℕ) :
    A ^ k * P = P * D ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]

theorem cube_of_fourth (x : ℂ) (h : x ^ 4 = x ^ 2 + x ^ 2) : x ^ 3 = x + x := by
  have h1 : x ^ 2 * (x ^ 2 - 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · have hx : x = 0 := by simpa using h2
    simp [hx]
  · linear_combination x * h2

theorem not_diag [DecidableRel G.Adj] (P : Matrix (Fin 4) (Fin 4) ℂ) (d : Fin 4 → ℂ)
    (hP : IsUnit P.det)
    (h : OMA.S_mo_452919.adjMatrix G * P = P * Matrix.diagonal d) : False := by
  rw [adj_eq] at h
  set φ := (Int.castRingHom ℂ).mapMatrix (m := Fin 4) with hφ
  set A := φ M with hA
  set D := Matrix.diagonal d with hD
  have hinvl : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hinvr : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hA4 : A ^ 4 = A ^ 2 + A ^ 2 := by
    rw [hA, ← map_pow, ← map_pow, ← map_add, pow_four]
  -- `P * D ^ 4 = P * (D ^ 2 + D ^ 2)`
  have h1 : P * D ^ 4 = P * (D ^ 2 + D ^ 2) := by
    rw [← pow_mul_eq h 4, hA4, Matrix.add_mul, pow_mul_eq h 2, Matrix.mul_add]
  have h2 : D ^ 4 = D ^ 2 + D ^ 2 := by
    calc D ^ 4 = P⁻¹ * (P * D ^ 4) := by rw [← Matrix.mul_assoc, hinvl, Matrix.one_mul]
      _ = P⁻¹ * (P * (D ^ 2 + D ^ 2)) := by rw [h1]
      _ = D ^ 2 + D ^ 2 := by rw [← Matrix.mul_assoc, hinvl, Matrix.one_mul]
  have h3 : ∀ i, d i ^ 4 = d i ^ 2 + d i ^ 2 := by
    intro i
    have := congrFun (congrFun h2 i) i
    simpa [hD, Matrix.diagonal_pow] using this
  have h4 : D ^ 3 = D + D := by
    rw [hD, Matrix.diagonal_pow, Matrix.diagonal_add]
    congr 1
    funext i
    simpa using cube_of_fourth (d i) (h3 i)
  have h5 : A ^ 3 * P = (A + A) * P := by
    rw [pow_mul_eq h 3, h4, Matrix.mul_add, Matrix.add_mul, h]
  have h6 : A ^ 3 = A + A := by
    calc A ^ 3 = A ^ 3 * P * P⁻¹ := by rw [Matrix.mul_assoc, hinvr, Matrix.mul_one]
      _ = (A + A) * P * P⁻¹ := by rw [h5]
      _ = A + A := by rw [Matrix.mul_assoc, hinvr, Matrix.mul_one]
  have h7 : φ (M ^ 3) = φ (M + M) := by rw [map_pow, map_add, ← hA, h6]
  have h8 := congrFun (congrFun h7 1) 0
  rw [hφ, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply] at h8
  exact pow_three (Int.cast_injective h8)

end MO452919

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_452919.main) := by
  intro h
  obtain ⟨P, d, hP, hPD⟩ := h (Fin 4) MO452919.G MO452919.edges
  exact MO452919.not_diag P d hP hPD
