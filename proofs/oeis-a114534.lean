import OMAStatements.S_oeis_a114534
import Mathlib

/-!
Proof that the Fibonacci matrix of A114534 has rank 2 for n ≥ 2.

Upper bound: F(m + j) = F(m) F(j+1) + (F(m+1) - F(m)) F(j), so M is a product of an n X 2 and a
2 X n matrix. Lower bound: the 2 X 2 minor of rows 0, 1 and columns 0, 1 has determinant -F(n).
-/

namespace A114534

open OMA.S_oeis_a114534

theorem fib_split (m : ℕ) : ∀ j : ℕ, ((Nat.fib (m + j) : ℚ) =
    Nat.fib m * Nat.fib (j + 1) + ((Nat.fib (m + 1) : ℚ) - Nat.fib m) * Nat.fib j) ∧
    ((Nat.fib (m + (j + 1)) : ℚ) =
    Nat.fib m * Nat.fib (j + 2) + ((Nat.fib (m + 1) : ℚ) - Nat.fib m) * Nat.fib (j + 1)) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have h1 : Nat.fib (m + (j + 1 + 1)) = Nat.fib (m + j) + Nat.fib (m + (j + 1)) := by
      rw [show m + (j + 1 + 1) = (m + j) + 2 by ring, Nat.fib_add_two]; rfl
    have h2 : Nat.fib (j + 1 + 2) = Nat.fib (j + 1) + Nat.fib (j + 2) := Nat.fib_add_two
    have h3 : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
    rw [h1, h2]
    push_cast
    rw [ih.1, ih.2, h3]
    push_cast
    ring

def A (n : ℕ) : Matrix (Fin n) (Fin 2) ℚ :=
  Matrix.of fun i k => if k = 0 then (Nat.fib ((i : ℕ) * n) : ℚ)
    else (Nat.fib ((i : ℕ) * n + 1) : ℚ) - Nat.fib ((i : ℕ) * n)

def B (n : ℕ) : Matrix (Fin 2) (Fin n) ℚ :=
  Matrix.of fun k j => if k = 0 then (Nat.fib ((j : ℕ) + 1) : ℚ) else (Nat.fib (j : ℕ) : ℚ)

theorem M_eq (n : ℕ) : M n = A n * B n := by
  ext i j
  simp [M, A, B, Matrix.mul_apply, Fin.sum_univ_two]
  exact (fib_split _ _).1

theorem rank_le (n : ℕ) : (M n).rank ≤ 2 := by
  rw [M_eq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

theorem rank_ge (n : ℕ) (hn : 2 ≤ n) : 2 ≤ (M n).rank := by
  let r : Fin 2 → Fin n := fun k => ⟨k.1, by omega⟩
  have hdet : ((M n).submatrix r r).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [M, r]
    omega
  have h := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  rw [Fintype.card_fin] at h
  rw [← h]
  exact Matrix.rank_submatrix_le _ r r

end A114534

theorem OMA.solution : type_of% @OMA.S_oeis_a114534.main :=
  fun n hn => le_antisymm (A114534.rank_le n) (A114534.rank_ge n hn)
