import OMAStatements.S_mo_236533
import Mathlib

open Finset Matrix

open OMA.S_mo_236533



theorem OMA.solution : type_of% @OMA.S_mo_236533.main := by
  intro n m hn A _ hA
  let X : Matrix (Fin m) (Fin n) ℝ := fun _ _ => 1 / (n : ℝ)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hAX (i j : Fin n) : (A * X) i j = 1 / (n : ℝ) := by
    rw [Matrix.mul_apply]
    change (∑ k, A i k * (1 / (n : ℝ))) = _
    rw [← Finset.sum_mul, hA, one_mul]
  refine ⟨X, fun _ _ => by dsimp [X]; positivity, ?_, ?_, ?_⟩
  · intro i
    simp [X, hn']
  · intro i j
    rw [hAX, hAX]
  · intro i j
    rw [hAX, hAX]
