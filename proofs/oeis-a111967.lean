import OMAStatements.S_oeis_a111967
import Mathlib.Tactic

open OMA.S_oeis_a111967 Matrix Finset

namespace FredholmTriangle

private lemma det_corner (n : ℕ) : (corner n).det = 1 := by
  have lower : (corner n).IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    exact if_neg (fun h => (Nat.not_le.mpr hij) h.1)
  rw [det_of_isLowerTriangular _ lower]
  have diagonal (i : Fin (n+1)) : corner n i i = 1 := by
    simp [corner, show i.val ≤ 2*i.val by omega]
  simp [diagonal]

private lemma row (n : ℕ) (i : Fin (n+1)) :
    (corner n *ᵥ fun j => fredholm j.val) i = 1 := by
  classical
  let t := (i.val+1).log2
  let b := 2^t
  have bp : 0 < b := pow_pos (by decide) _
  have lo : b ≤ i.val+1 := Nat.log2_self_le (by omega)
  have hi : i.val+1 < 2*b := by
    simpa [b, t, pow_succ, Nat.mul_comm] using Nat.lt_log2_self (n := i.val+1)
  let k : Fin (n+1) := ⟨b-1, by have := i.isLt; omega⟩
  have ek : k.val+1 = b := by dsimp [k]; omega
  change (∑ j : Fin (n+1), corner n i j * fredholm j.val) = 1
  rw [sum_eq_single k]
  · have occurs : ∃ r : ℕ, k.val+1 = 2^r := ⟨t,ek⟩
    have h₁ : k.val ≤ i.val := by omega
    have h₂ : i.val ≤ 2*k.val := by omega
    have hit : corner n i k = 1 := if_pos ⟨h₁,h₂⟩
    simp [hit, fredholm, occurs]
  · intro j _ hj
    by_cases hs : j.val ≤ i.val ∧ i.val ≤ 2*j.val
    · have off : ¬ ∃ r : ℕ, j.val+1 = 2^r := by
        rintro ⟨r,hr⟩
        have low : 2^r ≤ i.val+1 := by omega
        have high : i.val+1 < 2^(r+1) := by rw [pow_succ, ← hr]; omega
        have ht : t = r := (Nat.log2_eq_iff (by omega)).2 ⟨low,high⟩
        have eb : b = 2^r := congrArg (fun s : ℕ => 2^s) ht
        apply hj
        apply Fin.ext
        omega
      simp [fredholm, off]
    · have miss : corner n i j = 0 := if_neg hs
      rw [miss, zero_mul]
  · simp

end FredholmTriangle

theorem OMA.solution : type_of% @OMA.S_oeis_a111967.main := by
  intro n
  have unit : IsUnit (corner n).det := by rw [FredholmTriangle.det_corner]; exact isUnit_one
  have eqn : corner n *ᵥ (fun j => fredholm j.val) = fun _ => 1 := funext (FredholmTriangle.row n)
  have inverse := congrArg (fun v : Fin (n+1) → ℚ => (corner n)⁻¹ *ᵥ v) eqn
  change (corner n)⁻¹ *ᵥ (corner n *ᵥ (fun j => fredholm j.val)) =
    (corner n)⁻¹ *ᵥ (fun _ => 1) at inverse
  rw [mulVec_mulVec, nonsing_inv_mul _ unit, one_mulVec] at inverse
  simpa [Matrix.mulVec, dotProduct] using (congrFun inverse (Fin.last n)).symm
