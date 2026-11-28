import OMAStatements.S_mo_230766
import Mathlib

-- Problem: mo-230766, five pairwise distinct unit vectors u, v, w, x, y in R^d (d >= 3) with
-- |u + v + x| = |u + v + y| = |u + w + x| = |u + w + y| = 1.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Take, in the first three coordinates (all other coordinates 0),
--   u = (1, 0, 0), v = (3/5, 4/5, 0), w = (-1/9, 4/9, 8/9), x = -u, y = -v.
-- Then u + v + x = v, u + v + y = u, u + w + x = w and u + w + y = (13/45, -16/45, 40/45),
-- all of norm 1 (13^2 + 16^2 + 40^2 = 45^2), and the five vectors have different first
-- coordinates.

namespace MO230766

noncomputable def vec (k : ℕ) (a0 a1 a2 : ℝ) : EuclideanSpace ℝ (Fin (3 + k)) :=
  WithLp.toLp 2 (Fin.append ![a0, a1, a2] (fun _ => 0))

theorem norm1 (k : ℕ) (a0 a1 a2 : ℝ) (h : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 = 1) :
    ‖vec k a0 a1 a2‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_add, Fin.sum_univ_three]
  simpa [vec, Fin.append_left, Fin.append_right] using h

theorem norm3 (k : ℕ) (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ)
    (h : (a0 + b0 + c0) ^ 2 + (a1 + b1 + c1) ^ 2 + (a2 + b2 + c2) ^ 2 = 1) :
    ‖vec k a0 a1 a2 + vec k b0 b1 b2 + vec k c0 c1 c2‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_add, Fin.sum_univ_three]
  simpa [vec, Fin.append_left, Fin.append_right] using h

theorem vec_ne (k : ℕ) (a0 a1 a2 b0 b1 b2 : ℝ) (h : a0 ≠ b0) :
    vec k a0 a1 a2 ≠ vec k b0 b1 b2 := by
  intro e
  apply h
  have h2 := congrArg (fun z : EuclideanSpace ℝ (Fin (3 + k)) => z (Fin.castAdd k 0)) e
  simpa [vec, Fin.append_left] using h2

theorem general (k : ℕ) : OMA.S_mo_230766.Admits (3 + k) := by
  obtain ⟨u, hu⟩ : ∃ u, u = vec k 1 0 0 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = vec k (3 / 5) (4 / 5) 0 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = vec k (-1 / 9) (4 / 9) (8 / 9) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = vec k (-1) 0 0 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = vec k (-3 / 5) (-4 / 5) 0 := ⟨_, rfl⟩
  have h1 : u ≠ v := by
    rw [hu, hv]
    exact vec_ne k _ _ _ _ _ _ (by norm_num)
  have h2 : u ≠ w := by
    rw [hu, hw]
    exact vec_ne k _ _ _ _ _ _ (by norm_num)
  have h3 : u ≠ x := by
    rw [hu, hx]
    exact vec_ne k _ _ _ _ _ _ (by norm_num)
  have h4 : u ≠ y := by
    rw [hu, hy]
    exact vec_ne k _ _ _ _ _ _ (by norm_num)
  have h5 : v ≠ w := by
    rw [hv, hw]
    exact vec_ne k _ _ _ _ _ _ (by norm_num)
  have h6 : v ≠ x := by
    rw [hv, hx]
    exact vec_ne k _ _ _ _ _ _ (by norm_num)
  have h7 : v ≠ y := by
    rw [hv, hy]
    exact vec_ne k _ _ _ _ _ _ (by norm_num)
  have h8 : w ≠ x := by
    rw [hw, hx]
    exact vec_ne k _ _ _ _ _ _ (by norm_num)
  have h9 : w ≠ y := by
    rw [hw, hy]
    exact vec_ne k _ _ _ _ _ _ (by norm_num)
  have h10 : x ≠ y := by
    rw [hx, hy]
    exact vec_ne k _ _ _ _ _ _ (by norm_num)
  refine ⟨u, v, w, x, y, by simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu]
    exact norm1 k _ _ _ (by norm_num)
  · rw [hv]
    exact norm1 k _ _ _ (by norm_num)
  · rw [hw]
    exact norm1 k _ _ _ (by norm_num)
  · rw [hx]
    exact norm1 k _ _ _ (by norm_num)
  · rw [hy]
    exact norm1 k _ _ _ (by norm_num)
  · rw [hu, hv, hx]
    exact norm3 k _ _ _ _ _ _ _ _ _ (by norm_num)
  · rw [hu, hv, hy]
    exact norm3 k _ _ _ _ _ _ _ _ _ (by norm_num)
  · rw [hu, hw, hx]
    exact norm3 k _ _ _ _ _ _ _ _ _ (by norm_num)
  · rw [hu, hw, hy]
    exact norm3 k _ _ _ _ _ _ _ _ _ (by norm_num)

end MO230766

theorem OMA.solution : type_of% @OMA.S_mo_230766.main := by
  refine ⟨MO230766.general 0, ?_⟩
  intro d hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd.le
  exact MO230766.general k
