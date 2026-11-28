import OMAStatements.S_oeis_a259057
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace A259057

open OMA.S_oeis_a259057 (radius entry B normalizedDet)

/-- On the source's upper wedge, this is its displayed entry formula. -/
lemma entry_upper_wedge (n i j : ℤ) (hij : i ≤ j) (hedge : j ≤ n - 1 - i) :
    entry n i j = i * n - i ^ 2 + j + 1 := by
  have hr : radius n i j = i := by unfold radius; omega
  rw [entry, hr, abs_of_nonpos (by omega : i - j ≤ 0)]
  ring

lemma entry_transpose (n i j : ℤ) : entry n j i = entry n i j := by
  have hr : radius n j i = radius n i j := by
    unfold radius
    rw [min_comm j i, min_comm (n - 1 - j) (n - 1 - i)]
  simp only [entry, hr, abs_sub_comm]

lemma entry_centrosymmetry (n i j : ℤ) :
    entry n (n - 1 - i) (n - 1 - j) = entry n i j := by
  have hi : n - 1 - (n - 1 - i) = i := by ring
  have hj : n - 1 - (n - 1 - j) = j := by ring
  have hr : radius n (n - 1 - i) (n - 1 - j) = radius n i j := by
    unfold radius
    rw [hi, hj, min_comm (min (n - 1 - i) (n - 1 - j)) (min i j)]
  have ha : (n - 1 - i) - (n - 1 - j) = -(i - j) := by ring
  simp only [entry, hr, ha, abs_neg]

lemma entry_left (n i j : ℤ)
    (h1 : j ≤ i) (h2 : j ≤ n - 1 - i) (h3 : j ≤ n - 1 - j) :
    entry n i j = j * (n - j) + i + 1 := by
  have hr : radius n i j = j := by
    unfold radius
    rw [min_eq_right h1, min_eq_left (le_min h2 h3)]
  rw [entry, hr, abs_of_nonneg (by omega : 0 ≤ i - j)]
  ring

lemma entry_right (n i j : ℤ)
    (h1 : i ≤ j) (h2 : n - 1 - j ≤ i) (h3 : n - 1 - j ≤ j) :
    entry n i j = (n - 1 - j) * (j + 2) + j - i + 1 := by
  have hr : radius n i j = n - 1 - j := by
    unfold radius
    rw [min_eq_right (by omega : n - 1 - j ≤ n - 1 - i),
      min_eq_right (le_min h2 h3)]
  rw [entry, hr, abs_of_nonpos (by omega : i - j ≤ 0)]
  ring

lemma central_relation (k j : ℤ) :
    entry (2 * k + 4) (k + 1) j + entry (2 * k + 4) (k + 2) j -
      entry (2 * k + 4) k j - entry (2 * k + 4) (k + 3) j =
      if j = k + 1 ∨ j = k + 2 then 6 else 0 := by
  by_cases hj : j ≤ k
  · have hh : ¬ (j = k + 1 ∨ j = k + 2) := by omega
    rw [if_neg hh]
    rw [entry_left _ _ _ (by omega) (by omega) (by omega),
      entry_left _ _ _ (by omega) (by omega) (by omega),
      entry_left _ _ _ (by omega) (by omega) (by omega),
      entry_left _ _ _ (by omega) (by omega) (by omega)]
    ring
  · by_cases hj1 : j = k + 1
    · subst j
      have hr0 : radius (2 * k + 4) k (k + 1) = k := by unfold radius; omega
      have hr1 : radius (2 * k + 4) (k + 1) (k + 1) = k + 1 := by unfold radius; omega
      have hr2 : radius (2 * k + 4) (k + 2) (k + 1) = k + 1 := by unfold radius; omega
      have hr3 : radius (2 * k + 4) (k + 3) (k + 1) = k := by unfold radius; omega
      simp only [entry, hr0, hr1, hr2, hr3, true_or, if_true, sub_self, abs_zero]
      rw [abs_of_nonneg (by omega : 0 ≤ k + 2 - (k + 1)),
        abs_of_nonpos (by omega : k - (k + 1) ≤ 0),
        abs_of_nonneg (by omega : 0 ≤ k + 3 - (k + 1))]
      ring
    · by_cases hj2 : j = k + 2
      · subst j
        have hr0 : radius (2 * k + 4) k (k + 2) = k := by unfold radius; omega
        have hr1 : radius (2 * k + 4) (k + 1) (k + 2) = k + 1 := by unfold radius; omega
        have hr2 : radius (2 * k + 4) (k + 2) (k + 2) = k + 1 := by unfold radius; omega
        have hr3 : radius (2 * k + 4) (k + 3) (k + 2) = k := by unfold radius; omega
        simp only [entry, hr0, hr1, hr2, hr3, or_true, if_true, sub_self, abs_zero]
        rw [abs_of_nonpos (by omega : k + 1 - (k + 2) ≤ 0),
          abs_of_nonpos (by omega : k - (k + 2) ≤ 0),
          abs_of_nonneg (by omega : 0 ≤ k + 3 - (k + 2))]
        ring
      · have hj3 : k + 3 ≤ j := by omega
        rw [if_neg (by omega)]
        rw [entry_right _ _ _ (by omega) (by omega) (by omega),
          entry_right _ _ _ (by omega) (by omega) (by omega),
          entry_right _ _ _ (by omega) (by omega) (by omega),
          entry_right _ _ _ (by omega) (by omega) (by omega)]
        ring

lemma det_zero_of_four_rows {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (a b c d : ι)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hr : ∀ j, M a j + M b j - M c j - M d j = 0) : M.det = 0 := by
  let u : ι → R := M a + M b + (-1 : R) • M c + (-1 : R) • M d
  have hu : u = 0 := by
    funext j
    simpa [u, sub_eq_add_neg] using hr j
  have hd : (M.updateRow a u).det = M.det := by
    dsimp [u]
    simp only [Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
      Matrix.det_updateRow_eq_zero (M := M) hab.symm,
      Matrix.det_updateRow_eq_zero (M := M) hac.symm,
      Matrix.det_updateRow_eq_zero (M := M) had.symm,
      Matrix.updateRow_eq_self, mul_zero, add_zero]
  have hz : (M.updateRow a u).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero a
    intro j
    rw [hu]
    simp
  exact hd.symm.trans hz

lemma three_dvd_det_large (k : ℕ) : (3 : ℤ) ∣ (B (2 * k + 4)).det := by
  let a : Fin (2 * k + 4) := ⟨k + 1, by omega⟩
  let b : Fin (2 * k + 4) := ⟨k + 2, by omega⟩
  let c : Fin (2 * k + 4) := ⟨k, by omega⟩
  let d : Fin (2 * k + 4) := ⟨k + 3, by omega⟩
  let M : Matrix (Fin (2 * k + 4)) (Fin (2 * k + 4)) (ZMod 3) :=
    (B (2 * k + 4)).map (fun x => (x : ZMod 3))
  have hr : ∀ j, M a j + M b j - M c j - M d j = 0 := by
    intro j
    have h := central_relation (k : ℤ) (j.val : ℤ)
    have hcast := congrArg (fun x : ℤ => (x : ZMod 3)) h
    dsimp [M, B, Matrix.map, a, b, c, d]
    push_cast at hcast ⊢
    split_ifs at hcast
    · exact hcast.trans (by decide : (6 : ZMod 3) = 0)
    · exact hcast
  have hz : M.det = 0 := by
    apply det_zero_of_four_rows M a b c d _ _ _ hr
    all_goals
      intro he
      have hv := congrArg Fin.val he
      dsimp [a, b, c, d] at hv
      omega
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  rw [Int.cast_det]
  exact hz

lemma det_two : (B 2).det = -3 := by
  norm_num [Matrix.det_fin_two, B, entry, radius]

/-- The determinant of every positive even-dimensional matrix is divisible by three. -/
theorem three_dvd_det_even (m : ℕ) (hm : 0 < m) : (3 : ℤ) ∣ (B (2 * m)).det := by
  rcases m with _ | m
  · omega
  rcases m with _ | k
  · change (3 : ℤ) ∣ (B 2).det
    rw [det_two]
    norm_num
  · have hn : 2 * (k + 1 + 1) = 2 * k + 4 := by omega
    rw [hn]
    exact three_dvd_det_large k

/-- The sequence described in OEIS A259057, as an a priori rational number. -/
theorem normalizedDet_integral (m : ℕ) (hm : 0 < m) :
    ∃ z : ℤ, normalizedDet m = (z : ℚ) := by
  obtain ⟨z, hz⟩ := three_dvd_det_even m hm
  refine ⟨z, ?_⟩
  unfold normalizedDet
  rw [hz]
  push_cast
  ring


end A259057

theorem OMA.solution : type_of% @OMA.S_oeis_a259057.main := A259057.normalizedDet_integral
