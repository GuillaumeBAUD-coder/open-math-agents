import OMAStatements.S_mo_200855
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Tactic

open OMA.S_mo_200855

namespace OMA.MO200855

-- An eleven-vertex counterexample to the centrality comparison,
-- verified by the same exact vector-certificate argument as the earlier proof.
-- Bit j in row i records the edge between i and j.
def graph (i j : Fin 11) : Bool :=
  (![158, 1177, 865, 99, 195, 972, 316, 51, 1124, 36, 258] i : ℕ).testBit j.val

-- The scores are verified from integer solutions to (22 I - A) v = 22 d · 1.
theorem score_from_vector (G : Fin 11 → Fin 11 → Bool) (hdiag : ∀ i, G i i = false)
    (v : Fin 11 → ℤ) (d : ℤ) (hd : d ≠ 0)
    (hv : ∀ i, 22 * v i - ∑ j, (if G i j then v j else 0) = 22 * d) :
    score G (1 / 22) = fun i => (v i : ℝ) / d := by
  let M : Matrix (Fin 11) (Fin 11) ℝ := 1 - (1 / 22 : ℝ) • realAdj G
  have hMdiag (i : Fin 11) : M i i = 1 := by
    simp [M, realAdj, hdiag i]
  have hM : M.det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro i
    have hOff (j : Fin 11) (hj : j ∈ Finset.univ.erase i) : ‖M i j‖ ≤ 1 / 22 := by
      have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      cases hG : G i j <;> norm_num [M, Matrix.one_apply, realAdj, hij, hG, Real.norm_eq_abs]
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, (1 / 22 : ℝ) := Finset.sum_le_sum hOff
      _ < _ := by
        rw [hMdiag, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
        norm_num
  let y : Fin 11 → ℝ := fun i => (v i : ℝ) / d
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hMy : M.mulVec y = fun _ => 1 := by
    funext i
    have hi := congrArg (fun z : ℤ => (z : ℝ)) (hv i)
    push_cast at hi
    have hsum : (∑ j, (if G i j then (1 : ℝ) else 0) * y j) =
        (∑ j, (if G i j then (v j : ℝ) else 0)) / d := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      cases G i j <;> simp [y]
    change ((1 - (1 / 22 : ℝ) • realAdj G).mulVec y) i = 1
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    change y i - (1 / 22 : ℝ) * (∑ j, (if G i j then (1 : ℝ) else 0) * y j) = 1
    rw [hsum]
    change (v i : ℝ) / d - (1 / 22) * (_ / d) = 1
    rw [← mul_div_assoc, ← sub_div]
    apply (div_eq_iff hd').2
    linarith
  change M⁻¹.mulVec (fun _ => 1) = y
  rw [← hMy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),
    Matrix.one_mulVec]

def original : Fin 11 → ℤ :=
  ![8111782584818, 8064992709191, 8109912272088, 7802754847008, 7773283971651, 8435027057380, 8127199016255, 7786667799526, 7755794942951, 7066661118000, 7033745132667]

def removed : Fin 11 → ℤ :=
  ![31042147063310, 30846012424062, 32457494992999, 31157837751171, 31033902119749, 33814158710707, 32579686618205, 31087574819423, 31099286316406, 28339185427872, 28142532929543]

def added : Fin 11 → ℤ :=
  ![32523240379741, 33746834157762, 33918293531762, 31222599516789, 31104835046099, 33749202629756, 32517570374785, 31158384274576, 31031275693550, 28273992635856, 28142656894483]

end OMA.MO200855

open OMA.MO200855

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_200855.main) := by
  intro h
  have hY := score_from_vector graph (by decide) original 6314618421206 (by decide) (by decide +kernel)
  have hX := score_from_vector (edit graph 0 1 false) (by decide) removed 25326837532249
    (by decide) (by decide +kernel)
  have hZ := score_from_vector (edit graph 1 2 true) (by decide) added 25198197355787
    (by decide) (by decide +kernel)
  have hba : score graph (1 / 22) 1 ≤ score graph (1 / 22) 0 := by
    rw [hY]
    norm_num [original, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have hca : score graph (1 / 22) 2 ≤ score graph (1 / 22) 0 := by
    rw [hY]
    norm_num [original, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have hineq := h 11 (by decide) graph 0 1 2 (1 / 22) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num) hba hca
  rw [hX, hY, hZ] at hineq
  norm_num [original, removed, added, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at hineq
