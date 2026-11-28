import OMAStatements.S_mo_256897
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Matrix-optimal factors need not be tensor-optimal

An explicit counterexample to Ulderique Demoitre's question:
https://mathoverflow.net/questions/256897

The input columns are the first two standard basis vectors in ℝ³.
The single column −e₀ minimizes the order-two Frobenius distance.
At order three, replacing it by +e₀ lowers the squared distance from 5 to 1.

Formal statement credit: @etaubman.
Disproof credit: @grp06.
-/

open scoped BigOperators
open OMA.S_mo_256897

namespace OMA.Mo256897Counterexample

private def input : Matrix (Fin 3) (Fin 2) ℝ :=
  fun i j => if i.val = j.val then 1 else 0

private def firstColumn (t : ℝ) : Matrix (Fin 3) (Fin 1) ℝ :=
  fun i _ => if i.val = 0 then t else 0

private theorem input_rank : FullColumnRank input := by
  unfold FullColumnRank
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.forall_fin_two]
  constructor
  · have h := congrArg (fun v : Fin 3 → ℝ => v 0) hg
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul] at h
    simpa [input, Fin.val_one] using h
  · have h := congrArg (fun v : Fin 3 → ℝ => v 1) hg
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul] at h
    simpa [input, Fin.val_one] using h

private theorem firstColumn_rank {t : ℝ} (ht : t ≠ 0) :
    FullColumnRank (firstColumn t) := by
  unfold FullColumnRank
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (fun v : Fin 3 → ℝ => v 0) hg
  have hmul : g 0 * t = 0 := by
    simpa [Fin.sum_univ_one, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, firstColumn] using h
  have hj : j = 0 := Subsingleton.elim _ _
  rw [hj]
  exact (mul_eq_zero.mp hmul).resolve_right ht

private theorem sum_two_coordinates (f : Fin 3 → Fin 3 → ℝ) :
    (∑ a : Fin 2 → Fin 3, f (a 0) (a 1)) = ∑ i, ∑ j, f i j := by
  calc
    _ = ∑ p : Fin 3 × Fin 3, f p.1 p.2 :=
      Fintype.sum_equiv (finTwoArrowEquiv (Fin 3)) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type' f

private theorem sum_three_coordinates (f : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    (∑ a : Fin 3 → Fin 3, f (a 0) (a 1) (a 2)) = ∑ i, ∑ j, ∑ k, f i j k := by
  let e : (Fin 3 → Fin 3) ≃ Fin 3 × (Fin 3 × Fin 3) :=
    (Fin.consEquiv (fun _ : Fin 3 => Fin 3)).symm.trans
      (Equiv.prodCongr (Equiv.refl (Fin 3)) (finTwoArrowEquiv (Fin 3)))
  calc
    _ = ∑ p : Fin 3 × (Fin 3 × Fin 3), f p.1 p.2.1 p.2.2 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by simp only [Fintype.sum_prod_type]

private theorem squared_error_two (N : Matrix (Fin 3) (Fin 1) ℝ) :
    squaredError input N 2 =
      1 + (N 0 0 ^ 2 + N 1 0 ^ 2 + N 2 0 ^ 2 - 1) ^ 2 + 2 * N 2 0 ^ 2 := by
  unfold squaredError
  simp only [tensor, Fin.prod_univ_two, Fin.sum_univ_two, Fin.sum_univ_one]
  rw [sum_two_coordinates (fun i j =>
    (input i 0 * input j 0 + input i 1 * input j 1 - N i 0 * N j 0) ^ 2)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.succ_zero_eq_one', Fin.succ_one_eq_two']
  norm_num [input, Fin.val_zero, Fin.val_one, show (2 : Fin 3).val = 2 from rfl] <;> ring

private theorem squared_error_two_neg :
    squaredError input (firstColumn (-1)) 2 = 1 := by
  rw [squared_error_two]
  norm_num [firstColumn, Fin.val_one, show (2 : Fin 3).val = 2 from rfl]

private theorem squared_error_three_formula (t : ℝ) :
    squaredError input (firstColumn t) 3 = (1 - t * t * t) ^ 2 + 1 := by
  unfold squaredError
  simp only [tensor, Fin.prod_univ_three, Fin.sum_univ_two, Fin.sum_univ_one]
  rw [sum_three_coordinates (fun i j k =>
    (input i 0 * input j 0 * input k 0 + input i 1 * input j 1 * input k 1 -
      firstColumn t i 0 * firstColumn t j 0 * firstColumn t k 0) ^ 2)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.succ_zero_eq_one', Fin.succ_one_eq_two']
  norm_num [input, firstColumn, Fin.val_zero, Fin.val_one,
    show (2 : Fin 3).val = 2 from rfl] <;> ring

private theorem neg_minimizes_two : Minimizes input (firstColumn (-1)) 2 := by
  intro N _
  unfold error
  apply Real.sqrt_le_sqrt
  rw [squared_error_two_neg, squared_error_two]
  exact le_trans (le_add_of_nonneg_right (sq_nonneg _))
    (le_add_of_nonneg_right (mul_nonneg (by norm_num) (sq_nonneg _)))

theorem disprove : ¬ claim := by
  intro h
  have hmin :=
    h 3 2 1 (by decide) (by decide) input (firstColumn (-1))
      input_rank (firstColumn_rank (by norm_num)) neg_minimizes_two 3 (by decide)
      (firstColumn 1) (firstColumn_rank (by norm_num))
  unfold error at hmin
  have hneg : squaredError input (firstColumn (-1)) 3 = 5 := by
    rw [squared_error_three_formula]
    norm_num
  have hpos : squaredError input (firstColumn 1) 3 = 1 := by
    rw [squared_error_three_formula]
    norm_num
  rw [hneg, hpos] at hmin
  exact (not_le_of_gt (Real.sqrt_lt_sqrt (by norm_num) (show (1 : ℝ) < 5 by norm_num))) hmin

end OMA.Mo256897Counterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_256897.main) :=
  OMA.Mo256897Counterexample.disprove
