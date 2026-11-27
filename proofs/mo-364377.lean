import OMAStatements.S_mo_364377
import Mathlib

/-!
# A Fano-complement counterexample to nearest-target motion

The question is MathOverflow 364377 by ryanriess. The support of this
7-by-7 weighing matrix is the Fano complement. Hall and Severini proved
a stronger rigidity result for this support in the appendix to
"Locality for quantum systems on graphs depends on the number field".
Here we prove the specific logarithmic balance directly from column
orthogonality and check the closest-target property separately.
-/

namespace Fano
open OMA.S_mo_364377

def mask (i j : Fin 7) : Bool :=
  let d := (j.val + 7 - i.val) % 7
  decide (d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 4)

noncomputable def A : Mat 7 := fun i j =>
  if i = j then -(1/2:ℝ) else if mask i j then 1/2 else 0

noncomputable def P : Mat 7 := fun i j => if j = i then -1 else 0

theorem mask_diag (i : Fin 7) : mask i i = true := by fin_cases i <;> decide

theorem A_diag (i : Fin 7) : A i i = -(1/2:ℝ) := by simp [A]

theorem A_abs {i j : Fin 7} (h : mask i j = true) : |A i j| = (1/2:ℝ) := by
  by_cases e : i=j <;> simp [A, e, h]

theorem A_zero {i j : Fin 7} (h : mask i j = false) : A i j = 0 := by
  have e : i ≠ j := by intro hh; subst j; simp [mask_diag] at h
  simp [A,e,h]

end Fano

namespace Fano

open OMA.S_mo_364377

private def num (i j : Fin 7) : ℤ :=
  if i = j then -1 else if mask i j then 1 else 0

private theorem A_eq_num (i j : Fin 7) : A i j = (num i j : ℝ) / 2 := by
  by_cases h : i = j <;> cases hm : mask i j <;> norm_num [A, num, h, hm]

theorem A_orthogonal : orthogonal A := by
  have gram : ∀ i j : Fin 7, (∑ k : Fin 7, num k i * num k j) = if i = j then 4 else 0 := by
    decide
  unfold orthogonal
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, A_eq_num]
  have hp (k : Fin 7) : (num k i : ℝ) / 2 * ((num k j : ℝ) / 2)
      = ((num k i * num k j : ℤ) : ℝ) / 4 := by push_cast; ring
  simp_rw [hp, ← Finset.sum_div]
  rw [← Int.cast_sum, gram i j]
  split <;> norm_num

theorem A_not_signed : ¬ signedPermutation A := by
  rintro ⟨σ, s, hs, h⟩
  have hz := h 0 0
  rw [A_diag] at hz
  split at hz
  · rcases hs 0 with h0 | h0 <;> linarith
  · norm_num at hz

theorem P_signed : signedPermutation P :=
  ⟨Equiv.refl _, fun _ => -1, fun _ => Or.inr rfl, fun _ _ => rfl⟩

private lemma row_dist (v : Fin 7 → ℝ) (a : Fin 7) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (∑ j, (v j - (if j = a then s else 0))^2)
      = (∑ j, (v j)^2) + (1 - 2*v a*s) := by
  have hj (j : Fin 7) : (v j - (if j = a then s else 0))^2 =
      (v j)^2 + if j = a then 1 - 2*v j*s else 0 := by
    by_cases h : j = a
    · rcases hs with rfl | rfl <;> simp only [if_pos h] <;> ring
    · simp [h]
  simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem P_nearest (Q : Mat 7) (hQ : signedPermutation Q) : frobSq A P ≤ frobSq A Q := by
  obtain ⟨σ, s, hs, hmat⟩ := hQ
  apply Finset.sum_le_sum
  intro i _
  have hr := row_dist (A i) (σ i) (s i) (hs i)
  have hp := row_dist (A i) i (-1) (Or.inr rfl)
  simp_rw [hmat]
  change (∑ j, (A i j - (if j = i then (-1:ℝ) else 0))^2) ≤ _
  rw [hp, hr, A_diag]
  have hb : |A i (σ i)| ≤ 1/2 := by
    unfold A
    split
    · norm_num [abs_neg]
    · split <;> norm_num
  have hb' := abs_le.mp hb
  rcases hs i with hsign | hsign <;> rw [hsign] <;> linarith [hb'.1, hb'.2]

end Fano

namespace Fano
open OMA.S_mo_364377 Finset

/-- Each pair of columns has precisely two common nonzero coordinates. Their
orthogonality makes the two products in these positions equal in magnitude. -/
private theorem column_balance (B : Mat 7) (hB : orthogonal B)
    (hz : ∀ i j, mask i j = false → B i j = 0)
    (hn : ∀ i j, mask i j = true → B i j ≠ 0) {i j r s : Fin 7}
    (hij : i ≠ j) (hrs : r ≠ s)
    (hits : ∀ t, (mask t i = true ∧ mask t j = true) ↔ t = r ∨ t = s) :
    (Real.log |B r i| - Real.log (1/2)) + (Real.log |B r j| - Real.log (1/2)) =
    (Real.log |B s i| - Real.log (1/2)) + (Real.log |B s j| - Real.log (1/2)) := by
  have hdot : ∑ t, B t i * B t j = 0 := by
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,if_neg hij] using
      congrFun (congrFun hB i) j
  have terms (t : Fin 7) : B t i * B t j =
      (if t=r then B r i * B r j else 0) + (if t=s then B s i * B s j else 0) := by
    by_cases er : t=r
    · subst t
      simp [hrs]
    by_cases es : t=s
    · subst t
      simp [hrs.symm]
    simp only [if_neg er, if_neg es, add_zero]
    by_cases hi : mask t i = true
    · have hj : mask t j = false := by
        cases e : mask t j
        · rfl
        · exact False.elim ((hits t |>.mp ⟨hi,e⟩).elim er es)
      simp [hz t j hj]
    · simp [hz t i (by simpa using hi)]
  rw [Finset.sum_congr rfl (fun t _ => terms t), sum_add_distrib] at hdot
  simp only [sum_ite_eq', mem_univ, ite_true] at hdot
  obtain ⟨hri,hrj⟩ := (hits r).mpr (Or.inl rfl)
  obtain ⟨hsi,hsj⟩ := (hits s).mpr (Or.inr rfl)
  have ha : |B r i| * |B r j| = |B s i| * |B s j| := by
    rw [← abs_mul, ← abs_mul, show B r i * B r j = -(B s i * B s j) by linarith, abs_neg]
  have hl := congrArg Real.log ha
  rw [Real.log_mul (abs_ne_zero.mpr (hn r i hri)) (abs_ne_zero.mpr (hn r j hrj)),
    Real.log_mul (abs_ne_zero.mpr (hn s i hsi)) (abs_ne_zero.mpr (hn s j hsj))] at hl
  linarith

private theorem fano_count (W : Fin 7 → Fin 7 → ℝ)
    (h : ∀ {i j r s : Fin 7}, i≠j → r≠s →
      (∀ t, (mask t i = true ∧ mask t j = true) ↔ t=r ∨ t=s) →
      W r i + W r j = W s i + W s j) :
    3*(∑ i, W i i) = ∑ i, ∑ j, if mask i j = true ∧ i≠j then W i j else 0 := by
  have h01 := @h 0 1 0 6 (by decide) (by decide) (by decide)
  have h02 := @h 0 2 0 5 (by decide) (by decide) (by decide)
  have h03 := @h 0 3 3 6 (by decide) (by decide) (by decide)
  have h04 := @h 0 4 0 3 (by decide) (by decide) (by decide)
  have h05 := @h 0 5 5 3 (by decide) (by decide) (by decide)
  have h06 := @h 0 6 6 5 (by decide) (by decide) (by decide)
  have h12 := @h 1 2 1 0 (by decide) (by decide) (by decide)
  have h13 := @h 1 3 1 6 (by decide) (by decide) (by decide)
  have h14 := @h 1 4 4 0 (by decide) (by decide) (by decide)
  have h15 := @h 1 5 1 4 (by decide) (by decide) (by decide)
  have h16 := @h 1 6 6 4 (by decide) (by decide) (by decide)
  have h23 := @h 2 3 2 1 (by decide) (by decide) (by decide)
  have h24 := @h 2 4 2 0 (by decide) (by decide) (by decide)
  have h25 := @h 2 5 5 1 (by decide) (by decide) (by decide)
  have h26 := @h 2 6 2 5 (by decide) (by decide) (by decide)
  have h34 := @h 3 4 3 2 (by decide) (by decide) (by decide)
  have h35 := @h 3 5 3 1 (by decide) (by decide) (by decide)
  have h36 := @h 3 6 6 2 (by decide) (by decide) (by decide)
  have h45 := @h 4 5 4 3 (by decide) (by decide) (by decide)
  have h46 := @h 4 6 4 2 (by decide) (by decide) (by decide)
  have h56 := @h 5 6 5 4 (by decide) (by decide) (by decide)
  have sum7 (f : Fin 7 → ℝ) : ∑ i, f i = f 0+(f 1+(f 2+(f 3+(f 4+(f 5+f 6))))) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  simp only [sum7]
  norm_num [mask, Fin.ext_iff, Fin.val_natCast]
  linear_combination h01 + h02 + h03 + h04 + h05 + h06 + h12 + h13 + h14 + h15 + h16 + h23 + h24 + h25 + h26 + h34 + h35 + h36 + h45 + h46 + h56

/-- Counting the common nonzero coordinates over all column pairs, each diagonal
entry appears three times, while each off-diagonal supported entry has net weight one
on the opposite side. -/
theorem balance (B : Mat 7) (hB : orthogonal B)
    (hz : ∀ i j, mask i j = false → B i j = 0)
    (hn : ∀ i j, mask i j = true → B i j ≠ 0) :
    3*(∑ i, (Real.log |B i i| - Real.log (1/2))) =
      ∑ i, ∑ j, if mask i j = true ∧ i≠j then Real.log |B i j| - Real.log (1/2) else 0 :=
  fano_count _ (column_balance B hB hz hn)

end Fano

namespace Fano
open OMA.S_mo_364377 Finset

/-- The balance of magnitudes is incompatible with the three motion requirements
in a squared Frobenius neighborhood of radius one quarter. -/
theorem no_improvement (B : Mat 7) (hclose : frobSq A B < 1/4)
    (hdiag : ∀ i j, P i j ≠ 0 → |A i j| ≤ |B i j|)
    (hstrict : ∃ i j, P i j ≠ 0 ∧ |A i j| < |B i j|)
    (hoff : ∀ i j, P i j = 0 → |B i j| ≤ |A i j|)
    (balance_if :
      (∀ i j, mask i j = false → B i j = 0) →
      (∀ i j, mask i j = true → B i j ≠ 0) →
      3 * (∑ i, (Real.log |B i i| - Real.log (1/2))) =
        ∑ i, ∑ j, if mask i j = true ∧ i ≠ j
          then Real.log |B i j| - Real.log (1/2) else 0) : False := by
  have hz (i j) (h : mask i j = false) : B i j = 0 := by
    have hij : j ≠ i := by rintro rfl; simp [mask_diag] at h
    have hu := hoff i j (by simp [P, hij])
    rw [A_zero h, abs_zero] at hu
    exact abs_nonpos_iff.mp hu
  have hnonzero (i j) (h : mask i j = true) : B i j ≠ 0 := by
    intro hb
    have bound : (A i j - B i j)^2 ≤ frobSq A B :=
      (single_le_sum (fun k _ => sq_nonneg (A i k - B i k)) (mem_univ j)).trans
        (single_le_sum (fun l _ => sum_nonneg fun k _ => sq_nonneg (A l k - B l k)) (mem_univ i))
    rw [hb, sub_zero, ← sq_abs, A_abs h] at bound
    linarith
  have hmin (i) : (1/2:ℝ) ≤ |B i i| := by
    simpa only [A_abs (mask_diag i)] using hdiag i i (by simp [P])
  obtain ⟨i,j,hij,hgain⟩ := hstrict
  have heq : j = i := by by_contra h; simp [P,h] at hij
  subst j
  rw [A_abs (mask_diag i)] at hgain
  have hpos : 0 < ∑ j, (Real.log |B j j| - Real.log (1/2)) :=
    sum_pos' (fun j _ => sub_nonneg.mpr (Real.log_le_log (by norm_num) (hmin j)))
      ⟨i, mem_univ i, sub_pos.mpr (Real.log_lt_log (by norm_num) hgain)⟩
  have hneg : (∑ i, ∑ j, if mask i j = true ∧ i ≠ j
      then Real.log |B i j| - Real.log (1/2) else 0) ≤ 0 := by
    apply sum_nonpos
    intro i _
    apply sum_nonpos
    intro j _
    split_ifs with h
    · apply sub_nonpos.mpr
      apply Real.log_le_log (abs_pos.mpr (hnonzero i j h.1))
      simpa only [A_abs h.1] using hoff i j (by simp [P, Ne.symm h.2])
    · exact le_rfl
  linarith only [balance_if hz hnonzero, hpos, hneg]

end Fano

open Fano in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_364377.main) := by
  intro h
  obtain ⟨B,hB,hclose,hd,hs,ho⟩ :=
    h 7 A P A_orthogonal A_not_signed P_signed P_nearest (1/4) (by norm_num)
  exact no_improvement B hclose hd hs ho (balance B hB)
