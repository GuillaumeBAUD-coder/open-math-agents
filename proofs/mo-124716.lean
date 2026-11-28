import OMAStatements.S_mo_124716
import Mathlib

open Matrix Finset

theorem OMA.solution : type_of% @OMA.S_mo_124716.main := by
  classical
  intro n a P k _ ⟨i, hi⟩ hP hrow _ _ hk
  let _ : Nonempty (Fin n) := ⟨i⟩
  let A := diagonal a + k • P
  let B := fun z : ℝ => scalar (Fin n) z - A
  by_contra h
  have unit (z : ℝ) (hz : 0 < z) : IsUnit (B z).det :=
    isUnit_iff_ne_zero.mpr fun he => h ⟨z, hz, (A.eval_charpoly z).trans he⟩
  let x := fun z : ℝ => (B z)⁻¹ *ᵥ (fun _ => (1 : ℝ))
  have row (z : ℝ) (hz : 0 < z) (r : Fin n) :
      (z - a r) * x z r = 1 + k * ∑ j, P r j * x z j := by
    have eqn : B z *ᵥ x z = fun _ => (1 : ℝ) := by
      simp only [x, mulVec_mulVec, mul_nonsing_inv _ (unit z hz), one_mulVec]
    have e := congrFun eqn r
    simp only [B, A, sub_mulVec, add_mulVec, smul_mulVec, scalar_apply,
      mulVec_diagonal, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
    change z * x z r - (a r * x z r + k * ∑ j, P r j * x z j) = 1 at e
    linarith
  let m := fun z : ℝ => univ.inf' univ_nonempty (x z)
  have lower (z : ℝ) (r : Fin n) : m z ≤ x z r := inf'_le _ (mem_univ r)
  have average (z : ℝ) (r : Fin n) : m z ≤ ∑ j, P r j * x z j := calc
    m z = ∑ j, P r j * m z := by rw [← sum_mul, hrow, one_mul]
    _ ≤ _ := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (lower z j) (hP r j).1
  have nozero (z : ℝ) (hz : 0 < z) : m z ≠ 0 := by
    obtain ⟨r, _, hr⟩ := exists_mem_eq_inf' univ_nonempty (x z)
    change m z = x z r at hr
    intro hm
    have e := row z hz r
    rw [← hr, hm, mul_zero] at e
    have ha := average z r
    rw [hm] at ha
    linarith [mul_nonneg hk.le ha]
  let b := univ.sup' univ_nonempty a + k + 1
  have bound (r : Fin n) : a r + k < b := by
    have := le_sup' a (mem_univ r)
    dsimp [b]
    linarith
  have hib : a i ≤ b := by linarith [bound i]
  have hb : 0 < b := hi.trans_le hib
  have left : m (a i) ≤ 0 := by
    by_contra! hm
    have e := row (a i) hi i
    rw [sub_self, zero_mul] at e
    linarith [mul_nonneg hk.le (hm.le.trans (average (a i) i))]
  have right : 0 ≤ m b := by
    by_contra! hm
    obtain ⟨r, _, hr⟩ := exists_mem_eq_inf' univ_nonempty (x b)
    change m b = x b r at hr
    have e := row b hb r
    rw [← hr] at e
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ b - a r - k by linarith [bound r]) hm.le,
      mul_le_mul_of_nonneg_left (average b r) hk.le]
  have contB : Continuous B := by
    change Continuous (fun z : ℝ => diagonal (fun _ : Fin n => z) - A)
    apply Continuous.sub _ continuous_const
    apply continuous_matrix
    intro r j
    by_cases he : r = j <;> simp [diagonal, he, Matrix.of_apply] <;> fun_prop
  have cont : ContinuousOn m (Set.Icc (a i) b) := by
    apply ContinuousOn.finset_inf'_apply
    intro r _
    intro z hz
    have hz' : 0 < z := hi.trans_le hz.1
    have invc := continuousAt_matrix_inv (B z) (by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (unit z hz').ne_zero)
    have invB := invc.comp contB.continuousAt
    change ContinuousWithinAt (fun s => ∑ j, (B s)⁻¹ r j * 1) _ z
    simpa [Function.comp_def] using (continuous_finsetSum _ fun j _ =>
      (continuous_apply j).comp (continuous_apply r) : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ =>
        ∑ j, M r j)).continuousAt.comp invB |>.continuousWithinAt
  obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc hib cont (show 0 ∈ Set.Icc (m (a i)) (m b) from ⟨left, right⟩)
  exact nozero z (hi.trans_le hz.1) hzero
