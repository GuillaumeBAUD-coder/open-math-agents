import OMAStatements.S_mo_424348
import Mathlib

namespace Mo424348aux

def ti : Fin 6 → ℤ := ![1, -1, 2, -2, 3, -3]

lemma ti_inj : Function.Injective ti := by decide

noncomputable def tt : Fin 6 → ℝ := fun i => (ti i : ℝ)

lemma tt_inj : Function.Injective tt := fun i j h => ti_inj (by
  unfold tt at h
  exact_mod_cast h)

noncomputable def v : Fin 6 → Fin 3 → ℝ := fun i k => tt i ^ (k : ℕ)

noncomputable def xs : Fin 3 → Fin 3 → ℝ := ![![-27, 0, 3], ![-32, 0, 8], ![0, 0, 0]]

def aa : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

def bb : Fin 6 → Fin 3 := ![1, 1, 2, 2, 0, 0]

lemma indep (e : Fin 3 ↪ Fin 6) : LinearIndependent ℝ (fun i => v (e i)) := by
  have h : (fun i => v (e i)) = (Matrix.vandermonde (tt ∘ e)).row := by
    ext i k
    simp [v, Matrix.vandermonde_apply, Matrix.row]
  rw [h, Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
  exact tt_inj.comp e.injective

lemma neq : ∀ i : Fin 6, aa i ≠ bb i := by decide

lemma constr : ∀ i : Fin 6, (∑ k, v i k * xs (aa i) k) = ∑ k, v i k * xs (bb i) k := by
  intro i
  fin_cases i <;> simp [Fin.sum_univ_three, v, tt, ti, xs, aa, bb] <;> norm_num

lemma distinct : ∀ p q : Fin 3, xs p = xs q → p = q := by
  intro p q h
  have h0 := congrFun h 0
  fin_cases p <;> fin_cases q <;> first | rfl | (exfalso; simp [xs] at h0)

end Mo424348aux

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_424348.main) := by
  intro h
  obtain ⟨p, q, hpq, hx⟩ := h 3 3 (by norm_num) (by norm_num) Mo424348aux.v Mo424348aux.indep
    Mo424348aux.xs Mo424348aux.aa Mo424348aux.bb Mo424348aux.neq Mo424348aux.constr
  exact hpq (Mo424348aux.distinct p q hx)
