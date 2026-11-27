import OMAReductions.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

-- Credit: @anmolspace
open Polynomial Finset

namespace OMA.BinaryForms

/-- Subtracting the minimum of a nonnegative polynomial produces a double root. -/
private theorem splitAtMinimum (p : ℝ[X]) (hp : ∀ x, 0 ≤ p.eval x) :
    ∃ (a : ℝ) (r : ℝ[X]), p - C (p.eval a) = (X - C a)^2 * r ∧
      ∀ x, 0 ≤ r.eval x := by
  obtain ⟨a, ha⟩ := p.exists_forall_norm_le
  have hmin (x : ℝ) : p.eval a ≤ p.eval x := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hp _)] using ha x
  have hloc : IsLocalMin p.eval a := Filter.Eventually.of_forall hmin
  have hd : p.derivative.eval a = 0 := (p.hasDerivAt a).deriv.symm.trans hloc.deriv_eq_zero
  obtain ⟨q, hq⟩ := (X_sub_C_dvd_sub_C_eval : X - C a ∣ p - C (p.eval a))
  have hqroot : q.IsRoot a := by
    have he := congrArg (fun t : ℝ[X] ↦ t.derivative.eval a) hq
    simpa [IsRoot, derivative_mul, hd] using he.symm
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hqroot
  have heq : p - C (p.eval a) = (X - C a)^2 * r := by rw [hq, hr]; ring
  refine ⟨a, r, heq, ?_⟩
  have hoff : ({a}ᶜ : Set ℝ) ⊆ {x | 0 ≤ r.eval x} := by
    intro x hx
    have hne : x ≠ a := hx
    have he := congrArg (fun t : ℝ[X] ↦ t.eval x) heq
    simp only [eval_sub, eval_C, eval_mul, eval_pow, eval_X] at he
    exact nonneg_of_mul_nonneg_right (he ▸ sub_nonneg.mpr (hmin x)) (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
  exact fun x ↦ closure_minimal hoff (isClosed_le continuous_const r.continuous) ((dense_compl_singleton a) x)

/-- A real univariate polynomial of degree at most 2d that is nonnegative on the line is a
sum of squares of polynomials of degree at most d. -/
private theorem affineSOS (d : ℕ) (p : ℝ[X]) (hdeg : p.natDegree ≤ 2*d)
    (hp : ∀ x, 0 ≤ p.eval x) :
    ∃ m : ℕ, ∃ g : Fin m → ℝ[X], p = ∑ i, (g i)^2 ∧ ∀ i, (g i).natDegree ≤ d := by
  induction d generalizing p with
  | zero =>
    have he := eq_C_of_natDegree_le_zero (by simpa using hdeg)
    have hc : 0 ≤ p.coeff 0 := by rw [coeff_zero_eq_eval_zero]; exact hp 0
    refine ⟨1, fun _ ↦ C √(p.coeff 0), ?_, by simp⟩
    simp only [Fin.sum_univ_one, ← map_pow, Real.sq_sqrt hc]
    exact he
  | succ d ih =>
    obtain ⟨a, r, he, hr⟩ := splitAtMinimum p hp
    have hrdeg : r.natDegree ≤ 2*d := by
      by_cases hz : r = 0
      · simp [hz]
      have h := congrArg natDegree he
      rw [natDegree_sub_C, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero a)) hz,
        natDegree_pow, natDegree_X_sub_C] at h
      omega
    obtain ⟨m, g, hg, hgd⟩ := ih r hrdeg hr
    refine ⟨m+1, Fin.cons (C √(p.eval a)) (fun i ↦ (X - C a) * g i), ?_, ?_⟩
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← map_pow, Real.sq_sqrt (hp a), mul_pow, ← mul_sum]
      rw [← hg, ← he]
      ring
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp
      · change ((X - C a) * g j).natDegree ≤ d + 1
        exact natDegree_mul_le.trans (by rw [natDegree_X_sub_C, add_comm]; exact Nat.add_le_add_right (hgd j) 1)

/-- Rehomogenization restores the original binary form and its degree-controlled squares. -/
theorem binarySOS (d : ℕ) (f : MvPolynomial (Fin 2) ℝ) (hf : f.IsHomogeneous (2*d))
    (hpos : ∀ x, 0 ≤ MvPolynomial.eval x f) :
    ∃ m : ℕ, ∃ g : Fin m → MvPolynomial (Fin 2) ℝ, f = ∑ i, (g i)^2 := by
  let v : Fin 2 → ℝ[X] := ![X, 1]
  let p := MvPolynomial.aeval v f
  have hdeg : p.natDegree ≤ 2*d := by
    simpa using MvPolynomial.aeval_natDegree_le f hf.totalDegree_le v (n := 1) (fun i ↦ by fin_cases i <;> simp [v])
  have hp (x : ℝ) : 0 ≤ p.eval x := by
    change 0 ≤ Polynomial.aeval x (MvPolynomial.aeval v f)
    rw [MvPolynomial.comp_aeval_apply]
    exact hpos _
  obtain ⟨m, g, hg, hgd⟩ := affineSOS d p hdeg hp
  refine ⟨m, fun i ↦ (g i).homogenize d, ?_⟩
  calc
    f = p.homogenize (2*d) := (homogenize_eq_of_isHomogeneous hf rfl).symm
    _ = _ := by
      rw [hg, homogenize_finsetSum, two_mul]
      apply sum_congr rfl
      intro i _
      simpa only [sq] using homogenize_mul (g i) (g i) (hgd i) (hgd i)

end OMA.BinaryForms

theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1.H1 := by
  intro d _ f hf hp
  exact OMA.BinaryForms.binarySOS d f hf hp
