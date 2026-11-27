import OMAReductions.R_OeisA217785_conjecture_3_R1
import Mathlib

/-! With p = n+2 prime, translation by one makes the polynomial
Eisenstein at p. The coefficient identity follows by Pascal's rule. -/
open Polynomial OeisA217785

namespace OMA.Translated

lemma coeff_shift (n j : ℕ) :
    (taylor 1 (polyS n)).coeff j = ((j+1) * (n+2).choose (j+2) : ℕ) := by
  induction n with
  | zero =>
    cases j with
    | zero => norm_num [polyS,taylor_apply]
    | succ j =>
      have hz : (2:ℕ).choose (j+1+2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [polyS,taylor_apply,hz,coeff_one]
  | succ n ih =>
    have addTerm : polyS (n+1) = polyS n + C ((n:ℤ)+2) * X^(n+1) := by
      simp [polyS, Finset.sum_range_succ _ (n+1), Nat.cast_add]; ring
    rw [addTerm, map_add, coeff_add, ih, taylor_mul, taylor_C, taylor_apply, pow_comp, X_comp, C_1,
      coeff_C_mul, coeff_X_add_one_pow]
    have ident := Nat.add_one_mul_choose_eq (n+1) j
    rw [show n.succ+2 = (n+2)+1 by omega, Nat.choose_succ_succ]
    push_cast
    exact_mod_cast (show (j+1)*(n+2).choose (j+2) + (n+2)*(n+1).choose j =
      (j+1)*((n+2).choose (j+1)+(n+2).choose (j+2)) by nlinarith)

end OMA.Translated

namespace OMA.Translated

lemma eval_zero_polyS (n : ℕ) : eval 0 (polyS n) = 1 := by
  simp [polyS, eval_finsetSum, Finset.sum_range_succ']

lemma primitive_eval_one {f : Polynomial ℤ} {x : ℤ} (h : eval x f = 1) : f.IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro a ha
  apply isUnit_of_dvd_one
  simpa [h] using (eval_dvd (x := x) ha)

end OMA.Translated

theorem OMA.solution : OMA.R_OeisA217785_conjecture_3_R1.H1 := by
  intro n hn hp
  let q := taylor 1 (polyS n)
  have topcoeff : q.coeff n = (n:ℤ)+1 := by simp [q, OMA.Translated.coeff_shift]
  have deg : q.natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero _ (by rw [topcoeff]; positivity)
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    simp [q, OMA.Translated.coeff_shift, Nat.choose_eq_zero_of_lt (by omega : n+2 < i+2)]
  have prim : (polyS n).IsPrimitive := OMA.Translated.primitive_eval_one (OMA.Translated.eval_zero_polyS n)
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast prim).mp
  apply (MulEquiv.irreducible_iff (taylorEquiv (1:ℤ))).mp
  change Irreducible q
  let p : ℕ := n+2
  have pprime : Prime (p:ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  apply irreducible_of_eisenstein_criterion (Ideal.isPrime_span_singleton_of_prime pprime)
  · rw [leadingCoeff,deg,topcoeff,Ideal.mem_span_singleton]
    exact_mod_cast (Nat.not_dvd_of_pos_of_lt (by omega : 0<n+1) (by omega : n+1<p))
  · intro i hi
    have hlt := coe_lt_degree.mp hi
    rw [deg] at hlt
    rw [Ideal.mem_span_singleton, OMA.Translated.coeff_shift]
    exact_mod_cast (dvd_mul_of_dvd_right (hp.dvd_choose_self (by omega : i+2 ≠ 0) (by omega : i+2<n+2)) (i+1))
  · exact natDegree_pos_iff_degree_pos.mp (by omega)
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, OMA.Translated.coeff_shift]
    simp only [zero_add, one_mul]
    have hpos : 0 < p.choose 2 := Nat.choose_pos (by omega)
    have hlt : p.choose 2 < p^2 := by
      rw [Nat.choose_two_right]
      calc
        _ ≤ p*(p-1) := Nat.div_le_self _ _
        _ < p^2 := by rw [sq]; exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    exact_mod_cast (Nat.not_dvd_of_pos_of_lt hpos hlt)
  · apply OMA.Translated.primitive_eval_one (x := -1)
    simpa [q,taylor_apply,eval_comp] using OMA.Translated.eval_zero_polyS n
