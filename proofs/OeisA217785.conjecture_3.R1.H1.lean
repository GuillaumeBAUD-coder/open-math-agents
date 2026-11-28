import OMAReductions.R_OeisA217785_conjecture_3_R1
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! The reciprocal polynomial shifted by one satisfies Eisenstein at the prime n+2. -/

open Polynomial

namespace OMA.A217785

-- The reciprocal polynomial has coefficients n+1, n, ..., 1.
noncomputable def reciprocal : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => C ((n : ℤ) + 2) + X * reciprocal n

lemma coeff_reciprocal (n k : ℕ) :
    (reciprocal n).coeff k = if k ≤ n then (n : ℤ) + 1 - k else 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp [reciprocal, coeff_one]
  | succ n ih =>
    cases k with
    | zero =>
      simp [reciprocal]
      ring
    | succ k =>
      rw [reciprocal, coeff_add, coeff_C_succ, coeff_X_mul, zero_add, ih]
      simp only [Nat.succ_le_succ_iff, Nat.cast_succ]
      split <;> ring

lemma coeff_original (n k : ℕ) :
    (OeisA217785.polyS n).coeff k = if k ≤ n then (k : ℤ) + 1 else 0 := by
  classical
  simp only [OeisA217785.polyS, finsetSum_coeff, coeff_C_mul_X_pow,
    Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]

lemma original_degree (n : ℕ) : (OeisA217785.polyS n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    simp [coeff_original, not_le_of_gt hk]
  · rw [coeff_original, if_pos le_rfl]
    positivity

lemma reverse_original (n : ℕ) : (OeisA217785.polyS n).reverse = reciprocal n := by
  ext k
  rw [coeff_reverse, original_degree, coeff_reciprocal]
  by_cases hk : k ≤ n
  · rw [revAt_le hk, coeff_original, if_pos (Nat.sub_le ..), if_pos hk, Nat.cast_sub hk]
    ring
  · rw [revAt_eq_self_of_lt (lt_of_not_ge hk), coeff_original, if_neg hk, if_neg hk]

-- Shifting the reciprocal polynomial by one yields the shifted binomial row.
lemma coeff_shifted (n k : ℕ) :
    ((reciprocal n).comp (X + 1)).coeff k = ((n + 2).choose (k + 2) : ℤ) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => norm_num [reciprocal]
    | succ k =>
      simp [reciprocal, coeff_one, Nat.choose_eq_zero_of_lt (show 2 < k.succ + 2 by omega)]
  | succ n ih =>
    rw [reciprocal, add_comp, C_comp, mul_comp, X_comp, add_mul, one_mul]
    cases k with
    | zero =>
      simp only [coeff_add, coeff_X_mul_zero, coeff_C_zero, zero_add, ih]
      change (n : ℤ) + 2 + ((n + 2).choose 2 : ℤ) = ((n + 2 + 1).choose (1 + 1) : ℤ)
      rw [Nat.choose_succ_succ (n + 2) 1, Nat.choose_one_right, Nat.cast_add, Nat.cast_add, Nat.cast_ofNat]
    | succ k =>
      simp only [coeff_add, coeff_C_succ, coeff_X_mul, zero_add, ih]
      change ((n + 2).choose (k + 2) : ℤ) + ((n + 2).choose (k + 2 + 1) : ℤ) =
        ((n + 2 + 1).choose ((k + 2) + 1) : ℤ)
      rw [Nat.choose_succ_succ (n + 2) (k + 2), Nat.cast_add, add_comm]

lemma shifted_degree (n : ℕ) : ((reciprocal n).comp (X + 1)).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_shifted, Nat.choose_eq_zero_of_lt (by omega : n + 2 < k + 2), Nat.cast_zero]
  · rw [coeff_shifted, Nat.choose_self, Nat.cast_one]
    exact one_ne_zero

lemma square_not_dvd_choose_two (p : ℕ) (hp : 2 < p) : ¬ p ^ 2 ∣ p.choose 2 := by
  have hchoose : 2 * p.choose 2 = p * (p - 1) := by
    have he := Nat.descFactorial_eq_factorial_mul_choose p 2
    rwa [Nat.descFactorial_succ p 1, Nat.descFactorial_one, Nat.factorial_two, mul_comm (p-1) p,
      eq_comm] at he
  rintro ⟨d, hd⟩
  have hcancel : p * (p - 1) = p * (2 * p * d) := by
    rw [← hchoose, hd]
    ring
  have hdvd : p ∣ p - 1 :=
    ⟨2 * d, by
      have he := Nat.eq_of_mul_eq_mul_left (show 0 < p by omega) hcancel
      rw [he]
      ring⟩
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hdvd

lemma shifted_irreducible (n : ℕ) (hn : 1 ≤ n) (hp : (n + 2).Prime) :
    Irreducible ((reciprocal n).comp (X + 1)) := by
  let p : ℤ := (n + 2 : ℕ)
  have hpz : Prime p := Nat.prime_iff_prime_int.mp hp
  have hm : ((reciprocal n).comp (X + 1)).Monic := by
    rw [Monic, leadingCoeff, shifted_degree, coeff_shifted, Nat.choose_self, Nat.cast_one]
  apply irreducible_of_eisenstein_criterion (P := Ideal.span {p})
    ((Ideal.span_singleton_prime hpz.ne_zero).2 hpz)
  · rw [hm.leadingCoeff, Ideal.mem_span_singleton]
    exact hpz.not_isUnit ∘ isUnit_of_dvd_one
  · intro k hk
    rw [coe_lt_degree, shifted_degree] at hk
    rw [coeff_shifted, Ideal.mem_span_singleton]
    change ((n + 2 : ℕ) : ℤ) ∣ _
    exact_mod_cast hp.dvd_choose_self (by omega : k + 2 ≠ 0) (by omega : k + 2 < n + 2)
  · apply natDegree_pos_iff_degree_pos.mp
    rw [shifted_degree]
    omega
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, coeff_shifted]
    change ¬ ((n + 2 : ℕ) : ℤ) ^ 2 ∣ _
    exact_mod_cast square_not_dvd_choose_two (n + 2) (by omega)
  · exact hm.isPrimitive

lemma irreducible_of_reverse_int {f : Polynomial ℤ} (h0 : f.coeff 0 = 1)
    (hi : Irreducible f.reverse) : Irreducible f := by
  have reverse_unit_of (g : Polynomial ℤ) (hg : IsUnit (g.coeff 0)) :
      IsUnit g.reverse → IsUnit g := by
    intro hr
    have hz := natDegree_eq_zero_of_isUnit hr
    have ht : g.natTrailingDegree = 0 := natTrailingDegree_eq_zero_of_constantCoeff_ne_zero hg.ne_zero
    have hd : g.natDegree = 0 := by
      rw [natDegree_eq_reverse_natDegree_add_natTrailingDegree, hz, ht, zero_add]
    rw [eq_C_of_natDegree_eq_zero hd]
    exact isUnit_C.mpr hg
  have unit_reverse (g : Polynomial ℤ) (hg : IsUnit g) : IsUnit g.reverse := by
    have he := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hg)
    rw [he, reverse_C]
    exact isUnit_C.mpr (hg.map constantCoeff)
  refine ⟨fun hu => hi.not_isUnit (unit_reverse f hu), ?_⟩
  intro g h hmul
  have hz : g.coeff 0 * h.coeff 0 = 1 := by rw [← mul_coeff_zero, ← hmul, h0]
  have he : f.reverse = g.reverse * h.reverse := by rw [hmul, reverse_mul_of_domain]
  exact (hi.isUnit_or_isUnit he).imp
    (reverse_unit_of g (.of_mul_eq_one _ hz))
    (reverse_unit_of h (.of_mul_eq_one _ ((mul_comm _ _).trans hz)))

end OMA.A217785

theorem OMA.solution : OMA.R_OeisA217785_conjecture_3_R1.H1 := by
  intro n hn hp
  have h0 : (OeisA217785.polyS n).coeff 0 = 1 := by simp [OMA.A217785.coeff_original]
  have hPrimitive : (OeisA217785.polyS n).IsPrimitive := by
    rintro r ⟨q, hq⟩
    exact .of_mul_eq_one (q.coeff 0) (by rwa [← coeff_C_mul, ← hq])
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hPrimitive).mp
  apply OMA.A217785.irreducible_of_reverse_int h0
  rw [OMA.A217785.reverse_original]
  apply (MulEquiv.irreducible_iff (taylorEquiv (1 : ℤ))).mp
  change Irreducible ((OMA.A217785.reciprocal n).comp (X + C (1 : ℤ)))
  rw [C_1]
  exact OMA.A217785.shifted_irreducible n hn hp
