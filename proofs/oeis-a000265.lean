import OMAStatements.S_oeis_a000265
import Mathlib

-- Problem: A000265: Remove all factors of 2 from n; or largest odd divisor of n; or odd part of n.
-- Upstream: formal-conjectures statements/oeis-a000265.lean:0
-- Credit: @caa1982 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

namespace OMAProofA000265

lemma a_odd (m : ℕ) : OMA.S_oeis_a000265.a (2 * m + 1) = 2 * m + 1 := by
  unfold OMA.S_oeis_a000265.a
  rw [Nat.factorization_eq_zero_of_not_dvd (by omega)]
  simp

lemma a_even (m : ℕ) : OMA.S_oeis_a000265.a (2 * m) = OMA.S_oeis_a000265.a m := by
  unfold OMA.S_oeis_a000265.a
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  rw [Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, pow_add, pow_one,
    Nat.mul_div_mul_left _ _ (by norm_num)]

def P (N : ℕ) : ℕ := ∑ j ∈ range N, OMA.S_oeis_a000265.a (j + 1)

lemma P_double (M : ℕ) : P (2 * M) = P M + M ^ 2 := by
  induction M with
  | zero => simp [P]
  | succ M ih =>
    have h1 : P (2 * (M + 1)) = P (2 * M) + OMA.S_oeis_a000265.a (2 * M + 1)
        + OMA.S_oeis_a000265.a (2 * (M + 1)) := by
      simp only [P]
      rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, sum_range_succ, sum_range_succ]
    rw [h1, ih, a_odd, a_even]
    simp only [P]
    rw [sum_range_succ]
    ring

lemma key (k : ℕ) :
    ∑ j ∈ Ico ((k + 1) / 2) (k + 1), OMA.S_oeis_a000265.a (j + 1) = ((k + 2) / 2) ^ 2 := by
  have h := sum_range_add_sum_Ico (fun j => OMA.S_oeis_a000265.a (j + 1))
    (show (k + 1) / 2 ≤ k + 1 by omega)
  change P ((k + 1) / 2) + _ = P (k + 1) at h
  rcases Nat.even_or_odd' k with ⟨M, rfl | rfl⟩
  · have e1 : (2 * M + 1) / 2 = M := by omega
    have e2 : (2 * M + 2) / 2 = M + 1 := by omega
    have h3 : P (2 * M + 1) = P (2 * M) + OMA.S_oeis_a000265.a (2 * M + 1) := by
      simp only [P]; rw [sum_range_succ]
    rw [e1, h3, P_double, a_odd] at h
    rw [e1, e2]
    have : (M + 1) ^ 2 = M ^ 2 + (2 * M + 1) := by ring
    rw [this]
    omega
  · have e1 : (2 * M + 1 + 1) / 2 = M + 1 := by omega
    have e2 : (2 * M + 1 + 2) / 2 = M + 1 := by omega
    rw [e1, show 2 * M + 1 + 1 = 2 * (M + 1) by ring, P_double] at h
    rw [e1, e2, show 2 * M + 1 + 1 = 2 * (M + 1) by ring]
    omega

end OMAProofA000265

open OMAProofA000265 in
theorem OMA.solution : type_of% @OMA.S_oeis_a000265.main := by
  intro n
  set T := OMA.S_oeis_a000265.t (n + 1) with hT
  let v : Fin (n + 1) → ℚ := fun j => (OMA.S_oeis_a000265.a (j + 1) : ℚ)
  let c : Fin (n + 1) → ℚ := fun k => (((k : ℕ) + 2) / 2 : ℕ)
  have hrow : T.mulVec v = c := by
    funext k
    simp only [Matrix.mulVec, dotProduct, hT, OMA.S_oeis_a000265.t, v, c]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      (if j ≤ (k : ℕ) ∧ (k : ℕ) ≤ 2 * j then 1 / ((((k : ℕ) + 2) / 2 : ℕ) : ℚ) else 0)
        * (OMA.S_oeis_a000265.a (j + 1) : ℚ)) (n + 1)]
    have hs : (range (n + 1)).filter (fun j => j ≤ (k : ℕ) ∧ (k : ℕ) ≤ 2 * j)
        = Ico (((k : ℕ) + 1) / 2) ((k : ℕ) + 1) := by
      ext j; simp only [mem_filter, mem_range, mem_Ico]; omega
    simp only [ite_mul, zero_mul]
    rw [← sum_filter, hs, ← mul_sum]
    have hk := key (k : ℕ)
    have hpos : (0 : ℚ) < ((((k : ℕ) + 2) / 2 : ℕ) : ℚ) := by
      exact_mod_cast (show 0 < ((k : ℕ) + 2) / 2 by omega)
    have hk' : ∑ j ∈ Ico (((k : ℕ) + 1) / 2) ((k : ℕ) + 1),
        (OMA.S_oeis_a000265.a (j + 1) : ℚ) = ((((k : ℕ) + 2) / 2 : ℕ) : ℚ) ^ 2 := by
      exact_mod_cast hk
    rw [hk']
    field_simp
  have hdet : IsUnit T.det := by
    rw [Matrix.det_of_isLowerTriangular]
    · rw [isUnit_iff_ne_zero, prod_ne_zero_iff]
      intro i _
      simp only [hT, OMA.S_oeis_a000265.t]
      rw [if_pos ⟨le_refl _, by omega⟩]
      have : (0 : ℚ) < ((((i : ℕ) + 2) / 2 : ℕ) : ℚ) := by
        exact_mod_cast (show 0 < ((i : ℕ) + 2) / 2 by omega)
      positivity
    · intro i j hij
      simp only [hT, OMA.S_oeis_a000265.t]
      rw [if_neg]
      have : (i : ℕ) < j := hij
      omega
  have hv : T⁻¹.mulVec c = v := by
    rw [← hrow, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hdet, Matrix.one_mulVec]
  have h1 := congrFun hv (Fin.last n)
  simp only [v, Fin.val_last] at h1
  rw [← h1]
  simp only [Matrix.mulVec, dotProduct, c]
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    OMA.S_oeis_a000265.A127793 n k * (((k + 2) / 2 : ℕ) : ℚ)) (n + 1)]
  refine sum_congr rfl (fun k _ => ?_)
  have hk : (k : ℕ) ≤ n := by omega
  simp only [OMA.S_oeis_a000265.A127793, dif_pos hk, hT]
  rfl
