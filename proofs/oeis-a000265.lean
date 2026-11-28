import OMAStatements.S_oeis_a000265

-- Problem: A000265: Remove all factors of 2 from n; or largest odd divisor of n; or odd part of n.
-- Upstream: formal-conjectures statements/oeis-a000265.lean:0 (declaration OMA.S_oeis_a000265.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Proof_oeis_a000265

open OMA.S_oeis_a000265

private lemma a_two_mul (m : ℕ) (hm : 0 < m) : a (2 * m) = a m := by
  rw [a, a, Nat.factorization_mul two_ne_zero hm.ne', Finsupp.add_apply,
    Nat.prime_two.factorization_self, add_comm, pow_succ', Nat.mul_div_mul_left _ _ two_pos]

private lemma a_two_mul_add_one (m : ℕ) : a (2 * m + 1) = 2 * m + 1 := by
  simp [a, Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 2 * m + 1)]

private lemma sum_a_Icc (i : ℕ) :
    ∑ j ∈ Finset.Icc ((i + 1) / 2) i, a (j + 1) = ((i + 2) / 2) ^ 2 := by
  induction i with
  | zero => simp [a_two_mul_add_one 0]
  | succ i ih =>
    obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [show (2 * r + 1) / 2 = r by omega, ← Finset.insert_Icc_add_one_left_eq_Icc
        (by omega : r ≤ 2 * r), Finset.sum_insert (by simp)] at ih
      rw [show (2 * r + 1 + 1) / 2 = r + 1 by omega, show (2 * r + 1 + 2) / 2 = (2 * r + 2) / 2 by omega,
        Finset.sum_Icc_succ_top (by omega), ← ih, show 2 * r + 1 + 1 = 2 * (r + 1) by ring,
        a_two_mul _ r.succ_pos, add_comm]
    · rw [show (2 * r + 1 + 1 + 1) / 2 = (2 * r + 1 + 1) / 2 by omega, Finset.sum_Icc_succ_top (by omega),
        ih, show 2 * r + 1 + 1 + 1 = 2 * (r + 1) + 1 by ring, a_two_mul_add_one,
        show (2 * (r + 1) + 1) / 2 = r + 1 by omega, show (2 * r + 1 + 1 + 2) / 2 = r + 2 by omega]
      ring

private lemma t_det_ne_zero (N : ℕ) : (t N).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular (t N) fun i j (h : i < j) => if_neg (by omega)]
  exact Finset.prod_ne_zero_iff.2 fun i _ => by
    simp only [t, le_refl, true_and, if_pos (by omega : (i : ℕ) ≤ 2 * i)]
    exact one_div_ne_zero (Nat.cast_ne_zero.2 (by omega))

private lemma t_mulVec_a (N : ℕ) :
    (t N).mulVec (fun j : Fin N => (a (j.val + 1) : ℚ)) =
      fun i : Fin N => (((i.val + 2) / 2 : ℕ) : ℚ) := by
  ext i
  rw [Matrix.mulVec, dotProduct]
  have hsum :
      ∑ j : Fin N, t N i j * (a (j.val + 1) : ℚ) =
        ∑ j ∈ Finset.range N,
          if j ≤ i.val ∧ i.val ≤ 2 * j then
            (1 / (((i.val + 2) / 2 : ℕ) : ℚ)) * (a (j + 1) : ℚ)
          else 0 := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjN : j < N := Finset.mem_range.mp hj
    simp only [hjN, dif_pos, t]
    split_ifs <;> simp
  rw [hsum, ← Finset.sum_filter]
  have hfilter :
      (Finset.range N).filter (fun j => j ≤ i.val ∧ i.val ≤ 2 * j) =
        Finset.Icc ((i.val + 1) / 2) i.val := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    have hiN : i.val < N := i.isLt
    omega
  rw [hfilter, ← Finset.mul_sum]
  have hcast :
      (∑ j ∈ Finset.Icc ((i.val + 1) / 2) i.val, (a (j + 1) : ℚ)) =
        ((((i.val + 2) / 2 : ℕ) : ℚ)) ^ 2 := by
    exact_mod_cast sum_a_Icc i.val
  rw [hcast]
  have hne : ((((i.val + 2) / 2 : ℕ) : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hne]

private lemma main_proof : ∀ n : ℕ,
    (a (n + 1) : ℚ) = ∑ k ∈ Finset.range (n + 1), A127793 n k * (((k + 2) / 2 : ℕ) : ℚ) := by
  intro n
  let w : Fin (n + 1) → ℚ := fun j => (a (j.val + 1) : ℚ)
  let v : Fin (n + 1) → ℚ := fun i => (((i.val + 2) / 2 : ℕ) : ℚ)
  have hunit : IsUnit (t (n + 1)).det := isUnit_iff_ne_zero.mpr (t_det_ne_zero (n + 1))
  have hmul : (t (n + 1))⁻¹ * t (n + 1) = 1 := Matrix.nonsing_inv_mul (t (n + 1)) hunit
  have hvec : (t (n + 1))⁻¹.mulVec v = w := by
    have hv : (t (n + 1)).mulVec w = v := t_mulVec_a (n + 1)
    rw [← hv, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  have hentry := congrFun hvec ⟨n, Nat.lt_succ_self n⟩
  have hEq : (a (n + 1) : ℚ) = ((t (n + 1))⁻¹.mulVec v) ⟨n, Nat.lt_succ_self n⟩ := hentry.symm
  rw [hEq, Matrix.mulVec, dotProduct, Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k < n + 1 := Finset.mem_range.mp hk
  have hle : k ≤ n := Nat.lt_succ_iff.mp hkn
  simp [hkn, A127793, hle, v]

end OMA.Proof_oeis_a000265

theorem OMA.solution : type_of% @OMA.S_oeis_a000265.main :=
  OMA.Proof_oeis_a000265.main_proof
