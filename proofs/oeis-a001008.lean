import OMAStatements.S_oeis_a001008

open Finset Polynomial
open OMA.S_oeis_a001008

namespace A001008

private def upper (m : ℚ) (n k : ℕ) : ℚ := n + (m - 1) * (k + 1)

private noncomputable def raw (m : ℚ) (n k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k / (k + 1) * Ring.choose (m * (k + 1)) (k + 1) *
    Ring.choose (upper m n k) (n - (k + 1))

private noncomputable def differenceTerm (m : ℚ) (n k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k / (k + 1) * Ring.choose (m * (k + 1)) (k + 1) *
    Ring.choose (upper m n k) (n - k)

private theorem choose_succ (m : ℚ) (k : ℕ) :
    Ring.choose (m * (k + 1)) (k + 1) = m * Ring.choose (m * (k + 1) - 1) k := by
  have he := Ring.choose_smul_choose (m * (k + 1)) (n := k + 1) (k := 1) (by omega)
  rw [Nat.choose_one_right, Ring.choose_one_right, show k + 1 - 1 = k by omega,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at he
  have hk : (k : ℚ) + 1 ≠ 0 := by positivity
  apply (mul_left_cancel₀ hk)
  linear_combination he

private theorem differenceTerm_eval (m : ℚ) (n k : ℕ) (hk : k ≤ n) :
    differenceTerm m n k = (m / (n + 1)) *
      ((-1 : ℚ) ^ k * ((n + 1).choose (k + 1) : ℚ) * Ring.choose (upper m n k) n) := by
  have hs := Ring.choose_smul_choose (upper m n k) (n := n) (k := n - k) (by omega)
  rw [Nat.choose_symm hk, show n - (n - k) = k by omega, nsmul_eq_mul] at hs
  have ht : upper m n k - ((n - k : ℕ) : ℚ) = m * (k + 1) - 1 := by
    rw [upper, Nat.cast_sub hk]
    ring
  rw [ht] at hs
  have hchoose : ((n : ℚ) + 1) * (n.choose k : ℚ) =
    ((n + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  unfold differenceTerm
  rw [choose_succ]
  calc
    (-1 : ℚ) ^ k / (↑k + 1) * (m * Ring.choose (m * (↑k + 1) - 1) k) *
        Ring.choose (upper m n k) (n - k) =
      m * ((-1 : ℚ) ^ k / (↑k + 1)) *
        (Ring.choose (upper m n k) (n - k) * Ring.choose (m * (↑k + 1) - 1) k) := by ring
    _ = _ := by
      rw [← hs]
      have hn : (n : ℚ) + 1 ≠ 0 := by positivity
      have hk' : (k : ℚ) + 1 ≠ 0 := by positivity
      have hr : (n.choose k : ℚ) / ((k : ℚ) + 1) =
          ((n + 1).choose (k + 1) : ℚ) / ((n : ℚ) + 1) :=
        (div_eq_div_iff hk' hn).mpr (by simpa only [mul_comm] using hchoose)
      calc
        _ = m * (-1 : ℚ) ^ k * Ring.choose (upper m n k) n *
            ((n.choose k : ℚ) / ((k : ℚ) + 1)) := by ring
        _ = _ := by rw [hr]; ring

private theorem raw_sub (m : ℚ) (n k : ℕ) (hk : k < n) :
    raw m (n + 1) k - raw m n k = differenceTerm m n k := by
  have htop : upper m (n + 1) k = upper m n k + 1 := by
    simp only [upper, Nat.cast_add, Nat.cast_one]
    ring
  have hidx : n + 1 - (k + 1) = n - (k + 1) + 1 := by omega
  unfold raw differenceTerm
  rw [htop, hidx, Ring.choose_succ_succ, show n - (k + 1) + 1 = n - k by omega]
  ring

private theorem raw_last (m : ℚ) (n : ℕ) : raw m (n + 1) n = differenceTerm m n n := by
  simp [raw, differenceTerm]

private theorem sign_reverse (n k : ℕ) (hk : k ≤ n) :
    (-1 : ℚ) ^ k = (-1 : ℚ) ^ n * (-1 : ℚ) ^ (n - k) := by
  conv_rhs => enter [1, 2]; rw [show n = k + (n - k) by omega]
  rw [pow_add, mul_assoc, ← pow_two, ← pow_mul]
  simp

private theorem polynomial_eval_choose (e : ℕ) (x : ℚ) :
    (C ((e.factorial : ℚ)⁻¹) * descPochhammer ℚ e).eval x = Ring.choose x e := by
  rw [eval_mul, eval_C, ← descPochhammer_map (RingHom.smulOneHom : ℤ →+* ℚ),
    eval_map, eval₂_smulOneHom_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose]
  rw [nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

private theorem alternating_choose (m : ℚ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k *
      ((n + 1).choose (k + 1) : ℚ) * Ring.choose (upper m n k) n = 1 := by
  let q : ℚ[X] := C (n : ℚ) + C (m - 1) * X
  let P : ℚ[X] := (C ((n.factorial : ℚ)⁻¹) * descPochhammer ℚ n).comp q
  have hq : q.natDegree ≤ 1 := by
    unfold q
    apply natDegree_add_le_of_degree_le
    · simp
    · exact (natDegree_mul_le).trans (by rw [natDegree_C, natDegree_X, zero_add])
  have hP : P.natDegree < n + 1 := by
    apply lt_of_le_of_lt natDegree_comp_le
    have hD : (C ((n.factorial : ℚ)⁻¹) * descPochhammer ℚ n).natDegree ≤ n := by
      exact natDegree_mul_le.trans (by simp [descPochhammer_natDegree])
    exact (Nat.mul_le_mul hD hq).trans_lt (by simp)
  have hval (k : ℕ) : P.eval (k : ℚ) = Ring.choose (n + (m - 1) * k) n := by
    dsimp [P]
    rw [eval_comp, polynomial_eval_choose]
    simp [q]
  have hzero := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP) (0 : ℚ)
  rw [fwdDiff_iter_eq_sum_shift] at hzero
  simp only [nsmul_eq_mul, mul_one, zero_add, hval, zsmul_eq_mul, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, Pi.zero_apply] at hzero
  have hp :
      ∑ k ∈ range (n + 1 + 1), (-1 : ℚ) ^ k *
        ((n + 1).choose k : ℚ) * Ring.choose (n + (m - 1) * k) n = 0 := by
    calc
      _ = (-1 : ℚ) ^ (n + 1) *
          ∑ k ∈ range (n + 1 + 1), (-1 : ℚ) ^ (n + 1 - k) *
            ((n + 1).choose k : ℚ) * Ring.choose (n + (m - 1) * k) n := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k hk
        rw [sign_reverse (n + 1) k (by have := mem_range.mp hk; omega)]
        ring
      _ = 0 := by rw [hzero, mul_zero]
  rw [sum_range_succ'] at hp
  have hn : Ring.choose (n : ℚ) n = 1 := by simp [Ring.choose_natCast]
  simp only [Nat.cast_zero, mul_zero, add_zero, Nat.choose_zero_right, Nat.cast_one,
    pow_zero, one_mul, hn] at hp
  have hneg :
      (∑ k ∈ range (n + 1), (-1 : ℚ) ^ (k + 1) *
        ((n + 1).choose (k + 1) : ℚ) * Ring.choose (n + (m - 1) * (↑(k + 1) : ℚ)) n) =
        -(∑ k ∈ range (n + 1), (-1 : ℚ) ^ k *
          ((n + 1).choose (k + 1) : ℚ) * Ring.choose (upper m n k) n) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k _
    simp [upper, pow_succ]
  rw [hneg] at hp
  linarith

private theorem raw_harmonic (m : ℚ) (n : ℕ) :
    ∑ k ∈ range n, raw m n k = m * H n := by
  induction n with
  | zero => simp [H]
  | succ n ih =>
    have step : (∑ k ∈ range (n + 1), raw m (n + 1) k) - (∑ k ∈ range n, raw m n k) =
        ∑ k ∈ range (n + 1), differenceTerm m n k := by
      rw [sum_range_succ, sum_range_succ, raw_last, add_sub_right_comm, ← sum_sub_distrib]
      congr 1
      exact sum_congr rfl fun k hk => raw_sub m n k (mem_range.mp hk)
    have hΔ : (∑ k ∈ range (n + 1), differenceTerm m n k) = m / (n + 1) := by
      calc
        _ = m / (n + 1) * ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k *
            ((n + 1).choose (k + 1) : ℚ) * Ring.choose (upper m n k) n := by
          rw [mul_sum]
          exact sum_congr rfl fun k hk => differenceTerm_eval m n k (by have := mem_range.mp hk; omega)
        _ = _ := by rw [alternating_choose, mul_one]
    rw [ih, hΔ] at step
    change (∑ k ∈ range (n + 1), raw m (n + 1) k) = m * H (n + 1)
    have hH : H (n + 1) = H n + 1 / ((n : ℚ) + 1) := by
      unfold H
      rw [sum_range_succ]
    rw [hH, mul_add, mul_one_div]
    linarith

private theorem exact_sum (m : ℤ) (n : ℕ) : (∑ k ∈ Finset.Icc 1 n,
      ((-1 : ℚ) ^ (k + 1) / k) * Ring.choose ((m * k : ℤ) : ℚ) k *
        Ring.choose ((n + (m - 1) * k : ℤ) : ℚ) (n - k))
    = ∑ k ∈ range n, raw (m : ℚ) n k := by
  classical
  apply sum_bij (fun k _ => k - 1)
  · intro k hk
    have hp := mem_Icc.mp hk
    exact mem_range.mpr (by omega)
  · intro a ha b hb he
    have := (mem_Icc.mp ha).1
    have := (mem_Icc.mp hb).1
    omega
  · intro k hk
    have := mem_range.mp hk
    exact ⟨k + 1, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro k hk
    have hp := (mem_Icc.mp hk).1
    have he : k - 1 + 1 = k := by omega
    have hexp : (-1 : ℚ) ^ (k + 1) = (-1 : ℚ) ^ (k - 1) := by
      rw [show k + 1 = k - 1 + 2 by omega, pow_add]
      norm_num
    simp only [raw, upper, he, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_one,
      Int.cast_natCast, hexp]
    have hc : ((k - 1 : ℕ) : ℚ) + 1 = (k : ℚ) := by
      exact_mod_cast he
    rw [hc]

end A001008

/-- Pascal's identity reduces the change of the binomial sum to a vanishing finite difference. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a001008.main := by
  intro m hm n
  rw [A001008.exact_sum, A001008.raw_harmonic]
  field_simp
