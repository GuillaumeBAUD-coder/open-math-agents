import OMAStatements.S_oeis_a027481

-- Problem: A027481: Second subdiagonal of triangle A027477, constructed from the Stirling numbers of the first kind.
-- Upstream: formal-conjectures statements/oeis-a027481.lean:0 (declaration OMA.S_oeis_a027481.main)
-- Original Lean proof: @agchua.
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: A(i, j) = 0 for j > i, so in T(n, n-2) = n!^2 Sum_k A(n,k) A(k,n-2) only the three
-- terms with n-2 <= k <= n remain. With |s(i,i)| = 1, |s(i+1,i)| = C(i+1,2) and
-- |s(i+2,i)| = (i+2)(i+1)i(3i+5)/24 (induction on the Stirling recurrence) this gives
-- a(m+3) = P(m) for an explicit polynomial P of degree 6. Then (1 - x)^7 annihilates P (a ring
-- identity), which gives the recurrence, and the g.f. follows by comparing coefficients.

namespace P1A027481

open OMA.S_oeis_a027481

theorem Azero (i k : ℕ) (h : i < k) : A i k = 0 := by
  show (Nat.stirlingFirst i k : ℚ) / (i.factorial : ℚ) = 0
  rw [Nat.stirlingFirst_eq_zero_of_lt h, Nat.cast_zero, zero_div]

theorem sum3 (m : ℕ) (g : ℕ → ℚ) (hg : ∀ l, l ≤ m → g l = 0) :
    ∑ l ∈ Finset.Icc 1 (m + 3), g l = g (m + 1) + g (m + 2) + g (m + 3) := by
  have hz : ∑ l ∈ Finset.Icc 1 m, g l = 0 :=
    Finset.sum_eq_zero fun l hl ↦ hg l (Finset.mem_Icc.mp hl).2
  rw [Finset.sum_Icc_succ_top (Nat.succ_pos (m + 2)),
    Finset.sum_Icc_succ_top (Nat.succ_pos (m + 1)),
    Finset.sum_Icc_succ_top (Nat.succ_pos m), hz, zero_add]

theorem s1 (n : ℕ) : (Nat.stirlingFirst (n + 1) n : ℚ) = ((n : ℚ) + 1) * (n : ℚ) / 2 := by
  rw [Nat.stirlingFirst_succ_self_left, Nat.cast_choose_two, Nat.cast_add_one]
  ring

theorem s2 (n : ℕ) : (Nat.stirlingFirst (n + 2) n : ℚ) =
    ((n : ℚ) + 2) * ((n : ℚ) + 1) * (n : ℚ) * (3 * (n : ℚ) + 5) / 24 := by
  induction n with
  | zero => norm_num [Nat.stirlingFirst]
  | succ k ih =>
    rw [Nat.stirlingFirst_succ_succ]
    push_cast
    rw [s1, ih]
    push_cast
    ring

/-- a(m+3) as an explicit polynomial in m. -/
def P (m : ℕ) : ℚ :=
  ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * (3 * (m : ℚ) + 8) / 24 *
      (1 + ((m : ℚ) + 3) * ((m : ℚ) + 2)) +
    ((m : ℚ) + 3) * ((m : ℚ) + 2) / 2 * (((m : ℚ) + 2) * ((m : ℚ) + 1) / 2) * ((m : ℚ) + 3)

theorem a_closed (m : ℕ) : a (m + 3) = P m := by
  have hz : ∀ l, l ≤ m → A (m + 3) l * A l (m + 1) = 0 := by
    intro l hl
    rw [Azero l (m + 1) (by omega), mul_zero]
  have fac (j : ℕ) : ((j + 1).factorial : ℚ) = ((j : ℚ) + 1) * (j.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ j
  have hF : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  unfold a T
  rw [show m + 3 - 2 = m + 1 by omega, sum3 m _ hz]
  unfold A
  rw [s1 (m + 1), s1 (m + 2), s2 (m + 1), fac (m + 2), fac (m + 1), fac m]
  simp only [P, Nat.stirlingFirst_self, Nat.cast_one]
  push_cast
  field_simp
  ring

theorem Prec (k : ℕ) : P (k + 7) - 7 * P (k + 6) + 21 * P (k + 5) - 35 * P (k + 4) +
    35 * P (k + 3) - 21 * P (k + 2) + 7 * P (k + 1) - P k = 0 := by
  unfold P
  push_cast
  ring

theorem Pq (n : ℕ) (hn : 7 ≤ n) : P n - 7 * P (n - 1) + 21 * P (n - 2) - 35 * P (n - 3) +
    35 * P (n - 4) - 21 * P (n - 5) + 7 * P (n - 6) - P (n - 7) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simpa [Nat.add_sub_assoc] using Prec k

open PowerSeries in
theorem gf : mk P * (1 - X) ^ 7 = (23 : PowerSeries ℚ) + 54 * X + 13 * X ^ 2 := by
  let F := mk P
  have e : F * (1 - X) ^ 7 =
      F - C 7 * (F * X ^ 1) + C 21 * (F * X ^ 2) - C 35 * (F * X ^ 3) +
        C 35 * (F * X ^ 4) - C 21 * (F * X ^ 5) + C 7 * (F * X ^ 6) - F * X ^ 7 := by
    simp only [map_ofNat]
    ring
  have e2 : (23 : PowerSeries ℚ) + 54 * X + 13 * X ^ 2 = C 23 + C 54 * X ^ 1 + C 13 * X ^ 2 := by
    simp only [map_ofNat, pow_one]
  change F * _ = _
  rw [e, e2]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C, F]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> norm_num [P]
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [Pq n hn]

end P1A027481

open OMA.S_oeis_a027481 P1A027481 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a027481.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have h (j : ℕ) (hj : j ≤ 7) : a (m + 10 - j) = P (m + (7 - j)) := by
      rw [show m + 10 - j = m + (7 - j) + 3 by omega, a_closed]
    rw [show a (m + 10) = P (m + 7) from a_closed (m + 7)]
    simp (disch := omega) only [h, Nat.reduceSub, Nat.add_zero]
    linear_combination Prec m
  · rw [congrArg mk (funext a_closed), show (X - 1 : PowerSeries ℚ) ^ 7 = -((1 - X) ^ 7) by ring,
      mul_neg, mul_assoc, gf]
    ring
