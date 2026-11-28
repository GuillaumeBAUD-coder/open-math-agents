import OMAStatements.S_oeis_a233106

namespace OMA.S_oeis_a233106

open PowerSeries





/-- Number of columns of length m that pass the scan from the state (p, s1, s2). -/
def N (p : Fin 6) (s1 s2 : Bool) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 6, if ok p s1 s2 (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 6) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 6, f (List.ofFn x) =
      ∑ c : Fin 6, ∑ y : Fin m → Fin 6, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 6).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

theorem N_zero (p : Fin 6) (s1 s2 : Bool) : N p s1 s2 0 = 1 := by
  simp [N, ok]

theorem N_succ (p : Fin 6) (s1 s2 : Bool) (m : ℕ) :
    N p s1 s2 (m + 1) = ∑ c : Fin 6,
      if (decide (c.val + p.val ≠ 5) && (s1 || !decide (c.val = 2 ∨ c.val = 3 ∨ c.val = 4)) &&
        (s2 || decide (c.val ≠ 3))) = true then
        N c (s1 || decide (c.val = 1)) (s2 || decide (c.val = 2)) m else 0 := by
  have h := sum_cons m (fun l => if ok p s1 s2 l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : (decide (c.val + p.val ≠ 5) && (s1 || !decide (c.val = 2 ∨ c.val = 3 ∨ c.val = 4)) &&
      (s2 || decide (c.val ≠ 3))) = true
  · rw [if_pos hc]
    apply Finset.sum_congr rfl
    intro y _
    simp only [ok, hc, Bool.true_and]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro y _
    have hc' := Bool.eq_false_iff.mpr hc
    have hk : ok p s1 s2 (c :: List.ofFn y) = false := by
      show (_ && ok c _ _ (List.ofFn y)) = false
      rw [hc', Bool.false_and]
    simp [hk]

/-- Counts by class: g0 from (0, false, false), g2 from (p, true, false) with p ≠ 2, 3, g3 from
(p, true, true). -/
def st : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 1, 1)
  | m + 1 => ((st m).1 + (st m).2.1, 3 * (st m).2.1 + (st m).2.2, 5 * (st m).2.2)

theorem N_eq (m : ℕ) :
    N 0 false false m = (st m).1 ∧
      (∀ p : Fin 6, p.val ≠ 2 → p.val ≠ 3 → N p true false m = (st m).2.1) ∧
      (∀ p : Fin 6, N p true true m = (st m).2.2) := by
  induction m with
  | zero => refine ⟨?_, fun p _ _ => ?_, fun p => ?_⟩ <;> rw [N_zero] <;> rfl
  | succ m ih =>
    obtain ⟨h0, h2, h3⟩ := ih
    refine ⟨?_, fun p hp2 hp3 => ?_, fun p => ?_⟩
    · rw [N_succ]
      simp [Fin.sum_univ_succ, h0, h2 1 (by decide) (by decide), st]
    · rw [N_succ]
      fin_cases p <;> simp at hp2 hp3 ⊢ <;>
        simp [Fin.sum_univ_succ, h2 0 (by decide) (by decide), h2 1 (by decide) (by decide),
          h2 4 (by decide) (by decide), h2 5 (by decide) (by decide), h3, st] <;> ring
    · rw [N_succ]
      fin_cases p <;> simp [Fin.sum_univ_succ, h3, st] <;> ring

theorem a_succ (n : ℕ) : a (n + 1) = (st n).1 := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h, Fin.sum_univ_succ]
  simp only [valid]
  simp
  rw [← (N_eq n).1, N, Finset.card_filter]

theorem g0_rec (m : ℕ) :
    ((st (m + 3)).1 : ℤ) = 9 * (st (m + 2)).1 - 23 * (st (m + 1)).1 + 15 * (st m).1 := by
  simp only [st]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℤ) = 9 * a (n - 1) - 23 * a (n - 2) + 15 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 2 + 1 by omega, show m + 4 - 2 = m + 1 + 1 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 = m + 3 + 1 by omega]
  simp only [a_succ]
  exact g0_rec m

theorem a_vals : a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (a n : ℚ) := by simp [gf]

/-- Barker's g.f.: x(1 - 7x + 11x^2)/((1 - x)(1 - 3x)(1 - 5x)), in Q[[x]]. -/
theorem gf_eq : gf = X * (1 - 7 * X + 11 * X ^ 2) * ((1 - X) * (1 - 3 * X) * (1 - 5 * X))⁻¹ := by
  set D : ℚ⟦X⟧ := (1 - X) * (1 - 3 * X) * (1 - 5 * X) with hD
  have hden : constantCoeff D ≠ 0 := by rw [hD]; simp
  obtain ⟨v1, v2, v3⟩ := a_vals
  have key : gf * D = X * (1 - 7 * X + 11 * X ^ 2) := by
    have e : gf * D = gf - C 9 * (gf * X ^ 1) + C 23 * (gf * X ^ 2) - C 15 * (gf * X ^ 3) := by
      rw [hD]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) * (1 - 7 * X + 11 * X ^ 2) = X ^ 1 - C 7 * X ^ 2 + C 11 * X ^ 3 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> simp [v1, v2, v3] <;> norm_num
    · have hr := recurrence n hn
      have hq : (a n : ℚ) = 9 * a (n - 1) - 23 * a (n - 2) + 15 * a (n - 3) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true,
        show n ≠ 0 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
        show n - 3 ≠ 0 by omega, if_false, show n ≠ 1 by omega, coeff_C]
      linarith
  calc gf = gf * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * D) * D⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

theorem closed_int (m : ℕ) :
    ((st m).2.2 : ℤ) = 5 ^ m ∧ 2 * ((st m).2.1 : ℤ) = 5 ^ m + 3 ^ m ∧
      120 * ((st m).1 : ℤ) = 75 + 30 * 3 ^ m + 15 * 5 ^ m := by
  induction m with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> decide
  | succ m ih =>
    obtain ⟨h3, h2, h0⟩ := ih
    simp only [st]
    push_cast
    refine ⟨?_, ?_, ?_⟩
    · rw [h3]; ring
    · linear_combination 3 * h2 + 2 * h3
    · linear_combination h0 + 60 * h2

/-- Barker's closed form, for n >= 1. -/
theorem closed_form (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (75 + 10 * 3 ^ n + 3 * 5 ^ n) / 120 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := (closed_int m).2.2
  rw [← a_succ] at h
  have hq : 120 * (a (m + 1) : ℚ) = 75 + 30 * 3 ^ m + 15 * 5 ^ m := by exact_mod_cast h
  rw [pow_succ, pow_succ]
  linear_combination hq / 120

/-- Both of Barker's conjectures: the g.f. and the closed form. -/
theorem conjecture :
    gf = X * (1 - 7 * X + 11 * X ^ 2) * ((1 - X) * (1 - 3 * X) * (1 - 5 * X))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (75 + 10 * 3 ^ n + 3 * 5 ^ n) / 120 :=
  ⟨gf_eq, closed_form⟩

/-- Controls: a(1..13), the entry's data. -/
example : a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 6 ∧ a 4 = 23 ∧ a 5 = 99 ∧ a 6 = 452 ∧ a 7 = 2136 ∧
    a 8 = 10313 ∧ a 9 = 50469 ∧ a 10 = 249062 ∧ a 11 = 1235466 ∧ a 12 = 6147803 ∧
    a 13 = 30650439 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

/-- Control by direct enumeration of the 216 columns of length 3. -/
example : a 3 = 6 := by decide

end OMA.S_oeis_a233106

theorem OMA.solution : type_of% @OMA.S_oeis_a233106.main :=
  OMA.S_oeis_a233106.conjecture
