import OMAStatements.S_oeis_a201347

namespace OMA.S_oeis_a201347

open PowerSeries





/-- The test applied to the next row `w` in the state (r, t, s0, s1). -/
def step (r : Fin 2 × Fin 2) (t s0 s1 : Bool) (w : Fin 2 × Fin 2) : Bool :=
  decide (r.1 < w.1 ∨ (r.1 = w.1 ∧ r.2 ≤ w.2)) && (t || decide (w.1 ≤ w.2)) &&
    (s0 || decide (w.1 = r.1)) && (s1 || decide (w.2 = r.2))

/-- Number of row lists of length m that pass the scan from the state (r, t, s0, s1). -/
def N (r : Fin 2 × Fin 2) (t s0 s1 : Bool) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 2 × Fin 2, if ok r t s0 s1 (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 2 × Fin 2) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 2 × Fin 2, f (List.ofFn x) =
      ∑ c : Fin 2 × Fin 2, ∑ y : Fin m → Fin 2 × Fin 2, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 2 × Fin 2).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

theorem N_zero (r : Fin 2 × Fin 2) (t s0 s1 : Bool) :
    N r t s0 s1 0 = if (s0 && s1) = true then 1 else 0 := by
  simp [N, ok]

theorem N_succ (r : Fin 2 × Fin 2) (t s0 s1 : Bool) (m : ℕ) :
    N r t s0 s1 (m + 1) = ∑ w : Fin 2 × Fin 2, if step r t s0 s1 w = true then
      N w (t || decide (w.1 < w.2)) (decide (w.1 = w.2) || decide (w.1 = r.1))
        (decide (w.2 = w.1) || decide (w.2 = r.2)) m else 0 := by
  have h := sum_cons m (fun l => if ok r t s0 s1 l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hc : step r t s0 s1 w = true
  · rw [if_pos hc]
    apply Finset.sum_congr rfl
    intro y _
    have e1 : ok r t s0 s1 (w :: List.ofFn y) = ok w (t || decide (w.1 < w.2))
        (decide (w.1 = w.2) || decide (w.1 = r.1)) (decide (w.2 = w.1) || decide (w.2 = r.2))
        (List.ofFn y) := by
      show (step r t s0 s1 w && _) = _
      rw [hc, Bool.true_and]
    rw [e1]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro y _
    have hc' := Bool.eq_false_iff.mpr hc
    have e1 : ok r t s0 s1 (w :: List.ofFn y) = false := by
      show (step r t s0 s1 w && _) = false
      rw [hc', Bool.false_and]
    simp [e1]

/-- Counts by class of states (classes found by comparing count sequences). -/
structure S where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  c5 : ℕ
  c6 : ℕ
  c7 : ℕ
  c8 : ℕ
  c9 : ℕ
  c10 : ℕ
  c11 : ℕ
  c12 : ℕ
  c13 : ℕ
  c14 : ℕ
  c15 : ℕ
  c16 : ℕ

def st : ℕ → S
  | 0 => ⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1⟩
  | m + 1 =>
    let s := st m
    ⟨s.c2, s.c2 + s.c8, s.c2 + s.c8 + s.c13, s.c6, s.c6 + s.c8, s.c6 + s.c15,
      s.c6 + s.c8 + s.c13 + s.c15, s.c10, s.c10 + s.c13, s.c10 + s.c13, s.c10 + s.c13 + s.c14, 0,
      s.c13, s.c13, s.c16, s.c13 + s.c16, s.c13 + s.c16⟩

/-- The class count of each state. -/
def Nv (m : ℕ) (r : Fin 2 × Fin 2) (t s0 s1 : Bool) : ℕ :=
  if r = (0, 0) then
    (if t = false then
      (if s0 = false then (if s1 = false then (st m).c0 else (st m).c1)
       else (if s1 = false then (st m).c0 else (st m).c2))
     else
      (if s0 = false then (if s1 = false then (st m).c3 else (st m).c4)
       else (if s1 = false then (st m).c5 else (st m).c6)))
  else if r = (0, 1) then
    (if s0 = false then (st m).c7
     else (if s1 = false then (st m).c8 else (if t = false then (st m).c9 else (st m).c10)))
  else if r = (1, 0) then
    (if t = false then
      (if s1 = false then (st m).c11 else (if s0 = false then (st m).c12 else (st m).c13))
     else (if s1 = false then (st m).c14 else (if s0 = false then (st m).c15 else (st m).c16)))
  else
    (if s0 = true ∧ s1 = true then (st m).c13 else (st m).c12)

set_option maxHeartbeats 4000000 in
theorem N_eq (m : ℕ) : ∀ (r : Fin 2 × Fin 2) (t s0 s1 : Bool), N r t s0 s1 m = Nv m r t s0 s1 := by
  induction m with
  | zero =>
    intro r t s0 s1
    obtain ⟨r1, r2⟩ := r
    fin_cases r1 <;> fin_cases r2 <;> cases t <;> cases s0 <;> cases s1 <;> simp [N_zero, Nv, st]
  | succ m ih =>
    intro r t s0 s1
    rw [N_succ]
    simp only [ih]
    obtain ⟨r1, r2⟩ := r
    fin_cases r1 <;> fin_cases r2 <;> cases t <;> cases s0 <;> cases s1 <;>
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, step, Nv, st] <;> ring

/-- The total over the first row: (0, 0), (0, 1) and (1, 1). -/
def T (m : ℕ) : ℕ := (st m).c2 + (st m).c7 + (st m).c13

theorem a_succ (n : ℕ) : a (n + 1) = T n := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h]
  have e : ∀ w : Fin 2 × Fin 2,
      (∑ y : Fin n → Fin 2 × Fin 2, if valid (w :: List.ofFn y) = true then 1 else 0) =
        if w.1 ≤ w.2 then N w (decide (w.1 < w.2)) (decide (w.1 = w.2)) (decide (w.1 = w.2)) n
        else 0 := by
    intro w
    by_cases hw : w.1 ≤ w.2
    · rw [if_pos hw]
      apply Finset.sum_congr rfl
      intro y _
      have e1 : valid (w :: List.ofFn y) =
          ok w (decide (w.1 < w.2)) (decide (w.1 = w.2)) (decide (w.1 = w.2)) (List.ofFn y) := by
        show (decide (w.1 ≤ w.2) && _) = _
        rw [decide_eq_true hw, Bool.true_and]
      rw [e1]
    · rw [if_neg hw]
      apply Finset.sum_eq_zero
      intro y _
      have e1 : valid (w :: List.ofFn y) = false := by
        show (decide (w.1 ≤ w.2) && _) = false
        rw [decide_eq_false hw, Bool.false_and]
      simp [e1]
  simp only [e, N_eq]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Nv, T]

theorem T_rec (m : ℕ) :
    (T (m + 5) : ℤ) = 4 * T (m + 4) - 6 * T (m + 3) + 4 * T (m + 2) - T (m + 1) := by
  simp only [T, st]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 4 + 1 by omega, show m + 6 - 2 = m + 3 + 1 by omega,
    show m + 6 - 3 = m + 2 + 1 by omega, show m + 6 - 4 = m + 1 + 1 by omega,
    show m + 6 = m + 5 + 1 by omega]
  simp only [a_succ]
  exact T_rec m

theorem a_vals : a 1 = 2 ∧ a 2 = 4 ∧ a 3 = 8 ∧ a 4 = 14 ∧ a 5 = 23 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (a n : ℚ) := by simp [gf]

/-- Barker's g.f.: x(2 - 4x + 4x^2 - 2x^3 + x^4)/(1 - x)^4, in Q[[x]]. -/
theorem gf_eq : gf = X * (2 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 + X ^ 4) * ((1 - X) ^ 4)⁻¹ := by
  set D : ℚ⟦X⟧ := (1 - X) ^ 4 with hD
  have hden : constantCoeff D ≠ 0 := by rw [hD]; simp
  obtain ⟨v1, v2, v3, v4, v5⟩ := a_vals
  have key : gf * D = X * (2 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 + X ^ 4) := by
    have e : gf * D = gf - C 4 * (gf * X ^ 1) + C 6 * (gf * X ^ 2) - C 4 * (gf * X ^ 3) +
        gf * X ^ 4 := by
      rw [hD]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) * (2 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 + X ^ 4) =
        C 2 * X ^ 1 - C 4 * X ^ 2 + C 4 * X ^ 3 - C 2 * X ^ 4 + X ^ 5 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> simp [v1, v2, v3, v4, v5] <;> norm_num
    · have hr := recurrence n (by omega)
      have hq : (a n : ℚ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 4 ≤ n by omega, show 5 ≤ n by omega, if_true, show n ≠ 0 by omega,
        show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
        show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, if_false, show n ≠ 5 by omega,
        coeff_C]
      linarith
  calc gf = gf * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * D) * D⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

/-- Both of Barker's conjectures: the g.f. and the recurrence for n > 5. -/
theorem conjecture :
    gf = X * (2 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 + X ^ 4) * ((1 - X) ^ 4)⁻¹ ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) :=
  ⟨gf_eq, recurrence⟩

/-- Controls: a(1..19), the entry's data. -/
example : a 1 = 2 ∧ a 2 = 4 ∧ a 3 = 8 ∧ a 4 = 14 ∧ a 5 = 23 ∧ a 6 = 36 ∧ a 7 = 54 ∧ a 8 = 78 ∧
    a 9 = 109 ∧ a 10 = 148 ∧ a 11 = 196 ∧ a 12 = 254 ∧ a 13 = 323 ∧ a 14 = 404 ∧ a 15 = 498 ∧
    a 16 = 606 ∧ a 17 = 729 ∧ a 18 = 868 ∧ a 19 = 1024 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [a_succ] <;> rfl

set_option maxRecDepth 20000 in
/-- Control by direct enumeration of the 256 arrays with four rows. -/
example : a 4 = 14 := by decide

end OMA.S_oeis_a201347

theorem OMA.solution : type_of% @OMA.S_oeis_a201347.main :=
  OMA.S_oeis_a201347.conjecture
