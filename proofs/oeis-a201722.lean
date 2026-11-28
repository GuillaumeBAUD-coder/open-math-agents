import OMAStatements.S_oeis_a201722

namespace OMA.S_oeis_a201722

open PowerSeries





/-- Number of columns of length m that pass the scan from the state (p, r). -/
def N (p : Fin 5) (r m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 5, if ok p r (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 5) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 5, f (List.ofFn x) =
      ∑ c : Fin 5, ∑ y : Fin m → Fin 5, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

theorem N_zero (p : Fin 5) (r : ℕ) : N p r 0 = if r ≠ p.val then 1 else 0 := by
  by_cases h : r = p.val <;> simp [N, ok, h]

theorem N_succ (p : Fin 5) (r m : ℕ) :
    N p r (m + 1) = ∑ c : Fin 5, if p ≤ c then (if c = p then
      (if r + 1 ≠ p.val then N c 1 m else 0) else (if r ≠ p.val then N c 0 m else 0)) else 0 := by
  have h := sum_cons m (fun l => if ok p r l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hpc : p ≤ c
  · by_cases hc : c = p
    · subst hc
      by_cases hr : r + 1 = c.val <;> simp [ok, hr]
    · by_cases hr : r = p.val <;> simp [ok, hpc, hc, hr]
  · simp [ok, hpc]

/-- Counts by class: z0 from (0, 0), z1 from (0, 1), o0 from (1, 0), w0 from (2, 0), t from
(2, 1), (3, 0) and (3, 1), f from (4, 0) and (4, 1). -/
structure S where
  z0 : ℕ
  z1 : ℕ
  o0 : ℕ
  w0 : ℕ
  t : ℕ
  f : ℕ

def st : ℕ → S
  | 0 => ⟨0, 1, 1, 1, 1, 1⟩
  | m + 1 =>
    let s := st m
    ⟨s.z1, s.z1 + s.o0 + s.w0 + s.t + s.f, s.w0 + s.t + s.f, 2 * s.t + s.f, s.t + s.f, s.f⟩

theorem N_eq (m : ℕ) :
    N 0 0 m = (st m).z0 ∧ N 0 1 m = (st m).z1 ∧ N 1 0 m = (st m).o0 ∧ N 2 0 m = (st m).w0 ∧
      N 2 1 m = (st m).t ∧ (∀ r, r ≤ 1 → N 3 r m = (st m).t) ∧
      (∀ r, r ≤ 1 → N 4 r m = (st m).f) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_⟩ <;> simp [N_zero, st]
    · omega
    · omega
  | succ m ih =>
    obtain ⟨h00, h01, h10, h20, h21, h3, h4⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_⟩
    · rw [N_succ]; simp [Fin.sum_univ_five, h01, st]
    · rw [N_succ]; simp [Fin.sum_univ_five, h01, h10, h20, h3 0 (by omega), h4 0 (by omega), st]
    · rw [N_succ]; simp [Fin.sum_univ_five, h20, h3 0 (by omega), h4 0 (by omega), st]
    · rw [N_succ]; simp [Fin.sum_univ_five, h21, h3 0 (by omega), h4 0 (by omega), st]; ring
    · rw [N_succ]; simp [Fin.sum_univ_five, h3 0 (by omega), h4 0 (by omega), st]
    · rw [N_succ]
      interval_cases r <;> simp [Fin.sum_univ_five, h3 1 (by omega), h4 0 (by omega), st]
    · rw [N_succ]
      interval_cases r <;> simp [Fin.sum_univ_five, h4 1 (by omega), st]

/-- The sum over the first element. -/
def T (m : ℕ) : ℕ := (st m).z0 + (st m).o0 + (st m).w0 + (st m).t + (st m).f

theorem a_succ (n : ℕ) : a (n + 1) = T n := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h, Fin.sum_univ_five]
  have e : ∀ c : Fin 5,
      (∑ y : Fin n → Fin 5, if valid (c :: List.ofFn y) = true then 1 else 0) = N c 0 n :=
    fun c => rfl
  obtain ⟨h00, -, h10, h20, -, h3, h4⟩ := N_eq n
  rw [e 0, e 1, e 2, e 3, e 4, h00, h10, h20, h3 0 (by omega), h4 0 (by omega)]
  rfl

theorem T_rec (m : ℕ) :
    (T (m + 6) : ℤ) = 3 * T (m + 5) - 3 * T (m + 4) + T (m + 3) := by
  simp only [T, st]
  push_cast
  ring

theorem a_vals : a 1 = 4 ∧ a 2 = 10 ∧ a 3 = 20 ∧ a 4 = 35 ∧ a 5 = 56 ∧ a 6 = 83 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rcases Nat.lt_or_ge n 7 with h7 | h7
  · obtain rfl : n = 6 := by omega
    obtain ⟨-, -, v3, v4, v5, v6⟩ := a_vals
    simp [v3, v4, v5, v6]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [show m + 7 - 1 = m + 5 + 1 by omega, show m + 7 - 2 = m + 4 + 1 by omega,
      show m + 7 - 3 = m + 3 + 1 by omega, show m + 7 = m + 6 + 1 by omega]
    simp only [a_succ]
    exact T_rec m

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (a n : ℚ) := by simp [gf]

/-- Barker's g.f.: x(4 - 2x + 2x^2 + x^3 + x^4)/(1 - x)^3, in Q[[x]]. -/
theorem gf_eq : gf = X * (4 - 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4) * ((1 - X) ^ 3)⁻¹ := by
  set D : ℚ⟦X⟧ := (1 - X) ^ 3 with hD
  have hden : constantCoeff D ≠ 0 := by rw [hD]; simp
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := a_vals
  have key : gf * D = X * (4 - 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4) := by
    have e : gf * D = gf - C 3 * (gf * X ^ 1) + C 3 * (gf * X ^ 2) - gf * X ^ 3 := by
      rw [hD]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) * (4 - 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4) =
        C 4 * X ^ 1 - C 2 * X ^ 2 + C 2 * X ^ 3 + X ^ 4 + X ^ 5 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> simp [v1, v2, v3, v4, v5] <;> norm_num
    · have hr := recurrence n (by omega)
      have hq : (a n : ℚ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 4 ≤ n by omega, show 5 ≤ n by omega, if_true, show n ≠ 0 by omega,
        show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
        show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, if_false, show n ≠ 4 by omega,
        show n ≠ 5 by omega, coeff_C]
      linarith
  calc gf = gf * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * D) * D⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

/-- Both of Barker's conjectures: the g.f. and the recurrence for n > 5. -/
theorem conjecture :
    gf = X * (4 - 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4) * ((1 - X) ^ 3)⁻¹ ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨gf_eq, recurrence⟩

/-- Controls: a(1..19), the entry's data. -/
example : a 1 = 4 ∧ a 2 = 10 ∧ a 3 = 20 ∧ a 4 = 35 ∧ a 5 = 56 ∧ a 6 = 83 ∧ a 7 = 116 ∧
    a 8 = 155 ∧ a 9 = 200 ∧ a 10 = 251 ∧ a 11 = 308 ∧ a 12 = 371 ∧ a 13 = 440 ∧ a 14 = 515 ∧
    a 15 = 596 ∧ a 16 = 683 ∧ a 17 = 776 ∧ a 18 = 875 ∧ a 19 = 980 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [a_succ] <;> rfl

set_option maxRecDepth 20000 in
/-- Control by direct enumeration of the 625 columns of length 4. -/
example : a 4 = 35 := by decide

end OMA.S_oeis_a201722

theorem OMA.solution : type_of% @OMA.S_oeis_a201722.main :=
  OMA.S_oeis_a201722.conjecture
