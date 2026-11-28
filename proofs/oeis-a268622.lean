import OMAStatements.S_oeis_a268622

/-!
Proof of the three conjectures for A268622 (n X 2 arrays over 0..2 with at most one horizontally
or vertically adjacent pair totalling two).

Reading the array row by row, the number of pairs totalling two is the badness of the first row
plus a cost accumulated by the following rows (`a268622_pairs`): each new row p below a row q adds
its own badness (`a268622RB`) and the number of columns where q and p total two (`a268622VT`).
`a268622N m q b` counts the sequences of m rows below q of cost at most b, and peeling off the first
row gives a recursion over the nine rows (`a268622_N_succ`). By induction:
* below a row that does not total two, `N m q 0 = 3^m`;
* below a row that totals two, `N (m+1) q 0 = 2 * 3^m`;
* below a row that does not total two, `N (m+1) q 1 = (8m+18) 3^m / 3`.
Six rows do not total two and three do, so a(m+2) = 6 N (m+1) _ 1 + 3 N (m+1) _ 0
= 2 * 3^m * (8m+21), which is the closed form; the recurrence and the generating function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a268622 (pairsTotallingTwo a)

/-- Whether a row (x, y) totals two (1) or not (0). -/
def a268622RB (q : Fin 3 × Fin 3) : ℕ := if (q.1 : ℕ) + (q.2 : ℕ) = 2 then 1 else 0

/-- The number of columns where the row q above the row p totals two. -/
def a268622VT (q p : Fin 3 × Fin 3) : ℕ :=
  (if (q.1 : ℕ) + (p.1 : ℕ) = 2 then 1 else 0) + (if (q.2 : ℕ) + (p.2 : ℕ) = 2 then 1 else 0)

/-- The cost of a sequence of rows placed below the row q (q's own row pair not counted). -/
def a268622Cost : (m : ℕ) → Fin 3 × Fin 3 → (Fin m → Fin 2 → Fin 3) → ℕ
  | 0, _, _ => 0
  | m + 1, q, g => a268622RB (g 0 0, g 0 1) + a268622VT q (g 0 0, g 0 1) +
      a268622Cost m (g 0 0, g 0 1) (Fin.tail g)

theorem a268622_pairs_succ (m : ℕ) (x : Fin (m + 2) → Fin 2 → Fin 3) :
    pairsTotallingTwo (m + 1) x = a268622RB (x 0 0, x 0 1) +
      a268622VT (x 0 0, x 0 1) (x 1 0, x 1 1) + pairsTotallingTwo m (Fin.tail x) := by
  unfold pairsTotallingTwo a268622RB a268622VT
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ, Fin.tail, Fin.castSucc_zero, Fin.succ_zero_eq_one,
    Fin.succ_castSucc, Fin.sum_univ_zero]
  ac_rfl

theorem a268622_pairs (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 3) :
    pairsTotallingTwo m x = a268622RB (x 0 0, x 0 1) + a268622Cost m (x 0 0, x 0 1) (Fin.tail x) := by
  induction m with
  | zero =>
    unfold pairsTotallingTwo a268622RB
    simp only [Finset.card_filter, Finset.univ_eq_empty, Finset.sum_empty, a268622Cost]
    rfl
  | succ m ih =>
    rw [a268622_pairs_succ, ih]
    simp only [a268622Cost, Fin.tail, Fin.succ_zero_eq_one]
    ring

/-- The number of sequences of `m` rows below the row `q` with cost at most `b`. -/
def a268622N (m : ℕ) (q : Fin 3 × Fin 3) (b : ℕ) : ℕ :=
  ∑ g : Fin m → Fin 2 → Fin 3, if a268622Cost m q g ≤ b then 1 else 0

theorem a268622_N_zero (q : Fin 3 × Fin 3) (b : ℕ) : a268622N 0 q b = 1 := by
  unfold a268622N
  rw [Fintype.sum_unique]
  simp [a268622Cost]

theorem a268622_N_succ (m : ℕ) (q : Fin 3 × Fin 3) (b : ℕ) :
    a268622N (m + 1) q b = ∑ x : Fin 3, ∑ y : Fin 3,
      if a268622RB (x, y) + a268622VT q (x, y) ≤ b then
        a268622N m (x, y) (b - (a268622RB (x, y) + a268622VT q (x, y))) else 0 := by
  unfold a268622N
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2 → Fin 3).symm _
    (fun z => if a268622Cost (m + 1) q (Fin.cons z.1 z.2 : Fin (m + 1) → Fin 2 → Fin 3) ≤ b
      then 1 else 0) (fun g => by simp), Fintype.sum_prod_type]
  rw [Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 3) _
    (fun z : Fin 3 × Fin 3 => if a268622RB z + a268622VT q z ≤ b then
        ∑ g : Fin m → Fin 2 → Fin 3, if a268622Cost m z g ≤ b - (a268622RB z + a268622VT q z)
          then 1 else 0 else 0) ?_, Fintype.sum_prod_type]
  intro p
  simp only [a268622Cost, Fin.cons_zero, Fin.tail_cons, piFinTwoEquiv_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun g _ => ?_
    exact if_congr (by omega) rfl rfl
  · refine Finset.sum_eq_zero fun g _ => ?_
    exact if_neg (by omega)

theorem a268622_a_succ (m : ℕ) :
    a (m + 1) = ∑ x : Fin 3, ∑ y : Fin 3,
      if a268622RB (x, y) ≤ 1 then a268622N m (x, y) (1 - a268622RB (x, y)) else 0 := by
  rw [a, Finset.card_filter]
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2 → Fin 3).symm _
    (fun z => if pairsTotallingTwo m (Fin.cons z.1 z.2 : Fin (m + 1) → Fin 2 → Fin 3) ≤ 1
      then 1 else 0) (fun g => by simp), Fintype.sum_prod_type]
  rw [Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 3) _
    (fun z : Fin 3 × Fin 3 => if a268622RB z ≤ 1 then
        ∑ g : Fin m → Fin 2 → Fin 3, if a268622Cost m z g ≤ 1 - a268622RB z
          then 1 else 0 else 0) ?_, Fintype.sum_prod_type]
  · rfl
  intro p
  simp only [a268622_pairs, Fin.cons_zero, Fin.tail_cons, piFinTwoEquiv_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun g _ => ?_
    exact if_congr (by omega) rfl rfl
  · refine Finset.sum_eq_zero fun g _ => ?_
    exact if_neg (by omega)

theorem a268622_Z_good (m : ℕ) : ∀ q : Fin 3 × Fin 3, a268622RB q = 0 → a268622N m q 0 = 3 ^ m := by
  induction m with
  | zero => intro q _; exact a268622_N_zero q 0
  | succ m ih =>
    rintro ⟨x, y⟩ hq
    rw [a268622_N_succ]
    fin_cases x <;> fin_cases y <;>
      simp_all [a268622RB, a268622VT, Fin.sum_univ_three] <;> ring

theorem a268622_Z_bad (m : ℕ) (q : Fin 3 × Fin 3) (hq : a268622RB q = 1) :
    a268622N (m + 1) q 0 = 2 * 3 ^ m := by
  obtain ⟨x, y⟩ := q
  rw [a268622_N_succ]
  fin_cases x <;> fin_cases y <;>
    simp_all [a268622RB, a268622VT, Fin.sum_univ_three, a268622_Z_good] <;> ring

theorem a268622_T_good (m : ℕ) : ∀ q : Fin 3 × Fin 3, a268622RB q = 0 →
    (a268622N (m + 1) q 1 : ℚ) = (8 * m + 18) * 3 ^ m / 3 := by
  induction m with
  | zero =>
    rintro ⟨x, y⟩ hq
    have h6 : ∀ x y : Fin 3, a268622RB (x, y) = 0 → (∑ x' : Fin 3, ∑ y' : Fin 3,
        if a268622RB (x', y') + a268622VT (x, y) (x', y') ≤ 1 then 1 else 0) = 6 := by
      decide
    rw [a268622_N_succ]
    simp only [a268622_N_zero]
    rw [h6 x y hq]
    norm_num
  | succ m ih =>
    rintro ⟨x, y⟩ hq
    rw [a268622_N_succ]
    fin_cases x <;> fin_cases y <;>
      simp_all [a268622RB, a268622VT, Fin.sum_univ_three, a268622_Z_good, a268622_Z_bad] <;>
      ring

theorem a268622_a_zero : a 0 = 0 := rfl

theorem a268622_a_one : a 1 = 9 := by
  rw [a268622_a_succ]
  simp only [a268622_N_zero]
  decide

theorem a268622_a_closed (k : ℕ) : (a (k + 2) : ℚ) = 2 * 3 ^ k * (8 * k + 21) := by
  rw [a268622_a_succ]
  simp [a268622RB, Fin.sum_univ_three, a268622_T_good, a268622_Z_bad]
  ring

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a268622.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have h : (((OMA.S_oeis_a268622.a (k + 4) : ℤ)) : ℚ) =
        ((6 * (OMA.S_oeis_a268622.a (k + 4 - 1) : ℤ) - 9 * (OMA.S_oeis_a268622.a (k + 4 - 2) : ℤ) :
          ℤ) : ℚ) := by
      rw [show k + 4 - 1 = (k + 1) + 2 by omega, show k + 4 - 2 = k + 2 by omega,
        show k + 4 = (k + 2) + 2 by omega]
      push_cast
      rw [a268622_a_closed, a268622_a_closed, a268622_a_closed]
      push_cast
      ring
    exact_mod_cast h
  · open PowerSeries in
    have key : PowerSeries.mk (fun n => (OMA.S_oeis_a268622.a n : ℚ)) * (1 - 3 * X) ^ 2 =
        PowerSeries.mk (fun n => (OMA.S_oeis_a268622.a n : ℚ)) * X ^ 0 -
          C 6 * (PowerSeries.mk (fun n => (OMA.S_oeis_a268622.a n : ℚ)) * X ^ 1) +
          C 9 * (PowerSeries.mk (fun n => (OMA.S_oeis_a268622.a n : ℚ)) * X ^ 2) := by
      simp only [map_ofNat]
      ring
    have hrhs : (3 * X * (3 - X) * (1 - X) : ℚ⟦X⟧) =
        C 9 * X ^ 1 - C 12 * X ^ 2 + C 3 * X ^ 3 := by
      simp only [map_ofNat]
      ring
    rw [key, hrhs]
    ext k
    simp only [map_sub, map_add, coeff_C_mul_X_pow]
    simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    by_cases hk : k < 4
    · interval_cases k
      · simp [a268622_a_zero]
      · simp [a268622_a_zero, a268622_a_one]
      · simp [a268622_a_zero, a268622_a_one, a268622_a_closed 0]
        norm_num
      · simp [a268622_a_one, a268622_a_closed 0, a268622_a_closed 1]
        norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
      simp only [show 1 ≤ j + 4 by omega, show 2 ≤ j + 4 by omega, zero_le,
        show j + 4 - 0 = (j + 2) + 2 by omega, show j + 4 - 1 = (j + 1) + 2 by omega,
        show j + 4 - 2 = j + 2 by omega,
        show ¬ (j + 4 = 1) by omega, show ¬ (j + 4 = 2) by omega, show ¬ (j + 4 = 3) by omega,
        if_true, if_false]
      rw [a268622_a_closed, a268622_a_closed, a268622_a_closed]
      push_cast
      ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [a268622_a_closed]
    have : ((k + 2 : ℕ) : ℤ) - 2 = (k : ℤ) := by push_cast; ring
    rw [this, zpow_natCast]
    push_cast
    ring
