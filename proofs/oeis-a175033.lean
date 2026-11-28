import OMAStatements.S_oeis_a175033

namespace OMA.S_oeis_a175033



theorem P_iff (n : ℕ) : P n ↔ ∃ m : ℕ, 5 ≤ m ∧ n ^ 2 + 17 = 2 * m ^ 2 := by
  constructor
  · intro h
    unfold P at h
    set c := ⌈Real.sqrt ((n : ℝ) * n / 2)⌉ with hc
    have hc0 : 0 ≤ c := Int.ceil_nonneg (Real.sqrt_nonneg _)
    have hreal : 2 * (c : ℝ) ^ 2 = (n : ℝ) ^ 2 + 17 := by nlinarith [h]
    have hcz : 2 * c ^ 2 = (n : ℤ) ^ 2 + 17 := by exact_mod_cast hreal
    have hc1 : 1 ≤ c := by nlinarith
    have hlt : (c : ℝ) - 1 < Real.sqrt ((n : ℝ) * n / 2) := (Int.ceil_eq_iff.mp hc.symm).1
    have hc1r : (1 : ℝ) ≤ c := by exact_mod_cast hc1
    have hsq : ((c : ℝ) - 1) ^ 2 < (n : ℝ) * n / 2 := (Real.lt_sqrt (by linarith)).mp hlt
    have h19 : (19 : ℝ) < 4 * c := by nlinarith
    have h19z : (19 : ℤ) < 4 * c := by exact_mod_cast h19
    refine ⟨c.toNat, by omega, ?_⟩
    have e : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc0
    zify
    rw [e]
    linarith [hcz]
  · rintro ⟨m, hm5, hm⟩
    have hmr : 2 * (m : ℝ) ^ 2 = (n : ℝ) ^ 2 + 17 := by exact_mod_cast hm.symm
    have hm5r : (5 : ℝ) ≤ m := by exact_mod_cast hm5
    have hceil : ⌈Real.sqrt ((n : ℝ) * n / 2)⌉ = (m : ℤ) := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor
      · rw [Real.lt_sqrt (by linarith)]
        nlinarith
      · rw [Real.sqrt_le_left (by linarith)]
        nlinarith
    unfold P
    rw [hceil]
    push_cast
    nlinarith

/-- The solutions of n^2 + 17 = 2m^2 with m >= 5 in increasing order: two chains of
(n, m) -> (3n + 4m, 2n + 3m), started at (9, 7) and (15, 11) and interleaved. -/
def XY : ℕ → ℕ × ℕ
  | 0 => (9, 7)
  | 1 => (15, 11)
  | j + 2 => (3 * (XY j).1 + 4 * (XY j).2, 2 * (XY j).1 + 3 * (XY j).2)

theorem XY_add_two (j : ℕ) :
    XY (j + 2) = (3 * (XY j).1 + 4 * (XY j).2, 2 * (XY j).1 + 3 * (XY j).2) := by
  rw [XY]

theorem pell (j : ℕ) : (XY j).1 ^ 2 + 17 = 2 * (XY j).2 ^ 2 ∧ 5 ≤ (XY j).2 := by
  have key : ∀ j, ((XY j).1 ^ 2 + 17 = 2 * (XY j).2 ^ 2 ∧ 5 ≤ (XY j).2) ∧
      ((XY (j + 1)).1 ^ 2 + 17 = 2 * (XY (j + 1)).2 ^ 2 ∧ 5 ≤ (XY (j + 1)).2) := by
    intro j
    induction j with
    | zero => exact ⟨⟨rfl, by decide⟩, ⟨rfl, by decide⟩⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      rw [XY_add_two]
      exact ⟨by nlinarith [ih.1.1], by simp only; omega⟩
  exact (key j).1

theorem mono (j : ℕ) : (XY j).1 < (XY (j + 1)).1 ∧ (XY j).2 < (XY (j + 1)).2 := by
  have key : ∀ j, ((XY j).1 < (XY (j + 1)).1 ∧ (XY j).2 < (XY (j + 1)).2) ∧
      ((XY (j + 1)).1 < (XY (j + 2)).1 ∧ (XY (j + 1)).2 < (XY (j + 2)).2) := by
    intro j
    induction j with
    | zero => exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      rw [XY_add_two (j + 1), XY_add_two j]
      simp only
      constructor <;> omega
  exact (key j).1

/-- Every solution with m >= 5 is in the list. -/
theorem complete (m : ℕ) : ∀ n : ℕ, 5 ≤ m → n ^ 2 + 17 = 2 * m ^ 2 → ∃ j, XY j = (n, m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n h5 h
    rcases Nat.lt_or_ge m 9 with hm | hm
    · have hn : n < 12 := by nlinarith
      interval_cases m <;> interval_cases n <;>
        first
        | exact ⟨0, rfl⟩
        | (exfalso; revert h; decide)
    · have h1 : 4 * m < 3 * n := by
        by_contra hc
        push_neg at hc
        nlinarith [Nat.mul_le_mul hc hc]
      have h2 : m < n := by nlinarith
      have h3 : 2 * n < 3 * m := by nlinarith
      have hp : (3 * n - 4 * m) ^ 2 + 17 = 2 * (3 * m - 2 * n) ^ 2 := by
        zify [h1.le, h3.le]
        push_cast
        nlinarith [h]
      rcases Nat.lt_or_ge (3 * m - 2 * n) 5 with hs | hs
      · have hb : 3 * n - 4 * m < 4 := by nlinarith
        have e1 : n = 3 * (3 * n - 4 * m) + 4 * (3 * m - 2 * n) := by omega
        have e2 : m = 2 * (3 * n - 4 * m) + 3 * (3 * m - 2 * n) := by omega
        generalize 3 * n - 4 * m = u at hp hb e1 e2
        generalize 3 * m - 2 * n = v at hp hs e1 e2
        interval_cases v <;> interval_cases u <;>
          first
          | (exact ⟨1, by rw [e1, e2]; rfl⟩)
          | (exfalso; revert hp; decide)
      · obtain ⟨j, hj⟩ := ih (3 * m - 2 * n) (by omega) (3 * n - 4 * m) hs hp
        refine ⟨j + 2, ?_⟩
        rw [XY_add_two, hj]
        simp only [Prod.mk.injEq]
        omega

/-- The j-th term, j >= 0. -/
def f (j : ℕ) : ℕ := (XY j).1

theorem P_f (j : ℕ) : P (f j) := (P_iff _).2 ⟨(XY j).2, (pell j).2, (pell j).1⟩

theorem P_iff_f (n : ℕ) : P n ↔ ∃ j, f j = n := by
  constructor
  · intro h
    obtain ⟨m, hm5, hm⟩ := (P_iff n).1 h
    obtain ⟨j, hj⟩ := complete m n hm5 hm
    exact ⟨j, by unfold f; rw [hj]⟩
  · rintro ⟨j, rfl⟩
    exact P_f j

theorem f_strictMono : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact (mono j).1

theorem P_infinite : (Set.ofPred P).Infinite :=
  Set.infinite_of_injective_forall_mem f_strictMono.injective (fun j => P_f j)

theorem nth_eq (j : ℕ) : Nat.nth P j = f j := by
  have hS : ∀ n : ℕ, n ∈ { n : ℕ | ∀ hf : Set.Finite (Set.ofPred P), n < hf.toFinset.card } :=
    fun n hf => absurd hf P_infinite
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f ?_ ?_ ?_ (hS j)).symm
  · intro k hk
    obtain ⟨i, hi⟩ := (P_iff_f k).1 hk
    exact ⟨i, hS i, hi⟩
  · intro i _
    exact P_f i
  · intro i _ j _ hij
    exact f_strictMono hij

theorem a_eq (n : ℕ) (hn : 1 ≤ n) : a n = f (n - 1) := by
  rw [a, nth_eq]

/-- n_(j+4) = 6 n_(j+2) - n_j. -/
theorem f_rec (j : ℕ) : (f (j + 4) : ℤ) = 6 * f (j + 2) - f j := by
  unfold f
  rw [show j + 4 = (j + 2) + 2 by ring, XY_add_two (j + 2), XY_add_two j]
  simp only
  push_cast
  ring

/-- Greathouse's conjecture, for n > 4 (where a(n-4) is defined). -/
theorem recurrence (n : ℕ) (hn : 4 < n) : (a n : ℤ) = 6 * a (n - 2) - a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega)]
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 - 1 = m + 2 by omega,
    show m + 5 - 4 - 1 = m by omega]
  exact f_rec m

/-- Controls: the entry's terms a(1..12). -/
theorem controls : a 1 = 9 ∧ a 2 = 15 ∧ a 3 = 55 ∧ a 4 = 89 ∧ a 5 = 321 ∧ a 6 = 519 ∧
    a 7 = 1871 ∧ a 8 = 3025 ∧ a 9 = 10905 ∧ a 10 = 17631 ∧ a 11 = 63559 ∧ a 12 = 102761 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_eq _ (by norm_num)] <;> rfl

end OMA.S_oeis_a175033

theorem OMA.solution : type_of% @OMA.S_oeis_a175033.main :=
  OMA.S_oeis_a175033.recurrence
