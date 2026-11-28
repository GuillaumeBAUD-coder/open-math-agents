import OMAStatements.S_oeis_a223982

/-!
Proof of the conjectures of A223982 (n X 3 arrays with entries 0..3, rows unimodal, columns
nondecreasing).

Removing the first row gives a transfer recursion: if `T m r` counts the ways to continue the
row `r` by `m` more rows, then `T 0 r` is 1 or 0 as `r` is unimodal or not, `T (m + 1) r` sums
`T m s` over the rows `s ≥ r` (entrywise) when `r` is unimodal, and `a (m + 1)` is the sum of all
`T m r`. Rows are coded by 0, ..., 63 (base-4 digits, most significant first); on codes the two
conditions become a bit mask and a digitwise comparison, checked once against the definitions.

`G m c` is the number of chains `c ≤ d_1 ≤ ... ≤ d_m` of unimodal codes. Grouping equal
neighbours gives `G m c = Sum_k N k c * choose m k`, where `N k c` counts the strict chains
`c < e_1 < ... < e_k` of unimodal codes (`N 10 c = 0`: digit sums grow by at least one, from
at least 0 to at most 9). The table `N` is checked by the kernel against its defining
recursion, and summing over `c` gives `a (n + 1)` as a combination of binomial coefficients;
the closed form, the recurrence and the generating function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a223982 Finset

/-- A row of the array. -/
abbrev Row223982 := Fin 3 → Fin 4

instance decUnimodal223982 (r : Row223982) : Decidable (Unimodal r) := by
  unfold Unimodal
  infer_instance

/-- The conditions of the statement on an array with `m` rows. -/
def Good223982 {m : ℕ} (x : Fin m → Row223982) : Prop :=
  (∀ i, Unimodal (x i)) ∧ ∀ j, Monotone (fun i => x i j)

theorem col_cons223982 {m : ℕ} (r : Row223982) (B : Fin (m + 1) → Row223982) (j : Fin 3) :
    (fun i => (Fin.cons r B : Fin (m + 2) → Row223982) i j) =
      Matrix.vecCons (r j) (fun i => B i j) := by
  funext i
  refine Fin.cases rfl (fun i => rfl) i

theorem good_cons223982 {m : ℕ} (r : Row223982) (B : Fin (m + 1) → Row223982) :
    Good223982 (Fin.cons r B : Fin (m + 2) → Row223982) ↔
      Unimodal r ∧ (∀ j, r j ≤ B 0 j) ∧ Good223982 B := by
  have hm : ∀ j, Monotone (fun i => (Fin.cons r B : Fin (m + 2) → Row223982) i j) ↔
      r j ≤ B 0 j ∧ Monotone (fun i => B i j) := fun j => by
    rw [col_cons223982]; exact monotone_vecCons
  unfold Good223982
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, hm, forall_and]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact ⟨h0, h2, h1, h3⟩
  · rintro ⟨h0, h2, h1, h3⟩
    exact ⟨⟨h0, h1⟩, h2, h3⟩

theorem good_one223982 (r : Row223982) (B : Fin 0 → Row223982) :
    Good223982 (Fin.cons r B : Fin 1 → Row223982) ↔ Unimodal r := by
  have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  unfold Good223982
  constructor
  · rintro ⟨h, _⟩
    simpa using h 0
  · intro h
    refine ⟨fun i => ?_, fun j => Subsingleton.monotone _⟩
    rw [Subsingleton.elim i 0]
    simpa using h

/-- The number of ways to continue the row `r` by `m` more rows. -/
noncomputable def T223982 (m : ℕ) (r : Row223982) : ℕ := by
  classical
  exact ∑ B : Fin m → Row223982,
    if Good223982 (Fin.cons r B : Fin (m + 1) → Row223982) then 1 else 0

theorem T_zero223982 (r : Row223982) :
    T223982 0 r = if Unimodal r then 1 else 0 := by
  classical
  unfold T223982
  rw [Fintype.sum_unique]
  exact if_congr (good_one223982 r _) rfl rfl

theorem T_succ223982 (m : ℕ) (r : Row223982) :
    T223982 (m + 1) r =
      ∑ s : Row223982, if Unimodal r ∧ (∀ j, r j ≤ s j) then T223982 m s else 0 := by
  classical
  unfold T223982
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row223982).symm _
    (fun p => if Good223982 (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → Row223982)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hv : Unimodal r ∧ (∀ j, r j ≤ s j)
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [good_cons223982]
    simp only [Fin.cons_zero]
    exact ⟨fun h => h.2.2, fun h => ⟨hv.1, hv.2, h⟩⟩
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [good_cons223982]
    simp only [Fin.cons_zero]
    exact fun h => hv ⟨h.1, h.2.1⟩

theorem a_eq223982 (n : ℕ) : a (n + 1) = ∑ r : Row223982, T223982 n r := by
  classical
  have h1 : a (n + 1) = ∑ x : Fin (n + 1) → Row223982, if Good223982 x then 1 else 0 := by
    unfold a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    exact Finset.sum_congr rfl fun x _ => if_congr Iff.rfl rfl rfl
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Row223982).symm _
    (fun p => if Good223982 (Fin.cons p.1 p.2 : Fin (n + 1) → Row223982) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  rfl

/-- The row with code `c`: its base-4 digits, most significant first. -/
def row223982 (c : Fin 64) : Row223982 :=
  fun j => ⟨c.val / 4 ^ (2 - j.val) % 4, Nat.mod_lt _ (by norm_num)⟩

theorem row_injective223982 : Function.Injective row223982 := by
  decide +kernel

theorem row_bijective223982 : Function.Bijective row223982 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective223982, by simp⟩

/-- The unimodal codes, as a bit mask. -/
def Ut223982 (c : ℕ) : Bool := Nat.beq (17812298591439552511 / 2 ^ c % 2) 1

/-- Digitwise comparison of codes. -/
def Le223982 (c d : ℕ) : Bool :=
  Nat.ble (c / 16 % 4) (d / 16 % 4) && Nat.ble (c / 4 % 4) (d / 4 % 4) && Nat.ble (c % 4) (d % 4)

theorem Ut_iff223982 : ∀ c : Fin 64, Unimodal (row223982 c) ↔ Ut223982 c.val = true := by
  unfold Unimodal
  decide +kernel

theorem Le_iff223982 : ∀ c d : Fin 64,
    (∀ j, row223982 c j ≤ row223982 d j) ↔ Le223982 c.val d.val = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G223982 : ℕ → Fin 64 → ℕ
  | 0, c => if Ut223982 c.val then 1 else 0
  | m + 1, c => ∑ d : Fin 64, if (Ut223982 c.val && Le223982 c.val d.val) then G223982 m d else 0

theorem T_eq_G223982 (m : ℕ) : ∀ c : Fin 64, T223982 m (row223982 c) = G223982 m c := by
  induction m with
  | zero =>
    intro c
    rw [T_zero223982, G223982]
    exact if_congr (Ut_iff223982 c) rfl rfl
  | succ m ih =>
    intro c
    rw [T_succ223982, ← row_bijective223982.sum_comp]
    simp only [G223982]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ih d]
    refine if_congr ?_ rfl rfl
    rw [Ut_iff223982, Le_iff223982, Bool.and_eq_true]

theorem a_eq_G223982 (n : ℕ) : a (n + 1) = ∑ c : Fin 64, G223982 n c := by
  rw [a_eq223982, ← row_bijective223982.sum_comp]
  exact Finset.sum_congr rfl fun c _ => T_eq_G223982 n c

/-- `Ntab[c][k]`: the number of strict chains `c < e_1 < ... < e_k` of unimodal codes. -/
def Ntab223982 : List (List ℕ) :=
  [[1, 49, 585, 3126, 9199, 16283, 17847, 11892, 4424, 706],
   [1, 33, 284, 1119, 2426, 3095, 2324, 953, 165, 0],
   [1, 20, 118, 329, 501, 430, 196, 37, 0, 0],
   [1, 9, 31, 54, 51, 25, 5, 0, 0, 0],
   [1, 42, 419, 1841, 4354, 5973, 4774, 2068, 376, 0],
   [1, 30, 225, 745, 1298, 1245, 624, 128, 0, 0],
   [1, 18, 91, 207, 240, 139, 32, 0, 0, 0],
   [1, 8, 23, 31, 20, 5, 0, 0, 0, 0],
   [1, 30, 222, 726, 1251, 1188, 590, 120, 0, 0],
   [1, 22, 122, 294, 355, 212, 50, 0, 0, 0],
   [1, 14, 52, 82, 59, 16, 0, 0, 0, 0],
   [1, 6, 12, 10, 3, 0, 0, 0, 0, 0],
   [1, 15, 69, 147, 162, 90, 20, 0, 0, 0],
   [1, 11, 37, 55, 38, 10, 0, 0, 0, 0],
   [1, 7, 15, 13, 4, 0, 0, 0, 0, 0],
   [1, 3, 3, 1, 0, 0, 0, 0, 0, 0],
   [1, 33, 284, 1119, 2426, 3095, 2324, 953, 165, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 30, 225, 745, 1298, 1245, 624, 128, 0, 0],
   [1, 21, 115, 275, 330, 196, 46, 0, 0, 0],
   [1, 12, 41, 61, 42, 11, 0, 0, 0, 0],
   [1, 5, 9, 7, 2, 0, 0, 0, 0, 0],
   [1, 22, 122, 294, 355, 212, 50, 0, 0, 0],
   [1, 16, 65, 110, 84, 24, 0, 0, 0, 0],
   [1, 10, 26, 26, 9, 0, 0, 0, 0, 0],
   [1, 4, 5, 2, 0, 0, 0, 0, 0, 0],
   [1, 11, 37, 55, 38, 10, 0, 0, 0, 0],
   [1, 8, 19, 18, 6, 0, 0, 0, 0, 0],
   [1, 5, 7, 3, 0, 0, 0, 0, 0, 0],
   [1, 2, 1, 0, 0, 0, 0, 0, 0, 0],
   [1, 20, 118, 329, 501, 430, 196, 37, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 18, 91, 207, 240, 139, 32, 0, 0, 0],
   [1, 12, 41, 61, 42, 11, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 14, 52, 82, 59, 16, 0, 0, 0, 0],
   [1, 10, 26, 26, 9, 0, 0, 0, 0, 0],
   [1, 6, 9, 4, 0, 0, 0, 0, 0, 0],
   [1, 2, 1, 0, 0, 0, 0, 0, 0, 0],
   [1, 7, 15, 13, 4, 0, 0, 0, 0, 0],
   [1, 5, 7, 3, 0, 0, 0, 0, 0, 0],
   [1, 3, 2, 0, 0, 0, 0, 0, 0, 0],
   [1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 9, 31, 54, 51, 25, 5, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 8, 23, 31, 20, 5, 0, 0, 0, 0],
   [1, 5, 9, 7, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 6, 12, 10, 3, 0, 0, 0, 0, 0],
   [1, 4, 5, 2, 0, 0, 0, 0, 0, 0],
   [1, 2, 1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 3, 3, 1, 0, 0, 0, 0, 0, 0],
   [1, 2, 1, 0, 0, 0, 0, 0, 0, 0],
   [1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Lookup in the chain table. -/
def N223982 (k : ℕ) (c : Fin 64) : ℕ := (Ntab223982.getD c.val []).getD k 0

theorem N_step223982 : ∀ c : Fin 64, ∀ k : Fin 10,
    (∑ d : Fin 64, if (Ut223982 c.val && Le223982 c.val d.val) then N223982 k.val d else 0) =
      N223982 k.val c + N223982 (k.val + 1) c := by
  decide +kernel

theorem N_zero223982 : ∀ c : Fin 64, N223982 0 c = if Ut223982 c.val then 1 else 0 := by
  decide +kernel

theorem N_top223982 : ∀ c : Fin 64, N223982 10 c = 0 := by
  decide +kernel

theorem G_closed223982 (m : ℕ) :
    ∀ c : Fin 64, G223982 m c = ∑ k ∈ range 10, N223982 k c * m.choose k := by
  induction m with
  | zero =>
    intro c
    simp only [G223982, Finset.sum_range_succ, Finset.sum_range_zero, N_zero223982 c]
    simp
  | succ m ih =>
    intro c
    have h1 : G223982 (m + 1) c = ∑ k ∈ range 10,
        (∑ d : Fin 64, if (Ut223982 c.val && Le223982 c.val d.val) then N223982 k d else 0) *
          m.choose k := by
      simp only [G223982]
      rw [Finset.sum_congr rfl fun d _ => (show (if (Ut223982 c.val && Le223982 c.val d.val) then
          G223982 m d else 0) = ∑ k ∈ range 10, (if (Ut223982 c.val && Le223982 c.val d.val) then
          N223982 k d else 0) * m.choose k by
        split_ifs
        · exact ih d
        · simp), Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
    have h2 : G223982 (m + 1) c =
        ∑ k ∈ range 10, (N223982 k c + N223982 (k + 1) c) * m.choose k := by
      rw [h1]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [N_step223982 c ⟨k, Finset.mem_range.mp hk⟩]
    rw [h2]
    have p1 : (m + 1).choose 1 = m.choose 0 + m.choose 1 := Nat.choose_succ_succ' m 0
    have p2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ' m 1
    have p3 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ' m 2
    have p4 : (m + 1).choose 4 = m.choose 3 + m.choose 4 := Nat.choose_succ_succ' m 3
    have p5 : (m + 1).choose 5 = m.choose 4 + m.choose 5 := Nat.choose_succ_succ' m 4
    have p6 : (m + 1).choose 6 = m.choose 5 + m.choose 6 := Nat.choose_succ_succ' m 5
    have p7 : (m + 1).choose 7 = m.choose 6 + m.choose 7 := Nat.choose_succ_succ' m 6
    have p8 : (m + 1).choose 8 = m.choose 7 + m.choose 8 := Nat.choose_succ_succ' m 7
    have p9 : (m + 1).choose 9 = m.choose 8 + m.choose 9 := Nat.choose_succ_succ' m 8
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3, p4, p5, p6, p7, p8, p9,
      Nat.choose_zero_right, N_top223982 c]
    ring

theorem D_facts223982 :
    (∑ c : Fin 64, N223982 0 c) = 50 ∧
    (∑ c : Fin 64, N223982 1 c) = 634 ∧
    (∑ c : Fin 64, N223982 2 c) = 3711 ∧
    (∑ c : Fin 64, N223982 3 c) = 12325 ∧
    (∑ c : Fin 64, N223982 4 c) = 25482 ∧
    (∑ c : Fin 64, N223982 5 c) = 34130 ∧
    (∑ c : Fin 64, N223982 6 c) = 29739 ∧
    (∑ c : Fin 64, N223982 7 c) = 16316 ∧
    (∑ c : Fin 64, N223982 8 c) = 5130 ∧
    (∑ c : Fin 64, N223982 9 c) = 706 := by
  decide +kernel

theorem a_closed223982 (n : ℕ) :
    a (n + 1) = 50 * n.choose 0 + 634 * n.choose 1 + 3711 * n.choose 2 + 12325 * n.choose 3 + 25482 * n.choose 4 + 34130 * n.choose 5 + 29739 * n.choose 6 + 16316 * n.choose 7 + 5130 * n.choose 8 + 706 * n.choose 9 := by
  rw [a_eq_G223982]
  simp only [G_closed223982 n]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := D_facts223982
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9]
  ring

theorem ch1_223982 (n : ℕ) : (n.choose 1 : ℚ) = n := by simp

theorem ch2_223982 (n : ℕ) : (n.choose 2 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 2 = n.choose 1 + n.choose 2 from Nat.choose_succ_succ' n 1,
      Nat.cast_add, ih, ch1_223982]
    push_cast
    ring

theorem ch3_223982 (n : ℕ) : (n.choose 3 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 3 = n.choose 2 + n.choose 3 from Nat.choose_succ_succ' n 2,
      Nat.cast_add, ih, ch2_223982]
    push_cast
    ring

theorem ch4_223982 (n : ℕ) : (n.choose 4 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) / 24 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 4 = n.choose 3 + n.choose 4 from Nat.choose_succ_succ' n 3,
      Nat.cast_add, ih, ch3_223982]
    push_cast
    ring

theorem ch5_223982 (n : ℕ) : (n.choose 5 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) / 120 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 5 = n.choose 4 + n.choose 5 from Nat.choose_succ_succ' n 4,
      Nat.cast_add, ih, ch4_223982]
    push_cast
    ring

theorem ch6_223982 (n : ℕ) : (n.choose 6 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) * ((n : ℚ) - 5) / 720 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 6 = n.choose 5 + n.choose 6 from Nat.choose_succ_succ' n 5,
      Nat.cast_add, ih, ch5_223982]
    push_cast
    ring

theorem ch7_223982 (n : ℕ) : (n.choose 7 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) * ((n : ℚ) - 5) * ((n : ℚ) - 6) / 5040 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 7 = n.choose 6 + n.choose 7 from Nat.choose_succ_succ' n 6,
      Nat.cast_add, ih, ch6_223982]
    push_cast
    ring

theorem ch8_223982 (n : ℕ) : (n.choose 8 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) * ((n : ℚ) - 5) * ((n : ℚ) - 6) * ((n : ℚ) - 7) / 40320 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 8 = n.choose 7 + n.choose 8 from Nat.choose_succ_succ' n 7,
      Nat.cast_add, ih, ch7_223982]
    push_cast
    ring

theorem ch9_223982 (n : ℕ) : (n.choose 9 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) * ((n : ℚ) - 5) * ((n : ℚ) - 6) * ((n : ℚ) - 7) * ((n : ℚ) - 8) / 362880 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 9 = n.choose 8 + n.choose 9 from Nat.choose_succ_succ' n 8,
      Nat.cast_add, ih, ch8_223982]
    push_cast
    ring

theorem closedQ223982 (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (1 : ℚ) + (6491/1260 : ℚ) * (n : ℚ) + (715/63 : ℚ) * (n : ℚ) ^ 2 + (159679/11340 : ℚ) * (n : ℚ) ^ 3 + (1565/144 : ℚ) * (n : ℚ) ^ 4 + (46793/8640 : ℚ) * (n : ℚ) ^ 5 + (251/144 : ℚ) * (n : ℚ) ^ 6 + (10571/30240 : ℚ) * (n : ℚ) ^ 7 + (5/126 : ℚ) * (n : ℚ) ^ 8 + (353/181440 : ℚ) * (n : ℚ) ^ 9 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_closed223982]
  push_cast
  rw [ch1_223982, ch2_223982, ch3_223982, ch4_223982, ch5_223982, ch6_223982, ch7_223982, ch8_223982, ch9_223982]
  simp only [Nat.choose_zero_right, Nat.cast_one]
  ring

theorem recurrence223982 (n : ℕ) (hn : 11 ≤ n) :
    (a n : ℤ) = 10 * (a (n - 1) : ℤ) - 45 * (a (n - 2) : ℤ) + 120 * (a (n - 3) : ℤ) - 210 * (a (n - 4) : ℤ) + 252 * (a (n - 5) : ℤ) - 210 * (a (n - 6) : ℤ) + 120 * (a (n - 7) : ℤ) - 45 * (a (n - 8) : ℤ) + 10 * (a (n - 9) : ℤ) - 1 * (a (n - 10) : ℤ) := by
  have h : ((a n : ℤ) : ℚ) = ((10 * (a (n - 1) : ℤ) - 45 * (a (n - 2) : ℤ) + 120 * (a (n - 3) : ℤ) - 210 * (a (n - 4) : ℤ) + 252 * (a (n - 5) : ℤ) - 210 * (a (n - 6) : ℤ) + 120 * (a (n - 7) : ℤ) - 45 * (a (n - 8) : ℤ) + 10 * (a (n - 9) : ℤ) - 1 * (a (n - 10) : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ223982 n (by omega), closedQ223982 (n - 1) (by omega), closedQ223982 (n - 2) (by omega), closedQ223982 (n - 3) (by omega), closedQ223982 (n - 4) (by omega), closedQ223982 (n - 5) (by omega), closedQ223982 (n - 6) (by omega), closedQ223982 (n - 7) (by omega), closedQ223982 (n - 8) (by omega), closedQ223982 (n - 9) (by omega), closedQ223982 (n - 10) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega, show 9 ≤ n by omega, show 10 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun223982 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - PowerSeries.X) ^ 10 =
      C 1 * (PowerSeries.mk F * PowerSeries.X ^ 0) - C 10 * (PowerSeries.mk F * PowerSeries.X ^ 1) + C 45 * (PowerSeries.mk F * PowerSeries.X ^ 2) - C 120 * (PowerSeries.mk F * PowerSeries.X ^ 3) + C 210 * (PowerSeries.mk F * PowerSeries.X ^ 4) - C 252 * (PowerSeries.mk F * PowerSeries.X ^ 5) + C 210 * (PowerSeries.mk F * PowerSeries.X ^ 6) - C 120 * (PowerSeries.mk F * PowerSeries.X ^ 7) + C 45 * (PowerSeries.mk F * PowerSeries.X ^ 8) - C 10 * (PowerSeries.mk F * PowerSeries.X ^ 9) + C 1 * (PowerSeries.mk F * PowerSeries.X ^ 10) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (50 * PowerSeries.X + 184 * PowerSeries.X ^ 2 + 439 * PowerSeries.X ^ 3 - 100 * PowerSeries.X ^ 4 + 259 * PowerSeries.X ^ 5 - 210 * PowerSeries.X ^ 6 + 120 * PowerSeries.X ^ 7 - 45 * PowerSeries.X ^ 8 + 10 * PowerSeries.X ^ 9 - 1 * PowerSeries.X ^ 10 : ℚ⟦X⟧) =
      C 50 * PowerSeries.X ^ 1 + C 184 * PowerSeries.X ^ 2 + C 439 * PowerSeries.X ^ 3 - C 100 * PowerSeries.X ^ 4 + C 259 * PowerSeries.X ^ 5 - C 210 * PowerSeries.X ^ 6 + C 120 * PowerSeries.X ^ 7 - C 45 * PowerSeries.X ^ 8 + C 10 * PowerSeries.X ^ 9 - C 1 * PowerSeries.X ^ 10 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 11
  · interval_cases k <;> norm_num [hF, closedQ223982]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 11 := ⟨k - 11, by omega⟩
    simp only [show 0 ≤ j + 11 by omega,
      show j + 11 - 0 = j + 11 by omega,
      show 1 ≤ j + 11 by omega,
      show j + 11 - 1 = j + 10 by omega,
      show 2 ≤ j + 11 by omega,
      show j + 11 - 2 = j + 9 by omega,
      show 3 ≤ j + 11 by omega,
      show j + 11 - 3 = j + 8 by omega,
      show 4 ≤ j + 11 by omega,
      show j + 11 - 4 = j + 7 by omega,
      show 5 ≤ j + 11 by omega,
      show j + 11 - 5 = j + 6 by omega,
      show 6 ≤ j + 11 by omega,
      show j + 11 - 6 = j + 5 by omega,
      show 7 ≤ j + 11 by omega,
      show j + 11 - 7 = j + 4 by omega,
      show 8 ≤ j + 11 by omega,
      show j + 11 - 8 = j + 3 by omega,
      show 9 ≤ j + 11 by omega,
      show j + 11 - 9 = j + 2 by omega,
      show 10 ≤ j + 11 by omega,
      show j + 11 - 10 = j + 1 by omega,
      show ¬ (j + 11 = 1) by omega,
      show ¬ (j + 11 = 2) by omega,
      show ¬ (j + 11 = 3) by omega,
      show ¬ (j + 11 = 4) by omega,
      show ¬ (j + 11 = 5) by omega,
      show ¬ (j + 11 = 6) by omega,
      show ¬ (j + 11 = 7) by omega,
      show ¬ (j + 11 = 8) by omega,
      show ¬ (j + 11 = 9) by omega,
      show ¬ (j + 11 = 10) by omega,
      show ¬ (j + 1 = 0) by omega,
      show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 6 = 0) by omega,
      show ¬ (j + 7 = 0) by omega,
      show ¬ (j + 8 = 0) by omega,
      show ¬ (j + 9 = 0) by omega,
      show ¬ (j + 10 = 0) by omega,
      show ¬ (j + 11 = 0) by omega,
      if_true, if_false, hF]
    rw [closedQ223982 (j + 11) (by omega), closedQ223982 (j + 10) (by omega), closedQ223982 (j + 9) (by omega), closedQ223982 (j + 8) (by omega), closedQ223982 (j + 7) (by omega), closedQ223982 (j + 6) (by omega), closedQ223982 (j + 5) (by omega), closedQ223982 (j + 4) (by omega), closedQ223982 (j + 3) (by omega), closedQ223982 (j + 2) (by omega), closedQ223982 (j + 1) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a223982.main :=
  ⟨OMA.Helpers.recurrence223982, OMA.Helpers.gen_fun223982, OMA.Helpers.closedQ223982⟩
