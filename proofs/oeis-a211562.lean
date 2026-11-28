import OMAStatements.S_oeis_a211562

/-!
Proof of Barker's conjectures for A211562.

The arrays counted are the restricted growth strings: a string `x` of length `L` in which new
values are introduced in the order 0, 1, 2, ... has as set of values exactly `{0, ..., B - 1}`,
where `B` is its number of distinct values (`image_eq_range`). All entries are then below `L`, so
the arrays with entries in `Fin (n + 2)` are all of them (`a_eq_card`). The array contains the
value `n - 1` iff `n ≤ B`, and since `B ≤ L = n + 2`, `a n` counts the strings of length `n + 2`
with `n`, `n + 1` or `n + 2` distinct values.

Splitting off the last entry, `snoc y v` is such a string iff `y` is one and `v ≤ B(y)`, and then
`B(snoc y v) = B(y)` if `v < B(y)` and `B(y) + 1` if `v = B(y)`. So the number `N L b` of strings
of length `L` with `b` distinct values satisfies `N (L+1) (b+1) = (b+1) N L (b+1) + N L b`, the
recurrence of the Stirling numbers of the second kind, and `N L b = S(L, b)` (`N_eq`).

With `S(m+2, m+2) = 1`, `S(m+2, m+1) = C(m+2, 2)` and `24 S(m+2, m) = m(m+1)(m+2)(3m+1)`
(by induction), this gives `24 a(n) = 3n^4 + 10n^3 + 21n^2 + 38n + 48` for `n ≥ 1`. The
recurrence and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a211562 Finset

/-- The restricted growth property, for arrays with entries in `ℕ`. -/
abbrev NVO {L : ℕ} (x : Fin L → ℕ) : Prop := NewValuesInOrder x

/-- The number of distinct values of `x`. -/
def nv {L : ℕ} (x : Fin L → ℕ) : ℕ := (univ.image x).card

/-- Append the value `v` at the end of `y`. -/
def sn {L : ℕ} (y : Fin L → ℕ) (v : ℕ) : Fin (L + 1) → ℕ := Fin.snoc y v

@[simp] theorem sn_castSucc {L : ℕ} (y : Fin L → ℕ) (v : ℕ) (i : Fin L) :
    sn y v i.castSucc = y i :=
  Fin.snoc_castSucc (α := fun _ => ℕ) v y i

@[simp] theorem sn_last {L : ℕ} (y : Fin L → ℕ) (v : ℕ) : sn y v (Fin.last L) = v :=
  Fin.snoc_last (α := fun _ => ℕ) v y

theorem sn_init {L : ℕ} (x : Fin (L + 1) → ℕ) : sn (Fin.init x) (x (Fin.last L)) = x :=
  Fin.snoc_init_self (α := fun _ => ℕ) x

theorem init_sn {L : ℕ} (y : Fin L → ℕ) (v : ℕ) : Fin.init (sn y v) = y :=
  Fin.init_snoc (α := fun _ => ℕ) v y

theorem last_not_lt {L : ℕ} (i : Fin L) : ¬ Fin.last L < i.castSucc :=
  not_lt.2 (Fin.castSucc_lt_last i).le

theorem image_sn {L : ℕ} (y : Fin L → ℕ) (v : ℕ) :
    univ.image (sn y v) = insert v (univ.image y) := by
  ext m
  simp only [mem_image, mem_univ, true_and, mem_insert, Fin.exists_fin_succ', sn_castSucc,
    sn_last]
  tauto

theorem nio_sn {L : ℕ} (y : Fin L → ℕ) (v : ℕ) :
    NVO (sn y v) ↔ NVO y ∧ ∀ w < v, ∃ j, y j = w := by
  simp only [NVO, NewValuesInOrder, Fin.forall_fin_succ', Fin.exists_fin_succ', sn_castSucc,
    sn_last, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, last_not_lt, lt_irrefl,
    false_and, or_false, true_and]

/-- The values of a restricted growth string form an initial segment `{0, ..., nv x - 1}`. -/
theorem image_eq_range {L : ℕ} (x : Fin L → ℕ) (hx : NVO x) :
    univ.image x = range (nv x) := by
  induction L with
  | zero =>
    simp [nv]
  | succ L ih =>
    obtain ⟨y, v, rfl⟩ : ∃ y v, x = sn y v := ⟨Fin.init x, x (Fin.last L), (sn_init x).symm⟩
    obtain ⟨hy, hv⟩ := (nio_sn y v).1 hx
    have hiy := ih y hy
    show univ.image (sn y v) = range (univ.image (sn y v)).card
    rw [image_sn, hiy]
    by_cases h : v < nv y
    · rw [insert_eq_of_mem (mem_range.2 h), card_range]
    · have hv' : v = nv y := by
        by_contra hne
        obtain ⟨j, hj⟩ := hv (nv y) (by omega)
        have hm : y j ∈ range (nv y) := by
          rw [← hiy]
          exact mem_image_of_mem y (mem_univ j)
        rw [hj, mem_range] at hm
        omega
      rw [hv', ← range_add_one, card_range]

theorem nv_sn {L : ℕ} {y : Fin L → ℕ} (hy : NVO y) (v : ℕ) :
    nv (sn y v) = if v < nv y then nv y else nv y + 1 := by
  show (univ.image (sn y v)).card = _
  rw [image_sn, image_eq_range y hy]
  split_ifs with h
  · rw [insert_eq_of_mem (mem_range.2 h), card_range]
  · rw [card_insert_of_notMem (by simpa using h), card_range]

theorem nv_le {L : ℕ} (x : Fin L → ℕ) : nv x ≤ L := by
  calc nv x ≤ (univ : Finset (Fin L)).card := card_image_le
    _ = L := by simp

theorem lt_of_nio {L : ℕ} {x : Fin L → ℕ} (hx : NVO x) (i : Fin L) : x i < L := by
  have h : x i ∈ range (nv x) := by
    rw [← image_eq_range x hx]
    exact mem_image_of_mem x (mem_univ i)
  exact lt_of_lt_of_le (mem_range.1 h) (nv_le x)

theorem exists_eq_iff {L : ℕ} {x : Fin L → ℕ} (hx : NVO x) (m : ℕ) :
    (∃ i, x i = m) ↔ m < nv x := by
  rw [← mem_range, ← image_eq_range x hx]
  simp

theorem nio_sn_iff {L : ℕ} {y : Fin L → ℕ} (hy : NVO y) (v : ℕ) :
    NVO (sn y v) ↔ v ≤ nv y := by
  rw [nio_sn]
  constructor
  · rintro ⟨-, h⟩
    by_contra hlt
    obtain ⟨j, hj⟩ := h (nv y) (by omega)
    have := (exists_eq_iff hy (nv y)).1 ⟨j, hj⟩
    omega
  · intro h
    refine ⟨hy, fun w hw => (exists_eq_iff hy w).2 (by omega)⟩

/-- The restricted growth strings of length `L`, as a finset. -/
def R (L : ℕ) : Finset (Fin L → ℕ) :=
  (Fintype.piFinset fun _ : Fin L => range L).filter NVO

theorem mem_R {L : ℕ} {x : Fin L → ℕ} : x ∈ R L ↔ NVO x := by
  rw [R, mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h => h.2, fun h => ⟨fun i => mem_range.2 (lt_of_nio h i), h⟩⟩

/-- Truncate the entries of an array to `Fin (n + 2)`. -/
def toFinArr {n : ℕ} (y : Fin (n + 2) → ℕ) : Fin (n + 2) → Fin (n + 2) :=
  fun i => ⟨min (y i) (n + 1), by omega⟩

theorem toFinArr_val {n : ℕ} {y : Fin (n + 2) → ℕ} (hy : NVO y) :
    (fun i => ((toFinArr y i : Fin (n + 2)) : ℕ)) = y := by
  funext i
  have := lt_of_nio hy i
  simp only [toFinArr]
  omega

theorem a_eq_card (n : ℕ) : a n = ((R (n + 2)).filter (fun x => ∃ i, x i = n - 1)).card := by
  rw [a]
  apply card_nbij' (fun x i => ((x i : Fin (n + 2)) : ℕ)) toFinArr
  · intro x hx
    rw [mem_coe, mem_filter] at hx ⊢
    exact ⟨mem_R.2 hx.2.1, hx.2.2⟩
  · intro y hy
    rw [mem_coe, mem_filter] at hy ⊢
    have hy1 := mem_R.1 hy.1
    have hv : ∀ i, ((toFinArr y i : Fin (n + 2)) : ℕ) = y i := fun i =>
      congrFun (toFinArr_val hy1) i
    obtain ⟨i, hi⟩ := hy.2
    rw [toFinArr_val hy1]
    exact ⟨mem_univ _, hy1, i, (hv i).trans hi⟩
  · intro x _
    funext i
    apply Fin.ext
    have := (x i).isLt
    simp only [toFinArr]
    omega
  · intro y hy
    rw [mem_coe, mem_filter] at hy
    exact toFinArr_val (mem_R.1 hy.1)

/-- The number of restricted growth strings of length `L` with exactly `b` distinct values. -/
def N (L b : ℕ) : ℕ := ∑ x ∈ R L, if nv x = b then 1 else 0

theorem sum_R_succ {L : ℕ} (f : (Fin (L + 1) → ℕ) → ℕ) :
    ∑ x ∈ R (L + 1), f x = ∑ y ∈ R L, ∑ v ∈ range (nv y + 1), f (sn y v) := by
  rw [sum_sigma']
  symm
  apply sum_nbij' (fun p => sn p.1 p.2) (fun x => ⟨Fin.init x, x (Fin.last L)⟩)
  · rintro ⟨y, v⟩ hp
    rw [mem_sigma, mem_R, mem_range] at hp
    rw [mem_R, nio_sn_iff hp.1]
    omega
  · intro x hx
    rw [mem_R] at hx
    have hx' : NVO (sn (Fin.init x) (x (Fin.last L))) := by rw [sn_init]; exact hx
    have hy : NVO (Fin.init x) := ((nio_sn _ _).1 hx').1
    rw [mem_sigma, mem_R, mem_range]
    exact ⟨hy, Nat.lt_succ_of_le ((nio_sn_iff hy _).1 hx')⟩
  · rintro ⟨y, v⟩ _
    simp only [init_sn, sn_last]
  · intro x _
    exact sn_init x
  · intro p _
    rfl

theorem inner_sum {L : ℕ} {y : Fin L → ℕ} (hy : NVO y) (b : ℕ) :
    ∑ v ∈ range (nv y + 1), (if nv (sn y v) = b then 1 else 0) =
      nv y * (if nv y = b then 1 else 0) + (if nv y + 1 = b then 1 else 0) := by
  rw [sum_range_succ]
  congr 1
  · rw [sum_congr rfl (g := fun _ => if nv y = b then 1 else 0)]
    · simp
    · intro v hv
      rw [mem_range] at hv
      rw [nv_sn hy v, if_pos hv]
  · rw [nv_sn hy, if_neg (lt_irrefl _)]

theorem N_succ (L b : ℕ) :
    N (L + 1) b = ∑ y ∈ R L,
      (nv y * (if nv y = b then 1 else 0) + (if nv y + 1 = b then 1 else 0)) := by
  rw [N, sum_R_succ]
  apply sum_congr rfl
  intro y hy
  exact inner_sum (mem_R.1 hy) b

theorem N_zero (b : ℕ) : N 0 b = Nat.stirlingSecond 0 b := by
  have hR : R 0 = {fun i => Fin.elim0 i} := by
    ext x
    rw [mem_R, mem_singleton]
    constructor
    · intro _
      funext i
      exact Fin.elim0 i
    · rintro rfl i
      exact Fin.elim0 i
  have h0 : nv (fun i : Fin 0 => (Fin.elim0 i : ℕ)) = 0 := by simp [nv]
  rw [N, hR, sum_singleton, h0]
  cases b with
  | zero => simp [Nat.stirlingSecond_zero]
  | succ b => simp [Nat.stirlingSecond_zero_succ]

/-- `N L b` is the Stirling number of the second kind `S(L, b)`. -/
theorem N_eq (L b : ℕ) : N L b = Nat.stirlingSecond L b := by
  induction L generalizing b with
  | zero => exact N_zero b
  | succ L ih =>
    rw [N_succ]
    cases b with
    | zero =>
      rw [Nat.stirlingSecond_succ_zero]
      apply sum_eq_zero
      intro y _
      split_ifs <;> simp_all
    | succ b =>
      rw [Nat.stirlingSecond_succ_succ, ← ih, ← ih, N, N, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro y _
      split_ifs <;> omega

theorem a_eq_N (n : ℕ) (hn : 1 ≤ n) :
    a n = N (n + 2) n + N (n + 2) (n + 1) + N (n + 2) (n + 2) := by
  rw [a_eq_card, card_filter, N, N, N, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  have hx' := mem_R.1 hx
  have hle := nv_le x
  have key := exists_eq_iff hx' (n - 1)
  by_cases h : ∃ i, x i = n - 1
  · rw [if_pos h]
    have := key.1 h
    split_ifs <;> omega
  · rw [if_neg h]
    have := mt key.2 h
    split_ifs <;> omega

/-- `24 S(m + 2, m) = m (m + 1) (m + 2) (3m + 1)`, in `ℚ`. -/
theorem S_two (m : ℕ) :
    (Nat.stirlingSecond (m + 2) m : ℚ) = m * (m + 1) * (m + 2) * (3 * m + 1) / 24 := by
  induction m with
  | zero => simp [Nat.stirlingSecond_succ_zero]
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 from rfl, Nat.stirlingSecond_succ_succ,
      Nat.stirlingSecond_succ_self_left]
    push_cast [Nat.cast_choose_two]
    rw [ih]
    ring

theorem a_closedQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (3 * (n : ℚ) ^ 4 + 10 * n ^ 3 + 21 * n ^ 2 + 38 * n + 48) / 24 := by
  rw [a_eq_N n hn, N_eq, N_eq, N_eq]
  push_cast
  rw [S_two n, show n + 2 = (n + 1) + 1 from rfl, Nat.stirlingSecond_succ_self_left,
    Nat.stirlingSecond_self]
  push_cast [Nat.cast_choose_two]
  ring

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 5 = m + 1 by omega]
  have h : ((a (m + 6) : ℤ) : ℚ) = ((5 * a (m + 5) - 10 * a (m + 4) + 10 * a (m + 3)
      - 5 * a (m + 2) + a (m + 1) : ℤ) : ℚ) := by
    push_cast
    rw [a_closedQ (m + 6) (by omega), a_closedQ (m + 5) (by omega), a_closedQ (m + 4) (by omega),
      a_closedQ (m + 3) (by omega), a_closedQ (m + 2) (by omega), a_closedQ (m + 1) (by omega)]
    push_cast
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun_of_closed (f : ℕ → ℚ)
    (hf : ∀ n, 1 ≤ n → f n = (3 * (n : ℚ) ^ 4 + 10 * n ^ 3 + 21 * n ^ 2 + 38 * n + 48) / 24) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else f n) * (1 - X) ^ 5 =
        X * (5 - 11 * X + 16 * X ^ 2 - 9 * X ^ 3 + 2 * X ^ 4) := by
  set P : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else f n with hP
  have key : PowerSeries.mk P * (1 - X) ^ 5 =
      C 1 * (PowerSeries.mk P * X ^ 0) - C 5 * (PowerSeries.mk P * X ^ 1) +
        C 10 * (PowerSeries.mk P * X ^ 2) - C 10 * (PowerSeries.mk P * X ^ 3) +
        C 5 * (PowerSeries.mk P * X ^ 4) - C 1 * (PowerSeries.mk P * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (5 - 11 * X + 16 * X ^ 2 - 9 * X ^ 3 + 2 * X ^ 4) =
      C 5 * X ^ 1 - C 11 * X ^ 2 + C 16 * X ^ 3 - C 9 * X ^ 4 + C 2 * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [hP, hf]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 = 1) by omega, show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega,
      show ¬ (j + 6 = 4) by omega, show ¬ (j + 6 = 5) by omega,
      show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      if_true, if_false, hP]
    rw [hf (j + 6) (by omega), hf (j + 5) (by omega), hf (j + 4) (by omega),
      hf (j + 3) (by omega), hf (j + 2) (by omega), hf (j + 1) (by omega)]
    push_cast
    ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
        X * (5 - 11 * X + 16 * X ^ 2 - 9 * X ^ 3 + 2 * X ^ 4) :=
  gen_fun_of_closed (fun n => (a n : ℚ)) a_closedQ

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a211562.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
