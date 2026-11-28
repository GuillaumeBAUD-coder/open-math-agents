import OMAStatements.S_oeis_a211564

/-!
Proof of Barker's conjectures for A211564 (statement with arrays `Fin (n + 4) → Fin (n + 4)`) (arrays of length n+4 with new values 0 upwards
introduced in order, containing the value n-1).

Restricted growth strings. An array `x` of length `L` with new values in order (`NewValuesInOrder`)
satisfies `x i ≤ i` (`le_of_NIO`), so these arrays form the finite set `RGS L` (`mem_RGS`), and
`a n` is the number of arrays in `RGS (n + 4)` containing `n - 1` (`a_eq_card`). The set of values
of such an array is downward closed, hence equal to `{0, ..., k - 1}` where `k` is the number of
distinct values (`image_eq_range`); for `L ≥ 1` the array contains `n - 1` iff `n ≤ k`
(`contains_iff`).

Counting by the number of values. Let `cnt L k` be the number of arrays in `RGS L` with exactly
`k` distinct values. Appending an entry `y` to an array `g` with `k` values (`Fin.snoc`) gives an
array with new values in order iff `y ≤ k` (`NIO_snoc`); the result has `k + 1` values if `y = k`
and `k` values if `y < k` (`snoc_mem`). Splitting an array of length `L + 1` into its first `L`
entries and its last entry (`cnt_succ_eq_card_pairs`, `card_pairs_eq_sum`, `fiber_count`) gives
`cnt 0 k = [k = 0]`, `cnt (L + 1) 0 = 0` and
  cnt (L + 1) (k + 1) = cnt L k + (k + 1) cnt L (k + 1)   (`cnt_succ_succ`),
the recursion of the Stirling numbers of the second kind. By induction on `m` (`c0`, ..., `c4`):
  cnt m m = 1,   cnt (m + 1) m = m (m + 1) / 2,   cnt (m + 2) m = m (m + 1) (m + 2) (3m + 1) / 24,
  cnt (m + 3) m = m^2 (m + 1)^2 (m + 2) (m + 3) / 48,
  cnt (m + 4) m = m (m + 1) (m + 2) (m + 3) (m + 4) (15m^3 + 30m^2 + 5m - 2) / 5760.

Closed form. Summing over `k = n, ..., n + 4` (`card_contains`, `sum_window`),
  a(n) = cnt (n+4) n + cnt (n+4) (n+1) + cnt (n+4) (n+2) + cnt (n+4) (n+3) + cnt (n+4) (n+4)
       = n^8/384 + n^7/32 + 95n^6/576 + 71n^5/120 + 2155n^4/1152 + 167n^3/32 + 3301n^2/288
         + 2119n/120 + 15
(`a_closed`, the entry's empirical formula), a polynomial of degree 8 in `n`. The recurrence
follows by substituting it, and the generating function by comparing coefficients: the ninth
difference of a polynomial of degree 8 vanishes.
-/

namespace OMA.Helpers

open OMA.S_oeis_a211564 Finset

/-- Every entry is at most its position. -/
theorem le_of_NIO {L : ℕ} {x : Fin L → ℕ} (h : NewValuesInOrder x) : ∀ i : Fin L, x i ≤ i.val := by
  have key : ∀ m : ℕ, ∀ i : Fin L, i.val = m → x i ≤ m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hi
      rcases Nat.eq_zero_or_pos (x i) with h0 | hpos
      · omega
      · obtain ⟨j, hj, hxj⟩ := h i (x i - 1) (by omega)
        have hjm : j.val < m := by rw [← hi]; exact hj
        have := ih j.val hjm j rfl
        omega
  exact fun i => key i.val i rfl

theorem ex_lt_castSucc {L : ℕ} (g : Fin L → ℕ) (y : ℕ) (i : Fin L) (v : ℕ) :
    (∃ j : Fin (L + 1), j < i.castSucc ∧ (Fin.snoc g y : Fin (L + 1) → ℕ) j = v) ↔
      ∃ j : Fin L, j < i ∧ g j = v := by
  rw [Fin.exists_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.castSucc_lt_castSucc_iff]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · exact absurd h (not_lt.mpr (Fin.castSucc_lt_last i).le)
  · intro h
    exact Or.inl h

theorem ex_lt_last {L : ℕ} (g : Fin L → ℕ) (y : ℕ) (v : ℕ) :
    (∃ j : Fin (L + 1), j < Fin.last L ∧ (Fin.snoc g y : Fin (L + 1) → ℕ) j = v) ↔
      ∃ j : Fin L, g j = v := by
  rw [Fin.exists_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.castSucc_lt_last, true_and, lt_irrefl,
    false_and, or_false]

theorem NIO_snoc {L : ℕ} (g : Fin L → ℕ) (y : ℕ) :
    NewValuesInOrder (Fin.snoc g y : Fin (L + 1) → ℕ) ↔
      NewValuesInOrder g ∧ ∀ v, v < y → ∃ j : Fin L, g j = v := by
  unfold NewValuesInOrder
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, ex_lt_castSucc, ex_lt_last]

theorem image_snoc {L : ℕ} (g : Fin L → ℕ) (y : ℕ) :
    univ.image (Fin.snoc g y : Fin (L + 1) → ℕ) = insert y (univ.image g) := by
  ext v
  simp only [mem_image, mem_univ, true_and, mem_insert]
  rw [Fin.exists_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h.symm
  · rintro (h | h)
    · exact Or.inr h.symm
    · exact Or.inl h

/-- A downward closed finite set of naturals is an initial segment. -/
theorem eq_range_of_down (s : Finset ℕ) (h : ∀ y ∈ s, ∀ v, v < y → v ∈ s) :
    s = range s.card := by
  symm
  apply eq_of_subset_of_card_le
  · intro v hv
    rw [mem_range] at hv
    by_contra hvs
    have hsub : s ⊆ range v := by
      intro y hy
      rw [mem_range]
      by_contra hyv
      rcases lt_or_eq_of_le (not_lt.mp hyv) with hlt | heq
      · exact hvs (h y hy v hlt)
      · exact hvs (heq ▸ hy)
    have := card_le_card hsub
    rw [card_range] at this
    omega
  · rw [card_range]

theorem image_eq_range {L : ℕ} {x : Fin L → ℕ} (h : NewValuesInOrder x) :
    univ.image x = range (univ.image x).card := by
  apply eq_range_of_down
  intro y hy v hv
  simp only [mem_image, mem_univ, true_and] at hy ⊢
  obtain ⟨i, rfl⟩ := hy
  obtain ⟨j, -, hj⟩ := h i v hv
  exact ⟨j, hj⟩

/-- The arrays of length `L` with new values in order (their entries are below `L`). -/
def RGS (L : ℕ) : Finset (Fin L → ℕ) :=
  (Fintype.piFinset fun _ : Fin L => range L).filter NewValuesInOrder

theorem mem_RGS {L : ℕ} (x : Fin L → ℕ) : x ∈ RGS L ↔ NewValuesInOrder x := by
  unfold RGS
  rw [mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    rw [mem_range]
    have h1 := le_of_NIO h i
    have h2 := i.isLt
    omega

/-- The number of arrays of length `L` with new values in order and exactly `k` distinct values. -/
def cnt (L k : ℕ) : ℕ := #((RGS L).filter (fun x => (univ.image x).card = k))

theorem card_image_le_len {L : ℕ} (x : Fin L → ℕ) : (univ.image x).card ≤ L := by
  have := card_image_le (s := (univ : Finset (Fin L))) (f := x)
  rwa [card_univ, Fintype.card_fin] at this

theorem cnt_zero_left (k : ℕ) : cnt 0 k = if k = 0 then 1 else 0 := by
  have hR : RGS 0 = {fun i => Fin.elim0 i} := by
    ext x
    rw [mem_singleton, mem_RGS]
    constructor
    · intro _
      funext i
      exact i.elim0
    · intro _ i
      exact i.elim0
  unfold cnt
  rw [hR, filter_singleton]
  have h0 : (univ.image (fun i : Fin 0 => Fin.elim0 i : Fin 0 → ℕ)).card = 0 := by
    simp
  rw [h0]
  by_cases hk : k = 0
  · subst hk
    simp
  · simp [hk, Ne.symm hk]

theorem cnt_succ_zero (L : ℕ) : cnt (L + 1) 0 = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x _ hx
  rw [card_eq_zero] at hx
  have : x 0 ∈ univ.image x := mem_image_of_mem x (mem_univ 0)
  rw [hx] at this
  exact absurd this (notMem_empty _)

/-- Membership of `Fin.snoc g y` among the arrays of length `L + 1` with `k + 1` values. -/
theorem snoc_mem {L k : ℕ} {g : Fin L → ℕ} (hg : NewValuesInOrder g) (y : ℕ) :
    (Fin.snoc g y : Fin (L + 1) → ℕ) ∈
        (RGS (L + 1)).filter (fun x => (univ.image x).card = k + 1) ↔
      (y < (univ.image g).card ∧ (univ.image g).card = k + 1) ∨
        (y = (univ.image g).card ∧ (univ.image g).card = k) := by
  rw [mem_filter, mem_RGS, NIO_snoc, image_snoc]
  obtain ⟨c, hc⟩ : ∃ c, (univ.image g).card = c := ⟨_, rfl⟩
  have hrange : univ.image g = range c := hc ▸ image_eq_range hg
  rw [hrange, card_range]
  have hdown : (∀ v, v < y → ∃ j : Fin L, g j = v) ↔ y ≤ c := by
    constructor
    · intro h
      by_contra hyc
      obtain ⟨j, hj⟩ := h c (by omega)
      have hmem : g j ∈ univ.image g := mem_image_of_mem g (mem_univ j)
      rw [hrange, hj, mem_range] at hmem
      exact lt_irrefl _ hmem
    · intro h v hv
      have hmem : v ∈ univ.image g := by
        rw [hrange, mem_range]
        omega
      simpa using hmem
  rw [hdown]
  have hcard : (insert y (range c)).card = if y < c then c else c + 1 := by
    split_ifs with h
    · rw [card_insert_of_mem (mem_range.mpr h), card_range]
    · rw [card_insert_of_notMem (by rw [mem_range]; exact h), card_range]
  rw [hcard]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    split_ifs at h2 with h <;> omega
  · intro h
    refine ⟨⟨hg, by omega⟩, ?_⟩
    split_ifs with h' <;> omega

theorem cnt_succ_eq_card_pairs (L k : ℕ) :
    cnt (L + 1) (k + 1) = #((RGS L ×ˢ range (L + 1)).filter (fun p =>
      (Fin.snoc p.1 p.2 : Fin (L + 1) → ℕ) ∈
        (RGS (L + 1)).filter (fun x => (univ.image x).card = k + 1))) := by
  unfold cnt
  apply card_nbij' (fun x => (Fin.init x, x (Fin.last L))) (fun p => Fin.snoc p.1 p.2)
  · intro x hx
    rw [mem_coe] at hx
    have hx' := hx
    rw [mem_filter, mem_RGS] at hx'
    rw [mem_coe, mem_filter, mem_product, mem_RGS, mem_range, Fin.snoc_init_self]
    have hnio := hx'.1
    rw [← Fin.snoc_init_self x, NIO_snoc] at hnio
    have hle := le_of_NIO hx'.1 (Fin.last L)
    rw [Fin.val_last] at hle
    exact ⟨⟨hnio.1, Nat.lt_succ_of_le hle⟩, hx⟩
  · intro p hp
    rw [mem_coe, mem_filter] at hp
    exact hp.2
  · intro x _
    exact Fin.snoc_init_self x
  · intro p _
    simp only [Fin.init_snoc, Fin.snoc_last]

theorem card_pairs_eq_sum (L k : ℕ) :
    #((RGS L ×ˢ range (L + 1)).filter (fun p =>
      (Fin.snoc p.1 p.2 : Fin (L + 1) → ℕ) ∈
        (RGS (L + 1)).filter (fun x => (univ.image x).card = k + 1))) =
    ∑ g ∈ RGS L, #((range (L + 1)).filter (fun y =>
      (Fin.snoc g y : Fin (L + 1) → ℕ) ∈
        (RGS (L + 1)).filter (fun x => (univ.image x).card = k + 1))) := by
  rw [card_filter, sum_product]
  refine sum_congr rfl (fun g _ => ?_)
  rw [card_filter]

theorem fiber_count {L k : ℕ} {g : Fin L → ℕ} (hg : NewValuesInOrder g) :
    #((range (L + 1)).filter (fun y =>
      (Fin.snoc g y : Fin (L + 1) → ℕ) ∈
        (RGS (L + 1)).filter (fun x => (univ.image x).card = k + 1))) =
    (if (univ.image g).card = k then 1 else 0) +
      (if (univ.image g).card = k + 1 then k + 1 else 0) := by
  have hcL := card_image_le_len g
  rw [filter_congr (fun y _ => snoc_mem hg y)]
  generalize (univ.image g).card = c at hcL ⊢
  by_cases h1 : c = k + 1
  · subst h1
    have e : (range (L + 1)).filter
        (fun y => (y < k + 1 ∧ k + 1 = k + 1) ∨ (y = k + 1 ∧ k + 1 = k)) = range (k + 1) := by
      ext y
      rw [mem_filter, mem_range, mem_range]
      constructor
      · rintro ⟨-, (⟨h, -⟩ | ⟨-, h⟩)⟩
        · exact h
        · omega
      · intro h
        exact ⟨by omega, Or.inl ⟨h, rfl⟩⟩
    rw [e, card_range]
    simp
  · by_cases h2 : c = k
    · subst h2
      have e : (range (L + 1)).filter
          (fun y => (y < c ∧ c = c + 1) ∨ (y = c ∧ c = c)) = {c} := by
        ext y
        rw [mem_filter, mem_range, mem_singleton]
        constructor
        · rintro ⟨-, (⟨-, h⟩ | ⟨h, -⟩)⟩
          · omega
          · exact h
        · intro h
          exact ⟨by omega, Or.inr ⟨h, rfl⟩⟩
      rw [e, card_singleton]
      simp
    · have e : (range (L + 1)).filter
          (fun y => (y < c ∧ c = k + 1) ∨ (y = c ∧ c = k)) = ∅ := by
        ext y
        simp only [mem_filter, mem_range, notMem_empty, iff_false]
        omega
      rw [e, card_empty]
      simp [h1, h2]

/-- The recursion of the Stirling numbers of the second kind. -/
theorem cnt_succ_succ (L k : ℕ) : cnt (L + 1) (k + 1) = cnt L k + (k + 1) * cnt L (k + 1) := by
  rw [cnt_succ_eq_card_pairs, card_pairs_eq_sum,
    sum_congr rfl (fun g hg => fiber_count ((mem_RGS g).mp hg)), sum_add_distrib]
  unfold cnt
  rw [card_filter, card_filter, mul_sum]
  congr 1
  refine sum_congr rfl (fun g _ => ?_)
  split_ifs <;> simp

theorem cnt_eq_zero_of_lt {L k : ℕ} (h : L < k) : cnt L k = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x _ hx
  have := card_image_le_len x
  omega

/-- `S(m, m) = 1`. -/
theorem c0 (m : ℕ) : cnt m m = 1 := by
  induction m with
  | zero => rw [cnt_zero_left]; simp
  | succ m ih => rw [cnt_succ_succ, cnt_eq_zero_of_lt (Nat.lt_succ_self m), ih]; simp

/-- `S(m + 1, m) = m (m + 1) / 2`. -/
theorem c1 (m : ℕ) : (cnt (m + 1) m : ℚ) = (m : ℚ) * (m + 1) / 2 := by
  induction m with
  | zero => rw [cnt_succ_zero]; simp
  | succ m ih =>
    rw [cnt_succ_succ (m + 1) m]
    push_cast
    rw [ih, c0]
    push_cast
    ring

/-- `S(m + 2, m) = m (m + 1) (m + 2) (3m + 1) / 24`. -/
theorem c2 (m : ℕ) : (cnt (m + 2) m : ℚ) = (m : ℚ) * (m + 1) * (m + 2) * (3 * m + 1) / 24 := by
  induction m with
  | zero => rw [show cnt (0 + 2) 0 = 0 from cnt_succ_zero 1]; simp
  | succ m ih =>
    have e : cnt (m + 1 + 2) (m + 1) = cnt (m + 2) m + (m + 1) * cnt (m + 1 + 1) (m + 1) :=
      cnt_succ_succ (m + 2) m
    rw [e]
    push_cast
    rw [ih, c1 (m + 1)]
    push_cast
    ring

/-- `S(m + 3, m) = m^2 (m + 1)^2 (m + 2) (m + 3) / 48`. -/
theorem c3 (m : ℕ) :
    (cnt (m + 3) m : ℚ) = (m : ℚ) ^ 2 * (m + 1) ^ 2 * (m + 2) * (m + 3) / 48 := by
  induction m with
  | zero => rw [show cnt (0 + 3) 0 = 0 from cnt_succ_zero 2]; simp
  | succ m ih =>
    have e : cnt (m + 1 + 3) (m + 1) = cnt (m + 3) m + (m + 1) * cnt (m + 1 + 2) (m + 1) :=
      cnt_succ_succ (m + 3) m
    rw [e]
    push_cast
    rw [ih, c2 (m + 1)]
    push_cast
    ring

/-- `S(m + 4, m) = m (m + 1) (m + 2) (m + 3) (m + 4) (15m^3 + 30m^2 + 5m - 2) / 5760`. -/
theorem c4 (m : ℕ) :
    (cnt (m + 4) m : ℚ) = (m : ℚ) * (m + 1) * (m + 2) * (m + 3) * (m + 4) *
      (15 * m ^ 3 + 30 * m ^ 2 + 5 * m - 2) / 5760 := by
  induction m with
  | zero => rw [show cnt (0 + 4) 0 = 0 from cnt_succ_zero 3]; simp
  | succ m ih =>
    have e : cnt (m + 1 + 4) (m + 1) = cnt (m + 4) m + (m + 1) * cnt (m + 1 + 3) (m + 1) :=
      cnt_succ_succ (m + 4) m
    rw [e]
    push_cast
    rw [ih, c3 (m + 1)]
    push_cast
    ring

/-- Bridge: arrays with entries in `Fin (n + 4)` are the arrays of naturals in `RGS (n + 4)`. -/
theorem a_eq_card (n : ℕ) : a n = #((RGS (n + 4)).filter (fun x => ∃ i, x i = n - 1)) := by
  unfold a
  apply card_bij (fun (x : Fin (n + 4) → Fin (n + 4)) _ => fun i => ((x i : Fin (n + 4)) : ℕ))
  · intro x hx
    rw [mem_filter] at hx
    rw [mem_filter, mem_RGS]
    exact ⟨hx.2.1, hx.2.2⟩
  · intro x _ y _ h
    funext i
    exact Fin.ext (congrFun h i)
  · intro y hy
    rw [mem_filter, mem_RGS] at hy
    refine ⟨fun i => ⟨y i, ?_⟩, ?_, rfl⟩
    · have h1 := le_of_NIO hy.1 i
      have h2 := i.isLt
      omega
    · rw [mem_filter]
      exact ⟨mem_univ _, hy.1, hy.2⟩

theorem contains_iff {L n : ℕ} (hL : 1 ≤ L) {x : Fin L → ℕ} (hx : NewValuesInOrder x) :
    (∃ i, x i = n - 1) ↔ n ≤ (univ.image x).card := by
  have hrange := image_eq_range hx
  have hpos : 1 ≤ (univ.image x).card := by
    rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero]
    intro h
    have hmem : x ⟨0, hL⟩ ∈ univ.image x := mem_image_of_mem x (mem_univ _)
    rw [h] at hmem
    exact notMem_empty _ hmem
  constructor
  · rintro ⟨i, hi⟩
    have hmem : x i ∈ univ.image x := mem_image_of_mem x (mem_univ i)
    rw [hrange, mem_range, hi] at hmem
    omega
  · intro h
    have hmem : n - 1 ∈ univ.image x := by
      rw [hrange, mem_range]
      omega
    simpa using hmem

theorem card_contains (n : ℕ) :
    #((RGS (n + 4)).filter (fun x => ∃ i, x i = n - 1)) =
      ∑ j ∈ range (n + 5), if n ≤ j then cnt (n + 4) j else 0 := by
  rw [filter_congr (fun x hx => contains_iff (by omega) ((mem_RGS x).mp hx))]
  rw [card_eq_sum_card_fiberwise (f := fun x => (univ.image x).card) (t := range (n + 5))]
  · refine sum_congr rfl (fun j _ => ?_)
    rw [filter_filter]
    split_ifs with hj
    · unfold cnt
      congr 1
      apply filter_congr
      intro x _
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by omega, h⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro x _ h
      omega
  · intro x _
    simp only [mem_coe, mem_range]
    have := card_image_le_len x
    omega

theorem sum_window (n : ℕ) (F : ℕ → ℕ) :
    (∑ j ∈ range (n + 5), if n ≤ j then F j else 0) =
      F n + F (n + 1) + F (n + 2) + F (n + 3) + F (n + 4) := by
  rw [sum_range_add]
  rw [sum_eq_zero (fun x hx => if_neg (by rw [mem_range] at hx; omega))]
  simp [sum_range_succ]

/-- The closed form, Hardin's empirical polynomial. -/
theorem a_closed (n : ℕ) : (a n : ℚ) = (1 / 384) * (n : ℚ) ^ 8 + (1 / 32) * (n : ℚ) ^ 7 +
    (95 / 576) * (n : ℚ) ^ 6 + (71 / 120) * (n : ℚ) ^ 5 + (2155 / 1152) * (n : ℚ) ^ 4 +
    (167 / 32) * (n : ℚ) ^ 3 + (3301 / 288) * (n : ℚ) ^ 2 + (2119 / 120) * (n : ℚ) + 15 := by
  rw [a_eq_card, card_contains, sum_window]
  have h3 := c3 (n + 1)
  have h2 := c2 (n + 2)
  have h1 := c1 (n + 3)
  rw [show n + 1 + 3 = n + 4 from rfl] at h3
  rw [show n + 2 + 2 = n + 4 from rfl] at h2
  rw [show n + 3 + 1 = n + 4 from rfl] at h1
  push_cast
  rw [c4 n, h3, h2, h1, c0 (n + 4)]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 9 < n) :
    (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3)
        - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7)
        - 9 * a (n - 8) + a (n - 9) := by
  have hQ : (a n : ℚ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3)
        - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7)
        - 9 * a (n - 8) + a (n - 9) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    rw [show k + 10 - 1 = k + 9 by omega,
      show k + 10 - 2 = k + 8 by omega,
      show k + 10 - 3 = k + 7 by omega,
      show k + 10 - 4 = k + 6 by omega,
      show k + 10 - 5 = k + 5 by omega,
      show k + 10 - 6 = k + 4 by omega,
      show k + 10 - 7 = k + 3 by omega,
      show k + 10 - 8 = k + 2 by omega,
      show k + 10 - 9 = k + 1 by omega]
    rw [a_closed (k + 10), a_closed (k + 9), a_closed (k + 8), a_closed (k + 7), a_closed (k + 6),
      a_closed (k + 5), a_closed (k + 4), a_closed (k + 3), a_closed (k + 2), a_closed (k + 1)]
    push_cast
    ring
  exact_mod_cast hQ

/-- The polynomial closed form of A211564. -/
def a211564Poly (n : ℕ) : ℚ := (1 / 384) * (n : ℚ) ^ 8 + (1 / 32) * (n : ℚ) ^ 7 +
    (95 / 576) * (n : ℚ) ^ 6 + (71 / 120) * (n : ℚ) ^ 5 + (2155 / 1152) * (n : ℚ) ^ 4 +
    (167 / 32) * (n : ℚ) ^ 3 + (3301 / 288) * (n : ℚ) ^ 2 + (2119 / 120) * (n : ℚ) + 15

open PowerSeries in
/-- The generating function, for any sequence given by the closed form (stated generically so
that the concrete counting function is never evaluated). -/
theorem gen_fun_of_closed (f : ℕ → ℚ) (hf : ∀ n, f n = a211564Poly n) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else f n) * (1 - X) ^ 9 =
        X * (52 - 266 * X + 867 * X ^ 2 - 1367 * X ^ 3 + 1534 * X ^ 4 - 1097 * X ^ 5
          + 497 * X ^ 6 - 130 * X ^ 7 + 15 * X ^ 8) := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else f n) with hA
  have key : A * (1 - X) ^ 9 =
      A * X ^ 0 - C (9 : ℚ) * (A * X ^ 1) + C (36 : ℚ) * (A * X ^ 2) - C (84 : ℚ) * (A * X ^ 3) +
        C (126 : ℚ) * (A * X ^ 4) - C (126 : ℚ) * (A * X ^ 5) + C (84 : ℚ) * (A * X ^ 6) -
        C (36 : ℚ) * (A * X ^ 7) + C (9 : ℚ) * (A * X ^ 8) - A * X ^ 9 := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : PowerSeries ℚ) * (52 - 266 * X + 867 * X ^ 2 - 1367 * X ^ 3 + 1534 * X ^ 4
        - 1097 * X ^ 5 + 497 * X ^ 6 - 130 * X ^ 7 + 15 * X ^ 8) =
      C (52 : ℚ) * X ^ 1 - C (266 : ℚ) * X ^ 2 + C (867 : ℚ) * X ^ 3 - C (1367 : ℚ) * X ^ 4 +
        C (1534 : ℚ) * X ^ 5 - C (1097 : ℚ) * X ^ 6 + C (497 : ℚ) * X ^ 7 -
        C (130 : ℚ) * X ^ 8 + C (15 : ℚ) * X ^ 9 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  by_cases hk : k < 10
  · interval_cases k <;> norm_num [hf, a211564Poly]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 10 := ⟨k - 10, by omega⟩
    simp only [show 0 ≤ j + 10 by omega, show 1 ≤ j + 10 by omega, show 2 ≤ j + 10 by omega,
      show 3 ≤ j + 10 by omega, show 4 ≤ j + 10 by omega, show 5 ≤ j + 10 by omega,
      show 6 ≤ j + 10 by omega, show 7 ≤ j + 10 by omega, show 8 ≤ j + 10 by omega,
      show 9 ≤ j + 10 by omega, show j + 10 - 0 = j + 10 by omega, show j + 10 - 1 = j + 9 by omega,
      show j + 10 - 2 = j + 8 by omega, show j + 10 - 3 = j + 7 by omega,
      show j + 10 - 4 = j + 6 by omega, show j + 10 - 5 = j + 5 by omega,
      show j + 10 - 6 = j + 4 by omega, show j + 10 - 7 = j + 3 by omega,
      show j + 10 - 8 = j + 2 by omega, show j + 10 - 9 = j + 1 by omega,
      show ¬ (j + 1 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 4 = 0) by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 6 = 0) by omega,
      show ¬ (j + 7 = 0) by omega, show ¬ (j + 8 = 0) by omega, show ¬ (j + 9 = 0) by omega,
      show ¬ (j + 10 = 0) by omega, if_true, if_false]
    rw [hf (j + 10), hf (j + 9), hf (j + 8), hf (j + 7), hf (j + 6),
      hf (j + 5), hf (j + 4), hf (j + 3), hf (j + 2), hf (j + 1)]
    unfold a211564Poly
    push_cast
    ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
        X * (52 - 266 * X + 867 * X ^ 2 - 1367 * X ^ 3 + 1534 * X ^ 4 - 1097 * X ^ 5
          + 497 * X ^ 6 - 130 * X ^ 7 + 15 * X ^ 8) :=
  gen_fun_of_closed (fun n => (a n : ℚ)) (fun n => by rw [a_closed]; rfl)

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a211564.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
