import OMAStatements.S_oeis_a273145

namespace OMA.S_oeis_a273145

open PowerSeries




/-- The pattern inside the diamond, by t mod 4 and d mod 4. -/
def tab (r s : ℕ) : Bool :=
  (r == 0 && s == 0) || (r == 2 && s == 2) || (r == 1 && s != 0) || (r == 3 && s != 2)

/-- The state at stage t of a cell at distance d = |x| + |y| from the origin. -/
def g (t d : ℕ) : Bool := if t = 0 then d == 0 else if t < d then true else tab (t % 4) (d % 4)

theorem g_zero_pos {d : ℕ} (h : 0 < d) : g 0 d = false := by
  simp only [g, if_pos rfl]; simp; omega

theorem g_in {t d : ℕ} (ht : 0 < t) (h : d ≤ t) : g t d = tab (t % 4) (d % 4) := by
  simp only [g, if_neg (Nat.pos_iff_ne_zero.mp ht), if_neg (Nat.not_lt.mpr h)]

theorem g_out {t d : ℕ} (ht : 0 < t) (h : t < d) : g t d = true := by
  simp only [g, if_neg (Nat.pos_iff_ne_zero.mp ht), if_pos h]

/-- The origin: four neighbors at distance 1. -/
theorem step0 (t : ℕ) :
    Nat.testBit 597 ((g t 0).toNat + 2 * (4 * (g t 1).toNat)) = g (t + 1) 0 := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht; rfl
  · have h3 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
    have hr : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
    rw [g_in ht (by omega), g_in ht (by omega), g_in (by omega) (by omega), h3]
    generalize t % 4 = r at *
    interval_cases r <;> rfl

/-- A cell on an axis: one neighbor at distance d - 1, three at d + 1. -/
theorem step1 (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit 597 ((g t d).toNat + 2 * ((g t (d - 1)).toNat + 3 * (g t (d + 1)).toNat)) =
      g (t + 1) d := by
  have h1 : (d - 1) % 4 = (d % 4 + 3) % 4 := by omega
  have h2 : (d + 1) % 4 = (d % 4 + 1) % 4 := by omega
  have h3 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
  have hr : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hs : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · obtain rfl : d = 1 := by omega
      rfl
    · rw [g_zero_pos (by omega : 0 < d), g_zero_pos (by omega : 0 < d - 1),
        g_zero_pos (by omega : 0 < d + 1), g_out (by omega : 0 < 0 + 1) (by omega)]
      rfl
  · rcases (by omega : d + 1 ≤ t ∨ d = t ∨ d = t + 1 ∨ t + 2 ≤ d) with c | c | c | c
    · rw [g_in ht (by omega : d ≤ t), g_in ht (by omega : d - 1 ≤ t),
        g_in ht (by omega : d + 1 ≤ t), g_in (by omega : 0 < t + 1) (by omega : d ≤ t + 1),
        h1, h2, h3]
      generalize t % 4 = r at *; generalize d % 4 = s at *
      interval_cases r <;> interval_cases s <;> rfl
    · have hrel : d % 4 = t % 4 := by omega
      rw [g_in ht (by omega : d ≤ t), g_in ht (by omega : d - 1 ≤ t),
        g_out ht (by omega : t < d + 1), g_in (by omega : 0 < t + 1) (by omega : d ≤ t + 1),
        h1, h3, hrel]
      generalize t % 4 = r at *
      interval_cases r <;> rfl
    · have hrel : d % 4 = (t % 4 + 1) % 4 := by omega
      rw [g_out ht (by omega : t < d), g_in ht (by omega : d - 1 ≤ t),
        g_out ht (by omega : t < d + 1), g_in (by omega : 0 < t + 1) (by omega : d ≤ t + 1),
        h1, h3, hrel]
      generalize t % 4 = r at *
      interval_cases r <;> rfl
    · rw [g_out ht (by omega : t < d), g_out ht (by omega : t < d - 1),
        g_out ht (by omega : t < d + 1), g_out (by omega : 0 < t + 1) (by omega : t + 1 < d)]
      rfl

/-- A cell off the axes: two neighbors at distance d - 1, two at d + 1. -/
theorem step2 (t d : ℕ) (hd : 2 ≤ d) :
    Nat.testBit 597 ((g t d).toNat +
      2 * (2 * (g t (d - 1)).toNat + 2 * (g t (d + 1)).toNat)) = g (t + 1) d := by
  have h1 : (d - 1) % 4 = (d % 4 + 3) % 4 := by omega
  have h2 : (d + 1) % 4 = (d % 4 + 1) % 4 := by omega
  have h3 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
  have hr : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hs : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    rw [g_zero_pos (by omega : 0 < d), g_zero_pos (by omega : 0 < d - 1),
      g_zero_pos (by omega : 0 < d + 1), g_out (by omega : 0 < 0 + 1) (by omega)]
    rfl
  · rcases (by omega : d + 1 ≤ t ∨ d = t ∨ d = t + 1 ∨ t + 2 ≤ d) with c | c | c | c
    · rw [g_in ht (by omega : d ≤ t), g_in ht (by omega : d - 1 ≤ t),
        g_in ht (by omega : d + 1 ≤ t), g_in (by omega : 0 < t + 1) (by omega : d ≤ t + 1),
        h1, h2, h3]
      generalize t % 4 = r at *; generalize d % 4 = s at *
      interval_cases r <;> interval_cases s <;> rfl
    · have hrel : d % 4 = t % 4 := by omega
      rw [g_in ht (by omega : d ≤ t), g_in ht (by omega : d - 1 ≤ t),
        g_out ht (by omega : t < d + 1), g_in (by omega : 0 < t + 1) (by omega : d ≤ t + 1),
        h1, h3, hrel]
      generalize t % 4 = r at *
      interval_cases r <;> rfl
    · have hrel : d % 4 = (t % 4 + 1) % 4 := by omega
      rw [g_out ht (by omega : t < d), g_in ht (by omega : d - 1 ≤ t),
        g_out ht (by omega : t < d + 1), g_in (by omega : 0 < t + 1) (by omega : d ≤ t + 1),
        h1, h3, hrel]
      generalize t % 4 = r at *
      interval_cases r <;> rfl
    · rw [g_out ht (by omega : t < d), g_out ht (by omega : t < d - 1),
        g_out ht (by omega : t < d + 1), g_out (by omega : 0 < t + 1) (by omega : t + 1 < d)]
      rfl

/-- Stage t is the pattern `g` of the distance |x| + |y|. -/
theorem state_pattern (t : ℕ) : ∀ x y, state t x y = g t (x.natAbs + y.natAbs) := by
  induction t with
  | zero =>
    intro x y
    by_cases h : x = 0 ∧ y = 0
    · rw [show state 0 x y = decide (x = 0 ∧ y = 0) from rfl, decide_eq_true h,
        show x.natAbs + y.natAbs = 0 by omega]
      rfl
    · rw [show state 0 x y = decide (x = 0 ∧ y = 0) from rfl, decide_eq_false h,
        g_zero_pos (by omega)]
  | succ t ih =>
    intro x y
    show Nat.testBit 597 _ = _
    rw [ih, ih, ih, ih, ih]
    rcases lt_trichotomy x 0 with hx | hx | hx <;> rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← step2 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step1 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step2 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← step1 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = 1 by omega,
        show (x + 1).natAbs + y.natAbs = 1 by omega,
        show x.natAbs + (y - 1).natAbs = 1 by omega,
        show x.natAbs + (y + 1).natAbs = 1 by omega,
        show x.natAbs + y.natAbs = 0 by omega, ← step0 t]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step1 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← step2 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step1 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step2 t _ (by omega)]
      congr 1; ring
/-! ### Counting cells by distance -/

/-- The number of integers with absolute value i. -/
def w (i : ℕ) : ℕ := if i = 0 then 1 else 2

/-- The number of cells at distance d = |x| + |y| from the origin. -/
def c (d : ℕ) : ℕ := if d = 0 then 1 else 4 * d

theorem sum_Icc_natAbs (n : ℕ) (h : ℕ → ℕ) :
    ∑ x ∈ Finset.Icc (-(n : ℤ)) n, h x.natAbs = ∑ i ∈ Finset.range (n + 1), w i * h i := by
  induction n with
  | zero => simp [w]
  | succ n ih =>
    have e : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert (-((n + 1 : ℕ) : ℤ)) (insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) n)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [e, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih,
      Finset.sum_range_succ _ (n + 1), Int.natAbs_neg, Int.natAbs_natCast,
      show w (n + 1) = 2 by simp [w]]
    ring

theorem sum_w (n : ℕ) : ∑ i ∈ Finset.range (n + 1), w i = 2 * n + 1 := by
  induction n with
  | zero => simp [w]
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp only [w, if_neg (show n + 1 ≠ 0 by omega)]; ring

theorem sum_ww (m : ℕ) (hm : 1 ≤ m) : ∑ i ∈ Finset.range (m + 1), w i * w (m - i) = 4 * m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have e : ∀ i ∈ Finset.range k, w (i + 1) * w (k + 1 - (i + 1)) = 4 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only [w, if_neg (show i + 1 ≠ 0 by omega), if_neg (show k + 1 - (i + 1) ≠ 0 by omega)]
  rw [Finset.sum_congr rfl e, show k + 1 - (k + 1) = 0 by omega, show k + 1 - 0 = k + 1 by omega,
    show w 0 = 1 from rfl, show w (k + 1) = 2 by simp [w]]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

/-- Grouping the pairs (i, j) with i + j <= n by d = i + j. -/
theorem shell (n : ℕ) (h : ℕ → ℕ) :
    ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      w i * w j * (if i + j ≤ n then h (i + j) else 0) =
    ∑ d ∈ Finset.range (n + 1), c d * h d := by
  induction n with
  | zero => simp [w, c]
  | succ n ih =>
    have split : ∀ i j, (if i + j ≤ n + 1 then h (i + j) else 0) =
        (if i + j ≤ n then h (i + j) else 0) + (if i + j = n + 1 then h (n + 1) else 0) := by
      intro i j
      by_cases h1 : i + j ≤ n
      · rw [if_pos (by omega), if_pos h1, if_neg (by omega), add_zero]
      · by_cases h2 : i + j = n + 1
        · rw [if_pos (by omega), if_neg h1, if_pos h2, zero_add, h2]
        · rw [if_neg (by omega), if_neg h1, if_neg h2]
    simp only [split, mul_add, Finset.sum_add_distrib]
    have hA : ∑ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 1),
        w i * w j * (if i + j ≤ n then h (i + j) else 0) =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          w i * w j * (if i + j ≤ n then h (i + j) else 0) := by
      rw [Finset.sum_range_succ]
      have z : ∑ j ∈ Finset.range (n + 1 + 1),
          w (n + 1) * w j * (if n + 1 + j ≤ n then h (n + 1 + j) else 0) = 0 :=
        Finset.sum_eq_zero (fun j _ => by rw [if_neg (by omega), mul_zero])
      rw [z, add_zero]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp only [Finset.mem_range] at hi
      rw [Finset.sum_range_succ, if_neg (by omega), mul_zero, add_zero]
    have hB : ∑ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 1),
        w i * w j * (if i + j = n + 1 then h (n + 1) else 0) = c (n + 1) * h (n + 1) := by
      have inner : ∀ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 1),
          w i * w j * (if i + j = n + 1 then h (n + 1) else 0) =
            w i * w (n + 1 - i) * h (n + 1) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [Finset.sum_eq_single (n + 1 - i)]
        · rw [if_pos (by omega)]
        · intro j _ hj
          rw [if_neg (by omega), mul_zero]
        · intro hj
          simp only [Finset.mem_range] at hj
          omega
      rw [Finset.sum_congr rfl inner, ← Finset.sum_mul, sum_ww (n + 1) (by omega)]
      simp only [c, if_neg (show n + 1 ≠ 0 by omega)]
    rw [hA, hB, ih, Finset.sum_range_succ _ (n + 1)]

/-! ### The count -/

/-- The cells of stage n at distance d <= n that are OFF, counted with multiplicity c d. -/
def OFF (n : ℕ) : ℕ := ∑ d ∈ Finset.range (n + 1), c d * (if tab (n % 4) (d % 4) then 0 else 1)

theorem count_eq (n : ℕ) : count n = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    w i * w j * (if g n (i + j) then 1 else 0) := by
  unfold count
  rw [Finset.card_filter, Finset.sum_product]
  have inner : ∀ x ∈ Finset.Icc (-(n : ℤ)) n,
      (∑ y ∈ Finset.Icc (-(n : ℤ)) n, if state n x y = true then 1 else 0) =
        ∑ j ∈ Finset.range (n + 1), w j * (if g n (x.natAbs + j) then 1 else 0) := by
    intro x _
    simp only [state_pattern]
    exact sum_Icc_natAbs n (fun j => if g n (x.natAbs + j) then 1 else 0)
  rw [Finset.sum_congr rfl inner,
    sum_Icc_natAbs n (fun i => ∑ j ∈ Finset.range (n + 1), w j * (if g n (i + j) then 1 else 0))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem count_off (n : ℕ) : count n + OFF n = (2 * n + 1) ^ 2 := by
  have key : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
      w i * w j * (if g n (i + j) then 1 else 0) +
        w i * w j * (if i + j ≤ n then (if tab (n % 4) ((i + j) % 4) then 0 else 1) else 0) =
      w i * w j := by
    intro i hi j hj
    simp only [Finset.mem_range] at hi hj
    rw [← mul_add]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      obtain rfl : i = 0 := by omega
      obtain rfl : j = 0 := by omega
      rfl
    · by_cases hd : i + j ≤ n
      · rw [g_in hn hd, if_pos hd]
        cases tab (n % 4) ((i + j) % 4) <;> simp
      · rw [g_out hn (by omega), if_neg hd]; simp
  rw [count_eq, OFF, ← shell n (fun d => if tab (n % 4) (d % 4) then 0 else 1),
    ← Finset.sum_add_distrib]
  have e : ∀ i ∈ Finset.range (n + 1),
      (∑ j ∈ Finset.range (n + 1), w i * w j * (if g n (i + j) then 1 else 0)) +
        (∑ j ∈ Finset.range (n + 1), w i * w j *
          (if i + j ≤ n then (if tab (n % 4) ((i + j) % 4) then 0 else 1) else 0)) =
      ∑ j ∈ Finset.range (n + 1), w i * w j := by
    intro i hi
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j hj => key i hi j hj)
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul_sum, sum_w]
  ring

theorem off_shift (n : ℕ) : OFF (n + 4) = OFF n + (if n % 2 = 0 then 12 * n + 24 else 4 * n + 12) := by
  unfold OFF
  rw [show n + 4 + 1 = n + 1 + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, show (n + 1 + 1 + 1 + 1) % 4 = n % 4 by omega]
  have m2 : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
  have m3 : (n + 1 + 1) % 4 = (n % 4 + 2) % 4 := by omega
  have m4 : (n + 1 + 1 + 1) % 4 = (n % 4 + 3) % 4 := by omega
  have m6 : n % 2 = n % 4 % 2 := by omega
  simp only [c, m2, m3, m4, m6, if_neg (show n + 1 ≠ 0 by omega),
    if_neg (show n + 1 + 1 ≠ 0 by omega), if_neg (show n + 1 + 1 + 1 ≠ 0 by omega),
    if_neg (show n + 1 + 1 + 1 + 1 ≠ 0 by omega)]
  have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize n % 4 = r at *
  interval_cases r <;> simp [tab] <;> ring

/-! ### Stage 2^n - 1 -/

/-- At the stages 4m + 3 the OFF distances are those with d = 2 mod 4. -/
theorem off_odd (m : ℕ) : OFF (4 * m + 3) = 8 * (m + 1) ^ 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h := off_shift (4 * m + 3)
    rw [show 4 * m + 3 + 4 = 4 * (m + 1) + 3 by ring, ih, if_neg (by omega)] at h
    rw [h]
    ring

/-- Blomberg's closed form, for n > 1. -/
theorem closed (n : ℕ) (hn : 1 < n) : (a n : ℤ) = 14 * 4 ^ (n - 1) - 4 * 2 ^ n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have ht : 2 ^ (m + 2) - 1 = 4 * (2 ^ m - 1) + 3 := by rw [pow_add]; omega
  have h1 := count_off (2 ^ (m + 2) - 1)
  have hoff : OFF (2 ^ (m + 2) - 1) = 8 * (2 ^ m) ^ 2 := by
    rw [ht, off_odd, show 2 ^ m - 1 + 1 = 2 ^ m by omega]
  rw [hoff] at h1
  have ht' : ((2 ^ (m + 2) - 1 : ℕ) : ℤ) = 4 * 2 ^ m - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
    push_cast
    ring
  have h1z : ((count (2 ^ (m + 2) - 1) : ℕ) : ℤ) + 8 * ((2 : ℤ) ^ m) ^ 2 =
      (2 * ((2 ^ (m + 2) - 1 : ℕ) : ℤ) + 1) ^ 2 := by exact_mod_cast h1
  rw [ht'] at h1z
  have e4 : ((2 : ℤ) ^ m) ^ 2 = 4 ^ m := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  unfold a
  rw [show m + 2 - 1 = m + 1 by omega, pow_succ (4 : ℤ) m, pow_add (2 : ℤ) m 2, ← e4]
  linear_combination h1z

theorem a_zero : a 0 = 1 := by
  have h := count_off 0
  have e : OFF 0 = 0 := by decide
  rw [e] at h
  unfold a
  simpa using h

theorem a_one : a 1 = 8 := by
  have h := count_off 1
  have e : OFF 1 = 1 := by decide
  rw [e] at h
  unfold a
  norm_num at h ⊢
  omega

theorem val (n N : ℕ) (hn : 1 < n) (hN : (N : ℤ) = 14 * 4 ^ (n - 1) - 4 * 2 ^ n + 1) :
    a n = N := by
  have h := (closed n hn).trans hN.symm
  exact_mod_cast h

/-- Controls: the entry's terms a(0..9). -/
theorem controls : a 0 = 1 ∧ a 1 = 8 ∧ a 2 = 41 ∧ a 3 = 193 ∧ a 4 = 833 ∧ a 5 = 3457 ∧
    a 6 = 14081 ∧ a 7 = 56833 ∧ a 8 = 228353 ∧ a 9 = 915457 :=
  ⟨a_zero, a_one, val 2 41 (by norm_num) (by norm_num), val 3 193 (by norm_num) (by norm_num),
    val 4 833 (by norm_num) (by norm_num), val 5 3457 (by norm_num) (by norm_num),
    val 6 14081 (by norm_num) (by norm_num), val 7 56833 (by norm_num) (by norm_num),
    val 8 228353 (by norm_num) (by norm_num), val 9 915457 (by norm_num) (by norm_num)⟩

/-- Barker's recurrence, for n > 4. -/
theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, closed (m + 5) (by omega), closed (m + 4) (by omega),
    closed (m + 3) (by omega), closed (m + 2) (by omega)]
  rw [show m + 5 - 1 = m + 4 by omega, show m + 4 - 1 = m + 3 by omega,
    show m + 3 - 1 = m + 2 by omega, show m + 2 - 1 = m + 1 by omega]
  ring

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
    1 + X - X ^ 2 + 10 * X ^ 3 - 8 * X ^ 4 := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have c7 : (C (7 : ℤ) : PowerSeries ℤ) = 7 := map_ofNat C 7
  have c8 : (C (8 : ℤ) : PowerSeries ℤ) = 8 := map_ofNat C 8
  have c10 : (C (10 : ℤ) : PowerSeries ℤ) = 10 := map_ofNat C 10
  have c14 : (C (14 : ℤ) : PowerSeries ℤ) = 14 := map_ofNat C 14
  have hD : A * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      A - C 7 * (A * X ^ 1) + C 14 * (A * X ^ 2) - C 8 * (A * X ^ 3) := by
    rw [c7, c8, c14]; ring
  have hN : (1 + X - X ^ 2 + 10 * X ^ 3 - 8 * X ^ 4 : PowerSeries ℤ) =
      1 + X ^ 1 - X ^ 2 + X ^ 3 * C 10 - X ^ 4 * C 8 := by
    rw [c8, c10]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hA, coeff_mk,
    coeff_one, coeff_X_pow]
  obtain ⟨v0, v1, v2, v3, v4, -⟩ := controls
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4]
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, if_false]
    linear_combination r

/-- Blomberg's and Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 14 * 4 ^ (n - 1) - 4 * 2 ^ n + 1) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      1 + X - X ^ 2 + 10 * X ^ 3 - 8 * X ^ 4 :=
  ⟨closed, recurrence, gf⟩

end OMA.S_oeis_a273145

theorem OMA.solution : type_of% @OMA.S_oeis_a273145.main :=
  OMA.S_oeis_a273145.conjecture
