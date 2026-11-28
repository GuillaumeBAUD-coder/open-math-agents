import OMAStatements.S_oeis_a202865

-- Problem: A202865: Number of 3 X 3 0..n arrays with row and column sums one greater than the previous row and column.
-- Credit: @mt211211 (AI-assisted: Claude Code, model claude-opus-5-5)
--
-- Idea: subtracting E = e33 - e11 makes the array semi-magic, and every 3 X 3 semi-magic matrix is
-- e_a + o_b along its even and odd permutations. This gives a bijection with integer 5-tuples
-- (a, b, ox, oy, oz) where ox, oy, oz range over independent intervals, so a(n) is a double sum of
-- products of three interval lengths. For fixed a the lengths form a trapezoid in b; the inner sum is
-- evaluated piece by piece and both sums telescope to the closed form.

namespace A202865Proof
open OMA.S_oeis_a202865 Finset

noncomputable section

/-! ### Part 1: an explicit parametrization of the valid arrays -/

/-- The array with parameters `a b ox oy oz`. -/
def ent (a b ox oy oz : ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![ox - b - 1, oy, oz - a], ![oy - a, oz - b, ox], ![oz, ox - a, oy - b + 1]]

def lo (a c : ℤ) : ℤ := max (max 0 a) c
def hi (n : ℕ) (a c : ℤ) : ℤ := min (min (n : ℤ) (a + n)) (c + n)

def box (n : ℕ) : Finset (ℤ × ℤ) := Ico (-(n : ℤ)) (n + 1) ×ˢ Ico (-(n : ℤ) - 1) (n + 2)

def fib (n : ℕ) (p : ℤ × ℤ) : Finset (ℤ × ℤ × ℤ) :=
  Icc (lo p.1 (p.2 + 1)) (hi n p.1 (p.2 + 1)) ×ˢ Icc (lo p.1 (p.2 - 1)) (hi n p.1 (p.2 - 1)) ×ˢ
    Icc (lo p.1 p.2) (hi n p.1 p.2)

def T (n : ℕ) : Finset (Σ _ : ℤ × ℤ, ℤ × ℤ × ℤ) := (box n).sigma (fib n)

def v {n : ℕ} (x : Arr n) (i j : Fin 3) : ℤ := ((x i j : ℕ) : ℤ)

def φ {n : ℕ} (x : Arr n) : Σ _ : ℤ × ℤ, ℤ × ℤ × ℤ :=
  ⟨(v x 2 0 - v x 0 2, v x 2 0 - v x 1 1), (v x 1 2, v x 0 1, v x 2 0)⟩

def entT (t : Σ _ : ℤ × ℤ, ℤ × ℤ × ℤ) : Fin 3 → Fin 3 → ℤ :=
  ent t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2

def ψ (n : ℕ) (t : Σ _ : ℤ × ℤ, ℤ × ℤ × ℤ) : Arr n :=
  fun i j => ⟨min (entT t i j).toNat n, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma valid_iff {n : ℕ} (x : Arr n) : IsValid x ↔
    v x 1 0 + v x 1 1 + v x 1 2 = v x 0 0 + v x 0 1 + v x 0 2 + 1 ∧
    v x 2 0 + v x 2 1 + v x 2 2 = v x 1 0 + v x 1 1 + v x 1 2 + 1 ∧
    v x 0 1 + v x 1 1 + v x 2 1 = v x 0 0 + v x 1 0 + v x 2 0 + 1 ∧
    v x 0 2 + v x 1 2 + v x 2 2 = v x 0 1 + v x 1 1 + v x 2 1 + 1 := by
  simp only [IsValid, rowSum, colSum, Fin.sum_univ_three, v]
  omega

lemma v_le {n : ℕ} (x : Arr n) (i j : Fin 3) : 0 ≤ v x i j ∧ v x i j ≤ n := by
  have := (x i j).isLt
  simp only [v]
  omega

lemma mem_T {n : ℕ} (t : Σ _ : ℤ × ℤ, ℤ × ℤ × ℤ) : t ∈ T n ↔
    (-(n : ℤ) ≤ t.1.1 ∧ t.1.1 ≤ n) ∧ (-(n : ℤ) - 1 ≤ t.1.2 ∧ t.1.2 ≤ n + 1) ∧
    (0 ≤ t.2.1 ∧ t.1.1 ≤ t.2.1 ∧ t.1.2 + 1 ≤ t.2.1 ∧
      t.2.1 ≤ n ∧ t.2.1 ≤ t.1.1 + n ∧ t.2.1 ≤ t.1.2 + 1 + n) ∧
    (0 ≤ t.2.2.1 ∧ t.1.1 ≤ t.2.2.1 ∧ t.1.2 - 1 ≤ t.2.2.1 ∧
      t.2.2.1 ≤ n ∧ t.2.2.1 ≤ t.1.1 + n ∧ t.2.2.1 ≤ t.1.2 - 1 + n) ∧
    (0 ≤ t.2.2.2 ∧ t.1.1 ≤ t.2.2.2 ∧ t.1.2 ≤ t.2.2.2 ∧
      t.2.2.2 ≤ n ∧ t.2.2.2 ≤ t.1.1 + n ∧ t.2.2.2 ≤ t.1.2 + n) := by
  rcases t with ⟨⟨a, b⟩, ox, oy, oz⟩
  simp only [T, box, fib, mem_sigma, mem_product, mem_Ico, mem_Icc, lo, hi, max_le_iff,
    le_min_iff]
  omega

lemma entT_bounds {n : ℕ} {t : Σ _ : ℤ × ℤ, ℤ × ℤ × ℤ} (ht : t ∈ T n) (i j : Fin 3) :
    0 ≤ entT t i j ∧ entT t i j ≤ n := by
  rcases t with ⟨⟨a, b⟩, ox, oy, oz⟩
  rw [mem_T] at ht
  dsimp only at ht
  fin_cases i <;> fin_cases j <;> simp [entT, ent] <;> omega

lemma val_ψ {n : ℕ} {t : Σ _ : ℤ × ℤ, ℤ × ℤ × ℤ} (ht : t ∈ T n) (i j : Fin 3) :
    v (ψ n t) i j = entT t i j := by
  have h := entT_bounds ht i j
  simp only [v, ψ]
  omega

lemma card_valid (n : ℕ) :
    (Finset.univ.filter (fun x : Arr n => IsValid x)).card = (T n).card := by
  apply Finset.card_nbij' φ (ψ n)
  · intro x hx
    have hx' := (valid_iff x).mp (Finset.mem_filter.mp hx).2
    have b00 := v_le x 0 0; have b01 := v_le x 0 1; have b02 := v_le x 0 2
    have b10 := v_le x 1 0; have b11 := v_le x 1 1; have b12 := v_le x 1 2
    have b20 := v_le x 2 0; have b21 := v_le x 2 1; have b22 := v_le x 2 2
    rw [Finset.mem_coe, mem_T]
    simp only [φ]
    omega
  · intro t ht
    rw [Finset.mem_coe] at ht
    rw [Finset.mem_coe, Finset.mem_filter, valid_iff]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [val_ψ ht, entT, ent]
    simp
    omega
  · intro x hx
    have hx' := (valid_iff x).mp (Finset.mem_filter.mp hx).2
    have b00 := v_le x 0 0; have b01 := v_le x 0 1; have b02 := v_le x 0 2
    have b10 := v_le x 1 0; have b11 := v_le x 1 1; have b12 := v_le x 1 2
    have b20 := v_le x 2 0; have b21 := v_le x 2 1; have b22 := v_le x 2 2
    funext i j
    apply Fin.ext
    simp only [v] at *
    fin_cases i <;> fin_cases j <;> simp [ψ, φ, entT, ent, v] <;> omega
  · intro t ht
    rw [Finset.mem_coe] at ht
    have e20 := val_ψ ht 2 0; have e02 := val_ψ ht 0 2; have e11 := val_ψ ht 1 1
    have e12 := val_ψ ht 1 2; have e01 := val_ψ ht 0 1
    rcases t with ⟨⟨a, b⟩, ox, oy, oz⟩
    simp only [entT, ent] at e20 e02 e11 e12 e01
    simp at e20 e02 e11 e12 e01
    simp only [φ, e20, e02, e11, e12, e01]
    congr 1 <;> simp


/-! ### Part 2: the count as a double sum of products of interval lengths -/

/-- The length of the interval of admissible values: `(n + 1 - range {0, a, c})₊`. -/
def L (n : ℕ) (a c : ℤ) : ℤ := max 0 (hi n a c + 1 - lo a c)

lemma card_fib (n : ℕ) (p : ℤ × ℤ) :
    ((fib n p).card : ℤ) = L n p.1 (p.2 + 1) * L n p.1 (p.2 - 1) * L n p.1 p.2 := by
  simp only [fib, card_product, Int.card_Icc, Nat.cast_mul, Int.toNat_eq_max, L, max_comm]
  ring

lemma a_eq_sum (n : ℕ) : (a n : ℚ) = ∑ x ∈ Ico (-(n : ℤ)) (n + 1), ∑ y ∈ Ico (-(n : ℤ) - 1) (n + 2),
    ((L n x (y + 1) : ℚ) * L n x (y - 1) * L n x y) := by
  have h : a n = ∑ p ∈ box n, (L n p.1 (p.2 + 1) * L n p.1 (p.2 - 1) * L n p.1 p.2) := by
    unfold a
    rw [card_valid, T, card_sigma, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun p _ => card_fib n p)
  rw [h, box, Finset.sum_product]
  push_cast
  rfl

/-! ### Part 3: the trapezoid shape of `L` -/

lemma L_neg {n : ℕ} {a c : ℤ} (ha : 0 ≤ a) (han : a ≤ n) (hc : c ≤ 0) :
    L n a c = max 0 (c + n + 1 - a) := by
  simp only [L, lo, hi, max_def, min_def]
  split_ifs <;> omega

lemma L_mid {n : ℕ} {a c : ℤ} (han : a ≤ n) (hc0 : 0 ≤ c) (hca : c ≤ a) :
    L n a c = n + 1 - a := by
  simp only [L, lo, hi, max_def, min_def]
  split_ifs <;> omega

lemma L_pos {n : ℕ} {a c : ℤ} (ha : 0 ≤ a) (han : a ≤ n) (hac : a ≤ c) :
    L n a c = max 0 (n + 1 - c) := by
  simp only [L, lo, hi, max_def, min_def]
  split_ifs <;> omega

lemma hi_eq (n : ℕ) (a c : ℤ) : hi n a c = n + min (min 0 a) c := by
  simp only [hi, min_def]
  split_ifs <;> omega

lemma neg_lo (a c : ℤ) : lo (-a) (-c) = -min (min 0 a) c := by
  simp only [lo, max_def, min_def]
  split_ifs <;> omega

lemma neg_min (a c : ℤ) : min (min 0 (-a)) (-c) = -lo a c := by
  simp only [lo, max_def, min_def]
  split_ifs <;> omega

lemma L_symm (n : ℕ) (a c : ℤ) : L n (-a) (-c) = L n a c := by
  simp only [L, hi_eq, neg_lo, neg_min]
  congr 1
  ring

/-- The inner sum, for a fixed first parameter. -/
def G (n : ℕ) (x : ℤ) : ℚ :=
  ∑ y ∈ Ico (-(n : ℤ) - 1) (n + 2), ((L n x (y + 1) : ℚ) * L n x (y - 1) * L n x y)

lemma G_symm (n : ℕ) (x : ℤ) : G n (-x) = G n x := by
  unfold G
  apply Finset.sum_nbij' (fun y => -y) (fun y => -y)
  · intro y hy
    simp only [Finset.mem_Ico] at hy ⊢
    omega
  · intro y hy
    simp only [Finset.mem_Ico] at hy ⊢
    omega
  · intro y _
    simp
  · intro y _
    simp
  · intro y _
    have h1 : L n (-x) (y + 1) = L n x (-y - 1) := by
      rw [← L_symm n x (-y - 1)]
      congr 1 <;> ring
    have h2 : L n (-x) (y - 1) = L n x (-y + 1) := by
      rw [← L_symm n x (-y + 1)]
      congr 1 <;> ring
    have h3 : L n (-x) y = L n x (-y) := by
      rw [← L_symm n x (-y)]
      congr 1; ring
    rw [h1, h2, h3]
    ring

/-! ### Part 4: summation tools -/

lemma sum_Ico_tele (f Q : ℤ → ℚ) (hf : ∀ y, f y = Q (y + 1) - Q y) {l r : ℤ} (h : l ≤ r) :
    ∑ y ∈ Ico l r, f y = Q r - Q l := by
  induction r, h using Int.le_induction with
  | base => simp
  | succ r hlr ih =>
    rw [show Ico l (r + 1) = insert r (Ico l r) by ext; simp; omega,
      Finset.sum_insert (by simp), ih, hf]
    ring

lemma sum_Ico_split (f : ℤ → ℚ) {l m r : ℤ} (h1 : l ≤ m) (h2 : m ≤ r) :
    ∑ y ∈ Ico l r, f y = ∑ y ∈ Ico l m, f y + ∑ y ∈ Ico m r, f y := by
  rw [← Finset.Ico_union_Ico_eq_Ico h1 h2, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive l m r)]

lemma sum_Ico_one (f : ℤ → ℚ) (m : ℤ) : ∑ y ∈ Ico m (m + 1), f y = f m := by
  rw [show Ico m (m + 1) = {m} by ext; simp; omega, Finset.sum_singleton]

/-! ### Part 5: the inner sums -/

/-- The summand of `G`. -/
def tm (n : ℕ) (x y : ℤ) : ℚ := (L n x (y + 1) : ℚ) * L n x (y - 1) * L n x y

lemma G_eq_tm (n : ℕ) (x : ℤ) : G n x = ∑ y ∈ Ico (-(n : ℤ) - 1) (n + 2), tm n x y := rfl

lemma tm_Z {n : ℕ} {x y : ℤ} (hx : 0 ≤ x) (hxn : x ≤ n) (hy : y ≤ x - n - 2) : tm n x y = 0 := by
  have : L n x (y - 1) = 0 := by
    rw [L_neg hx hxn (by omega)]
    exact max_eq_left (by omega)
  simp [tm, this]

lemma tm_S1 {n : ℕ} {x y : ℤ} (hx : 0 ≤ x) (hxn : x ≤ n) (hy1 : x - n - 1 ≤ y) (hy2 : y ≤ -1) :
    tm n x y = (y + n + 2 - x) * (y + n - x) * (y + n + 1 - x) := by
  rw [tm, L_neg hx hxn (by omega : y + 1 ≤ 0), L_neg hx hxn (by omega : y - 1 ≤ 0),
    L_neg hx hxn (by omega : y ≤ 0), max_eq_right (by omega : (0 : ℤ) ≤ y + 1 + n + 1 - x),
    max_eq_right (by omega : (0 : ℤ) ≤ y + n + 1 - x)]
  rcases le_or_gt 0 (y - 1 + n + 1 - x) with h | h
  · rw [max_eq_right h]
    push_cast
    ring
  · rw [max_eq_left h.le]
    have h0 : y + n + 1 - x = 0 := by omega
    have h0' : (y : ℚ) + n + 1 - x = 0 := by exact_mod_cast h0
    push_cast
    rw [h0']
    ring

lemma tm_S2 {n : ℕ} {x y : ℤ} (hx : 0 ≤ x) (hxn : x ≤ n) (hy1 : x + 1 ≤ y) (hy2 : y ≤ n + 1) :
    tm n x y = (n - y) * (n + 2 - y) * (n + 1 - y) := by
  rw [tm, L_pos hx hxn (by omega : x ≤ y + 1), L_pos hx hxn (by omega : x ≤ y - 1),
    L_pos hx hxn (by omega : x ≤ y), max_eq_right (by omega : (0 : ℤ) ≤ n + 1 - (y - 1)),
    max_eq_right (by omega : (0 : ℤ) ≤ n + 1 - y)]
  rcases le_or_gt 0 ((n : ℤ) + 1 - (y + 1)) with h | h
  · rw [max_eq_right h]
    push_cast
    ring
  · rw [max_eq_left h.le]
    have h0 : (n : ℤ) + 1 - y = 0 := by omega
    have h0' : (n : ℚ) + 1 - y = 0 := by exact_mod_cast h0
    push_cast
    rw [h0']
    ring

lemma tm_P {n : ℕ} {x y : ℤ} (hxn : x ≤ n) (hy1 : 1 ≤ y) (hy2 : y ≤ x - 1) :
    tm n x y = ((n : ℚ) + 1 - x) ^ 3 := by
  rw [tm, L_mid hxn (by omega : 0 ≤ y + 1) (by omega), L_mid hxn (by omega : 0 ≤ y - 1) (by omega),
    L_mid hxn (by omega : 0 ≤ y) (by omega)]
  push_cast
  ring

lemma tm_zero {n : ℕ} {x : ℤ} (hx : 1 ≤ x) (hxn : x ≤ n) :
    tm n x 0 = ((n : ℚ) + 1 - x) * (n - x) * (n + 1 - x) := by
  rw [tm, L_mid hxn (by omega : (0 : ℤ) ≤ 0 + 1) (by omega), L_neg (by omega) hxn (by omega : (0 : ℤ) - 1 ≤ 0),
    L_mid hxn le_rfl (by omega), max_eq_right (by omega : (0 : ℤ) ≤ 0 - 1 + n + 1 - x)]
  push_cast
  ring

lemma tm_top {n : ℕ} {x : ℤ} (hx : 1 ≤ x) (hxn : x ≤ n) :
    tm n x x = ((n : ℚ) - x) * (n + 1 - x) * (n + 1 - x) := by
  rw [tm, L_pos (by omega) hxn (by omega : x ≤ x + 1), L_mid hxn (by omega : 0 ≤ x - 1) (by omega),
    L_mid hxn (by omega) le_rfl, max_eq_right (by omega : (0 : ℤ) ≤ n + 1 - (x + 1))]
  push_cast
  ring

lemma tm_zero0 (n : ℕ) : tm n 0 0 = (n : ℚ) * n * (n + 1) := by
  rw [tm, L_pos le_rfl (by omega) (by omega : (0 : ℤ) ≤ 0 + 1),
    L_neg le_rfl (by omega) (by omega : (0 : ℤ) - 1 ≤ 0), L_mid (by omega) le_rfl le_rfl,
    max_eq_right (by omega : (0 : ℤ) ≤ n + 1 - (0 + 1)), max_eq_right (by omega : (0 : ℤ) ≤ 0 - 1 + n + 1 - 0)]
  push_cast
  ring

def Q1 (n : ℕ) (x y : ℤ) : ℚ :=
  ((y : ℚ) + n - x - 1) * (y + n - x) * (y + n - x + 1) * (y + n - x + 2) / 4

def Q2 (n : ℕ) (y : ℤ) : ℚ := -(((n : ℚ) - y) * (n - y + 1) * (n - y + 2) * (n - y + 3)) / 4

lemma piece_Z {n : ℕ} {x : ℤ} (hx : 0 ≤ x) (hxn : x ≤ n) :
    ∑ y ∈ Ico (-(n : ℤ) - 1) (x - n - 1), tm n x y = 0 :=
  Finset.sum_eq_zero (fun y hy => tm_Z hx hxn (by rw [Finset.mem_Ico] at hy; omega))

lemma piece_S1 {n : ℕ} {x : ℤ} (hx : 0 ≤ x) (hxn : x ≤ n) :
    ∑ y ∈ Ico (x - n - 1) 0, tm n x y = Q1 n x 0 - Q1 n x (x - n - 1) := by
  rw [Finset.sum_congr rfl (fun y hy => tm_S1 hx hxn (Finset.mem_Ico.mp hy).1
    (by have := (Finset.mem_Ico.mp hy).2; omega))]
  apply sum_Ico_tele _ (Q1 n x) _ (by omega)
  intro y
  simp only [Q1]
  push_cast
  ring

lemma piece_S2 {n : ℕ} {x : ℤ} (hx : 0 ≤ x) (hxn : x ≤ n) :
    ∑ y ∈ Ico (x + 1) (n + 2), tm n x y = Q2 n (n + 2) - Q2 n (x + 1) := by
  rw [Finset.sum_congr rfl (fun y hy => tm_S2 hx hxn (Finset.mem_Ico.mp hy).1
    (by have := (Finset.mem_Ico.mp hy).2; omega))]
  apply sum_Ico_tele _ (Q2 n) _ (by omega)
  intro y
  simp only [Q2]
  push_cast
  ring

lemma piece_P {n : ℕ} {x : ℤ} (hx : 1 ≤ x) (hxn : x ≤ n) :
    ∑ y ∈ Ico 1 x, tm n x y = ((x : ℚ) - 1) * ((n : ℚ) + 1 - x) ^ 3 := by
  rw [Finset.sum_congr rfl (fun y hy => tm_P hxn (Finset.mem_Ico.mp hy).1
    (by have := (Finset.mem_Ico.mp hy).2; omega))]
  rw [sum_Ico_tele _ (fun y : ℤ => (y : ℚ) * ((n : ℚ) + 1 - x) ^ 3) (fun y => by push_cast; ring) hx]
  push_cast
  ring

/-- The inner sum for `1 ≤ x ≤ n`. -/
def Gpoly (n : ℚ) (x : ℚ) : ℚ :=
  -x ^ 4 / 2 + x ^ 3 * n + x ^ 3 - 5 * x ^ 2 / 2 - x * n ^ 3 - 3 * x * n ^ 2 + 2 * x * n + 3 * x +
    n ^ 4 / 2 + 2 * n ^ 3 + n ^ 2 / 2 - 2 * n - 1

lemma G_pos {n : ℕ} {x : ℤ} (hx : 1 ≤ x) (hxn : x ≤ n) : G n x = Gpoly n x := by
  rw [G_eq_tm, sum_Ico_split _ (m := x - n - 1) (by omega) (by omega),
    sum_Ico_split _ (l := x - n - 1) (m := 0) (by omega) (by omega),
    sum_Ico_split _ (l := 0) (m := 1) (by omega) (by omega),
    sum_Ico_split _ (l := 1) (m := x) (by omega) (by omega),
    sum_Ico_split _ (l := x) (m := x + 1) (by omega) (by omega),
    show Ico (0 : ℤ) 1 = Ico 0 (0 + 1) by norm_num, sum_Ico_one, sum_Ico_one,
    piece_Z (by omega) hxn, piece_S1 (by omega) hxn, tm_zero hx hxn, piece_P hx hxn, tm_top hx hxn,
    piece_S2 (by omega) hxn]
  simp only [Q1, Q2, Gpoly]
  push_cast
  ring

lemma G_zero (n : ℕ) : G n 0 = ((n : ℚ) + 1 - 1) ^ 2 * (n + 1) +
    ((n : ℚ) + 1 - 2) * ((n : ℚ) + 1 - 1) * (n + 1) * (n + 2) / 2 := by
  rw [G_eq_tm, sum_Ico_split _ (m := 0) (by omega) (by omega),
    sum_Ico_split _ (l := 0) (m := 1) (by omega) (by omega),
    show Ico (0 : ℤ) 1 = Ico 0 (0 + 1) by norm_num, sum_Ico_one,
    show (-(n : ℤ) - 1) = 0 - n - 1 by ring, piece_S1 le_rfl (by omega), tm_zero0,
    show (1 : ℤ) = 0 + 1 by norm_num, piece_S2 le_rfl (by omega)]
  simp only [Q1, Q2]
  push_cast
  ring

/-! ### Part 6: the closed form -/

def Qout (n : ℚ) (x : ℚ) : ℚ :=
  -x ^ 5 / 10 + x ^ 4 * n / 4 + x ^ 4 / 2 - x ^ 3 * n / 2 - 3 * x ^ 3 / 2 - x ^ 2 * n ^ 3 / 2 -
    3 * x ^ 2 * n ^ 2 / 2 + 5 * x ^ 2 * n / 4 + 3 * x ^ 2 + x * n ^ 4 / 2 + 5 * x * n ^ 3 / 2 +
    2 * x * n ^ 2 - 3 * x * n - 29 * x / 10 - n ^ 4 / 2 - 2 * n ^ 3 - n ^ 2 / 2 + 2 * n + 1

lemma closed_form (n : ℕ) : (a n : ℚ) =
    3 / 10 * (n : ℚ) ^ 5 + 3 / 2 * (n : ℚ) ^ 4 + 3 / 2 * (n : ℚ) ^ 3 - 1 / 2 * (n : ℚ) ^ 2 -
      4 / 5 * (n : ℚ) := by
  have hsum : (a n : ℚ) = ∑ x ∈ Ico (-(n : ℤ)) (n + 1), G n x := a_eq_sum n
  rw [hsum, sum_Ico_split _ (m := 0) (by omega) (by omega),
    sum_Ico_split _ (l := 0) (m := 1) (by omega) (by omega),
    show Ico (0 : ℤ) 1 = Ico 0 (0 + 1) by norm_num, sum_Ico_one, G_zero]
  have hneg : ∑ x ∈ Ico (-(n : ℤ)) 0, G n x = ∑ x ∈ Ico (1 : ℤ) (n + 1), G n x := by
    apply Finset.sum_nbij' (fun x => -x) (fun x => -x)
    · intro x hx
      simp only [Finset.mem_Ico] at hx ⊢
      omega
    · intro x hx
      simp only [Finset.mem_Ico] at hx ⊢
      omega
    · intro x _
      simp
    · intro x _
      simp
    · intro x _
      rw [← G_symm n (-x), neg_neg]
  have hpos : ∑ x ∈ Ico (1 : ℤ) (n + 1), G n x = Qout n ((n : ℚ) + 1) - Qout n 1 := by
    rw [Finset.sum_congr rfl (fun x hx => G_pos (Finset.mem_Ico.mp hx).1
      (by have := (Finset.mem_Ico.mp hx).2; omega))]
    rw [sum_Ico_tele _ (fun x : ℤ => Qout n x) (fun x => by simp only [Qout, Gpoly]; push_cast; ring)
      (by omega)]
    push_cast
    rfl
  rw [hneg, hpos]
  simp only [Qout]
  ring

/-! ### Part 7: the three clauses -/

open PowerSeries in
lemma series (hp : ∀ n : ℕ, (a n : ℚ) = 3 / 10 * (n : ℚ) ^ 5 + 3 / 2 * (n : ℚ) ^ 4 +
      3 / 2 * (n : ℚ) ^ 3 - 1 / 2 * (n : ℚ) ^ 2 - 4 / 5 * (n : ℚ)) :
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 6 = 2 * X * (1 + 15 * X + 3 * X ^ 2 - X ^ 3) := by
  set F := PowerSeries.mk fun n => (a n : ℚ) with hF
  have hD : F * (1 - X) ^ 6 = F - 6 • (F * X ^ 1) + 15 • (F * X ^ 2) - 20 • (F * X ^ 3) +
      15 • (F * X ^ 4) - 6 • (F * X ^ 5) + F * X ^ 6 := by
    simp only [nsmul_eq_mul]
    ring
  have hN : (2 : ℚ⟦X⟧) * X * (1 + 15 * X + 3 * X ^ 2 - X ^ 3) =
      2 • X ^ 1 + 30 • X ^ 2 + 6 • X ^ 3 - 2 • X ^ 4 := by
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [hD, hN]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, hF, coeff_mk]
  by_cases h : n ≤ 6
  · interval_cases n <;> norm_num [hp]
  · simp (disch := omega) only [if_pos, if_neg, hp, Nat.cast_sub, Nat.cast_ofNat,
      Nat.cast_one, nsmul_eq_mul]
    ring

lemma recurrence (n : ℕ) (hn : 6 < n) : a n = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
    15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  have h : (a n : ℚ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
    rw [closed_form n, closed_form (n - 1), closed_form (n - 2), closed_form (n - 3),
      closed_form (n - 4), closed_form (n - 5), closed_form (n - 6)]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega),
      Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  exact_mod_cast h

end

end A202865Proof

open A202865Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a202865.main :=
  ⟨fun n _ => closed_form n, recurrence, series closed_form⟩

