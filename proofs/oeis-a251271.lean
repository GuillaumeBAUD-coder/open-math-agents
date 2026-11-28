import OMAStatements.S_oeis_a251271

namespace OMA.S_oeis_a251271

open PowerSeries Finset


/-! ## The window condition, rows and the transfer -/

/-- A row. -/
abbrev Row := Fin 5 → Fin 2

/-- The window condition on the 2 X 2 block with top row (p, q) and bottom row (r, s). -/
def P (p q r s : Fin 2) : Prop :=
  ¬ (((s).val : ℤ) - (p).val < ((q).val : ℤ) - (r).val)

instance (p q r s : Fin 2) : Decidable (P p q r s) := by unfold P; infer_instance

/-- Row s may follow row r: every block between them satisfies P. -/
def rowOK (r s : Fin 5 → Fin 2) : Prop :=
  ∀ j j' : Fin 5, j'.val = j.val + 1 → P (r j) (r j') (s j) (s j')

instance : DecidableRel rowOK := fun r s => by unfold rowOK; infer_instance

/-- Consecutive rows allowed. -/
def Valid {m : ℕ} (x : Fin m → Fin 5 → Fin 2) : Prop :=
  ∀ i i' : Fin m, i'.val = i.val + 1 → rowOK (x i) (x i')

instance {m : ℕ} : DecidablePred (@Valid m) := fun x => by unfold Valid; infer_instance

/-- The number of valid arrays with n + 1 rows. -/
def cnt (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 5 → Fin 2)).filter Valid).card

/-- Transposing: the columns of an array are the rows of its transpose. -/
lemma a_eq (n : ℕ) : a n = cnt n := by
  unfold a cnt
  skip
  apply Finset.card_bij' (fun x _ => fun j i => x i j) (fun y _ => fun i j => y j i)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro c c' hc b b' hb
    exact hx b b' hb c c' hc
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    intro b b' hb c c' hc
    exact hy c c' hc b b' hb
  · intro x _
    rfl
  · intro y _
    rfl

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 5 → Fin 2) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 5 → Fin 2)).filter (fun x => Valid x ∧ x 0 = r)).card

lemma valid_cons {n : ℕ} (r : Row) (g : Fin (n + 1) → Row) :
    Valid (Fin.cons r g : Fin (n + 2) → Row) ↔ rowOK r (g 0) ∧ Valid g := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨h0, hg⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        have hj : j = 0 := by ext; simp at hij; omega
        subst hj
        simpa using h0
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        simp only [Fin.cons_succ]
        exact hg i j (by simp at hij; omega)

lemma cnt_sum (n : ℕ) : cnt n = ∑ r : Row, W n r := by
  unfold cnt W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  congr 1
  ext f
  simp

lemma W_zero (r : Row) : W 0 r = 1 := by
  unfold W
  rw [Finset.card_eq_one]
  refine ⟨fun _ => r, ?_⟩
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hf⟩
    funext i
    rw [Fin.fin_one_eq_zero i, hf]
  · rintro rfl
    refine ⟨?_, rfl⟩
    intro i j hij
    have := j.isLt
    omega

/-- Prepending the row r. -/
def consEmb (n : ℕ) (r : Row) : (Fin (n + 1) → Row) ↪ (Fin (n + 2) → Row) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Row) (g : Fin (n + 1) → Row) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Row) :
    W (n + 1) r = ∑ s : Row, if rowOK r s then W n s else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Row)).filter (fun f => Valid f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Row)).filter (fun g => rowOK r (g 0) ∧ Valid g)).map
        (consEmb n r)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons r (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        exact hv
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(valid_cons r g).2 hg, by simp⟩
  unfold W
  rw [e, Finset.card_map]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  split_ifs with hrs
  · congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hg⟩, h0⟩
      exact ⟨hg, h0⟩
    · rintro ⟨hg, h0⟩
      exact ⟨⟨h0 ▸ hrs, hg⟩, h0⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hok, _⟩, h0⟩
    exact hrs (h0 ▸ hok)

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 2) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 2, f s = ∑ x : Fin 2, ∑ t : Fin m → Fin 2, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : Row → ℕ) :
    ∑ s : Row, f s = ∑ x0 : Fin 2, ∑ x1 : Fin 2, ∑ x2 : Fin 2, ∑ x3 : Fin 2, ∑ x4 : Fin 2, f ![x0, x1, x2, x3, x4] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x2 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x3 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x4 _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Row) : r = ![r 0, r 1, r 2, r 3, r 4] := by
  funext j
  fin_cases j <;> rfl

lemma rowOK_iff (r s : Row) : rowOK r s ↔ P (r 0) (r 1) (s 0) (s 1) ∧ P (r 1) (r 2) (s 1) (s 2) ∧ P (r 2) (r 3) (s 2) (s 3) ∧ P (r 3) (r 4) (s 3) (s 4) := by
  constructor
  · intro h
    exact ⟨h 0 1 rfl, h 1 2 rfl, h 2 3 rfl, h 3 4 rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩ j j' hj
    rcases j with ⟨j, hj0⟩
    rcases j' with ⟨j', hj1⟩
    simp only at hj
    subst hj
    have hjw : j < 4 := by omega
    interval_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : Row → ℕ) (r : Row) : ℕ :=
  ∑ x0 : Fin 2, ∑ x1 : Fin 2, if P (r 0) (r 1) x0 x1 then ∑ x2 : Fin 2, if P (r 1) (r 2) x1 x2 then ∑ x3 : Fin 2, if P (r 2) (r 3) x2 x3 then ∑ x4 : Fin 2, if P (r 3) (r 4) x3 x4 then g ![x0, x1, x2, x3, x4] else 0 else 0 else 0 else 0

lemma T_eq (g : Row → ℕ) (r : Row) :
    T g r = ∑ s, if rowOK r s then g s else 0 := by
  rw [sum_row]
  unfold T
  simp only [rowOK_iff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons,
    Matrix.tail_cons, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]

lemma W_succT (n : ℕ) (r : Row) : W (n + 1) r = T (W n) r := by
  rw [W_succ, T_eq]

/-- The index of a row in the tables. -/
def idx (r : Row) : ℕ := 16 * (r 0).val + 8 * (r 1).val + 4 * (r 2).val + 2 * (r 3).val + (r 4).val

/-- W(1, r), by the index of r. -/
def L1 : List ℕ := [32, 24, 20, 8, 20, 16, 8, 4, 20, 15, 13, 5, 8, 6, 4, 2, 24, 18, 15, 6, 16, 13, 6, 3, 8, 6, 5,
    2, 4, 3, 2, 1]

def t1 (r : Row) : ℕ := L1.getD (idx r) 0

/-- W(2, r), by the index of r. -/
def L2 : List ℕ := [337, 205, 142, 31, 141, 93, 30, 10, 142, 86, 65, 13, 30, 18, 9, 3, 205, 125, 86, 19, 93, 65,
    18, 6, 31, 19, 13, 3, 10, 6, 3, 1]

def t2 (r : Row) : ℕ := L2.getD (idx r) 0

/-- W(3, r), by the index of r. -/
def L3 : List ℕ := [2058, 1069, 634, 86, 630, 356, 80, 20, 634, 328, 223, 26, 80, 40, 16, 4, 1069, 558, 328, 45,
    356, 223, 40, 10, 86, 45, 26, 4, 20, 10, 4, 1]

def t3 (r : Row) : ℕ := L3.getD (idx r) 0

/-- W(4, r), by the index of r. -/
def L4 : List ℕ := [9109, 4176, 2176, 196, 2169, 1083, 175, 35, 2176, 1000, 627, 45, 175, 75, 25, 5, 4176, 1931,
    1000, 90, 1083, 627, 75, 15, 196, 90, 45, 5, 35, 15, 5, 1]

def t4 (r : Row) : ℕ := L4.getD (idx r) 0

/-- W(5, r), by the index of r. -/
def L5 : List ℕ := [32636, 13517, 6320, 392, 6320, 2858, 336, 56, 6320, 2655, 1565, 71, 336, 126, 36, 6, 13517,
    5676, 2655, 161, 2858, 1565, 126, 21, 392, 161, 71, 6, 56, 21, 6, 1]

def t5 (r : Row) : ℕ := L5.getD (idx r) 0

/-- W(6, r), by the index of r. -/
def L6 : List ℕ := [100843, 38408, 16399, 714, 16441, 6871, 588, 84, 16399, 6437, 3621, 105, 588, 196, 49, 7,
    38408, 14929, 6437, 266, 6871, 3621, 196, 28, 714, 266, 105, 7, 84, 28, 7, 1]

def t6 (r : Row) : ℕ := L6.getD (idx r) 0

/-- W(7, r), by the index of r. -/
def L7 : List ℕ := [279718, 99370, 39330, 1212, 39498, 15514, 960, 120, 39330, 14674, 7971, 148, 960, 288, 64, 8,
    99370, 36306, 14674, 414, 15514, 7971, 288, 36, 1212, 414, 148, 8, 120, 36, 8, 1]

def t7 (r : Row) : ℕ := L7.getD (idx r) 0

/-- W(8, r), by the index of r. -/
def L8 : List ℕ := [715685, 239963, 89199, 1947, 89661, 33569, 1485, 165, 89199, 32063, 16975, 201, 1485, 405, 81,
    9, 239963, 83457, 32063, 615, 33569, 16975, 405, 45, 1947, 615, 201, 9, 165, 45, 9, 1]

def t8 (r : Row) : ℕ := L8.getD (idx r) 0

/-- W(9, r), by the index of r. -/
def L9 : List ℕ := [1722176, 550502, 194404, 2992, 195460, 70580, 2200, 220, 194404, 68039, 35361, 265, 2200, 550,
    100, 10, 550502, 184174, 68039, 880, 70580, 35361, 550, 55, 2992, 880, 265, 10, 220, 55,
    10, 1]

def t9 (r : Row) : ℕ := L9.getD (idx r) 0

/-- W(10, r), by the index of r. -/
def L10 : List ℕ := [3954037, 1215503, 411908, 4433, 414053, 145593, 3146, 286, 411908, 141512, 72593, 341, 3146,
    726, 121, 11, 1215503, 394605, 141512, 1221, 145593, 72593, 726, 66, 4433, 1221, 341, 11,
    286, 66, 11, 1]

def t10 (r : Row) : ℕ := L10.getD (idx r) 0

def t0 (_ : Row) : ℕ := 1

lemma W0f : W 0 = t0 := by
  funext r
  rw [W_zero]
  rfl

lemma check1 : ∀ x0 x1 x2 x3 x4 : Fin 2, T t0 ![x0, x1, x2, x3, x4] = t1 ![x0, x1, x2, x3, x4] := by
  decide +kernel

lemma W1f : W 1 = t1 := by
  funext r
  rw [W_succT, W0f, row_eta r]
  exact check1 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma check2 : ∀ x0 x1 x2 x3 x4 : Fin 2, T t1 ![x0, x1, x2, x3, x4] = t2 ![x0, x1, x2, x3, x4] := by
  decide +kernel

lemma W2f : W 2 = t2 := by
  funext r
  rw [W_succT, W1f, row_eta r]
  exact check2 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma check3 : ∀ x0 x1 x2 x3 x4 : Fin 2, T t2 ![x0, x1, x2, x3, x4] = t3 ![x0, x1, x2, x3, x4] := by
  decide +kernel

lemma W3f : W 3 = t3 := by
  funext r
  rw [W_succT, W2f, row_eta r]
  exact check3 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma check4 : ∀ x0 x1 x2 x3 x4 : Fin 2, T t3 ![x0, x1, x2, x3, x4] = t4 ![x0, x1, x2, x3, x4] := by
  decide +kernel

lemma W4f : W 4 = t4 := by
  funext r
  rw [W_succT, W3f, row_eta r]
  exact check4 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma check5 : ∀ x0 x1 x2 x3 x4 : Fin 2, T t4 ![x0, x1, x2, x3, x4] = t5 ![x0, x1, x2, x3, x4] := by
  decide +kernel

lemma W5f : W 5 = t5 := by
  funext r
  rw [W_succT, W4f, row_eta r]
  exact check5 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma check6 : ∀ x0 x1 x2 x3 x4 : Fin 2, T t5 ![x0, x1, x2, x3, x4] = t6 ![x0, x1, x2, x3, x4] := by
  decide +kernel

lemma W6f : W 6 = t6 := by
  funext r
  rw [W_succT, W5f, row_eta r]
  exact check6 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma check7 : ∀ x0 x1 x2 x3 x4 : Fin 2, T t6 ![x0, x1, x2, x3, x4] = t7 ![x0, x1, x2, x3, x4] := by
  decide +kernel

lemma W7f : W 7 = t7 := by
  funext r
  rw [W_succT, W6f, row_eta r]
  exact check7 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma check8 : ∀ x0 x1 x2 x3 x4 : Fin 2, T t7 ![x0, x1, x2, x3, x4] = t8 ![x0, x1, x2, x3, x4] := by
  decide +kernel

lemma W8f : W 8 = t8 := by
  funext r
  rw [W_succT, W7f, row_eta r]
  exact check8 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma check9 : ∀ x0 x1 x2 x3 x4 : Fin 2, T t8 ![x0, x1, x2, x3, x4] = t9 ![x0, x1, x2, x3, x4] := by
  decide +kernel

lemma W9f : W 9 = t9 := by
  funext r
  rw [W_succT, W8f, row_eta r]
  exact check9 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma check10 : ∀ x0 x1 x2 x3 x4 : Fin 2, T t9 ![x0, x1, x2, x3, x4] = t10 ![x0, x1, x2, x3, x4] := by
  decide +kernel

lemma W10f : W 10 = t10 := by
  funext r
  rw [W_succT, W9f, row_eta r]
  exact check10 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma check_rel : ∀ x0 x1 x2 x3 x4 : Fin 2, t10 ![x0, x1, x2, x3, x4] + 54 * t8 ![x0, x1, x2, x3, x4] + 294 * t6 ![x0, x1, x2, x3, x4] + 336 * t4 ![x0, x1, x2, x3, x4] + 81 * t2 ![x0, x1, x2, x3, x4] + 2 * t0 ![x0, x1, x2, x3, x4] = 11 * t9 ![x0, x1, x2, x3, x4] + 156 * t7 ![x0, x1, x2, x3, x4] + 378 * t5 ![x0, x1, x2, x3, x4] + 204 * t3 ![x0, x1, x2, x3, x4] + 19 * t1 ![x0, x1, x2, x3, x4] := by
  decide +kernel

/-- The per-row relation: the g.f. denominator annihilates W(k + 0), ..., W(k + 10). -/
lemma W_rec (k : ℕ) : ∀ r : Row, W (k + 10) r + 54 * W (k + 8) r + 294 * W (k + 6) r + 336 * W (k + 4) r + 81 * W (k + 2) r + 2 * W (k + 0) r = 11 * W (k + 9) r + 156 * W (k + 7) r + 378 * W (k + 5) r + 204 * W (k + 3) r + 19 * W (k + 1) r := by
  induction k with
  | zero =>
    intro r
    simp only [Nat.zero_add, W0f, W10f, W1f, W2f, W3f, W4f, W5f, W6f, W7f, W8f, W9f]
    rw [row_eta r]
    exact check_rel (r 0) (r 1) (r 2) (r 3) (r 4)
  | succ k ih =>
    intro r
    rw [show k + 1 + 0 = (k + 0) + 1 from rfl, show k + 1 + 1 = (k + 1) + 1 from rfl, show k + 1 + 2 = (k + 2) + 1 from rfl, show k + 1 + 3 = (k + 3) + 1 from rfl, show k + 1 + 4 = (k + 4) + 1 from rfl, show k + 1 + 5 = (k + 5) + 1 from rfl, show k + 1 + 6 = (k + 6) + 1 from rfl, show k + 1 + 7 = (k + 7) + 1 from rfl, show k + 1 + 8 = (k + 8) + 1 from rfl, show k + 1 + 9 = (k + 9) + 1 from rfl, show k + 1 + 10 = (k + 10) + 1 from rfl]
    rw [W_succ (k + 0), W_succ (k + 1), W_succ (k + 2), W_succ (k + 3), W_succ (k + 4), W_succ (k + 5), W_succ (k + 6), W_succ (k + 7), W_succ (k + 8), W_succ (k + 9), W_succ (k + 10)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs
    · exact ih s
    · simp

lemma cnt_rec (k : ℕ) : cnt (k + 10)  + 54 * cnt (k + 8)  + 294 * cnt (k + 6)  + 336 * cnt (k + 4)  + 81 * cnt (k + 2)  + 2 * cnt (k + 0)  = 11 * cnt (k + 9)  + 156 * cnt (k + 7)  + 378 * cnt (k + 5)  + 204 * cnt (k + 3)  + 19 * cnt (k + 1)  := by
  simp only [cnt_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => W_rec k r)

lemma sum_tab (t : Row → ℕ) : ∑ r : Row, t r = ∑ x0 : Fin 2, ∑ x1 : Fin 2, ∑ x2 : Fin 2, ∑ x3 : Fin 2, ∑ x4 : Fin 2, t ![x0, x1, x2, x3, x4] := sum_row t

lemma cnt0 : cnt 0 = 32 := by
  rw [cnt_sum, W0f, sum_tab]
  decide +kernel

lemma cnt1 : cnt 1 = 337 := by
  rw [cnt_sum, W1f, sum_tab]
  decide +kernel

lemma cnt2 : cnt 2 = 2058 := by
  rw [cnt_sum, W2f, sum_tab]
  decide +kernel

lemma cnt3 : cnt 3 = 9109 := by
  rw [cnt_sum, W3f, sum_tab]
  decide +kernel

lemma cnt4 : cnt 4 = 32636 := by
  rw [cnt_sum, W4f, sum_tab]
  decide +kernel

lemma cnt5 : cnt 5 = 100843 := by
  rw [cnt_sum, W5f, sum_tab]
  decide +kernel

lemma cnt6 : cnt 6 = 279718 := by
  rw [cnt_sum, W6f, sum_tab]
  decide +kernel

lemma cnt7 : cnt 7 = 715685 := by
  rw [cnt_sum, W7f, sum_tab]
  decide +kernel

lemma cnt8 : cnt 8 = 1722176 := by
  rw [cnt_sum, W8f, sum_tab]
  decide +kernel

lemma cnt9 : cnt 9 = 3954037 := by
  rw [cnt_sum, W9f, sum_tab]
  decide +kernel

lemma cnt10 : cnt 10 = 8757506 := by
  rw [cnt_sum, W10f, sum_tab]
  decide +kernel

lemma a_cast (n : ℕ) : (a n : ℚ) = (cnt n : ℚ) := by
  rw [a_eq]

lemma a_rec (k : ℕ) : (a (k + 10) : ℚ) + 54 * (a (k + 8) : ℚ) + 294 * (a (k + 6) : ℚ) + 336 * (a (k + 4) : ℚ) + 81 * (a (k + 2) : ℚ) + 2 * (a (k + 0) : ℚ) = 11 * (a (k + 9) : ℚ) + 156 * (a (k + 7) : ℚ) + 378 * (a (k + 5) : ℚ) + 204 * (a (k + 3) : ℚ) + 19 * (a (k + 1) : ℚ) := by
  simp only [a_cast]
  have h : cnt (k + 10) + 54 * cnt (k + 8) + 294 * cnt (k + 6) + 336 * cnt (k + 4) + 81 * cnt (k + 2) + 2 * cnt (k + 0) = 11 * cnt (k + 9) + 156 * cnt (k + 7) + 378 * cnt (k + 5) + 204 * cnt (k + 3) + 19 * cnt (k + 1) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using cnt_rec (k + 0)
  have h' : ((cnt (k + 10) : ℕ) : ℚ) + 54 * ((cnt (k + 8) : ℕ) : ℚ) + 294 * ((cnt (k + 6) : ℕ) : ℚ) + 336 * ((cnt (k + 4) : ℕ) : ℚ) + 81 * ((cnt (k + 2) : ℕ) : ℚ) + 2 * ((cnt (k + 0) : ℕ) : ℚ) = 11 * ((cnt (k + 9) : ℕ) : ℚ) + 156 * ((cnt (k + 7) : ℕ) : ℚ) + 378 * ((cnt (k + 5) : ℕ) : ℚ) + 204 * ((cnt (k + 3) : ℕ) : ℚ) + 19 * ((cnt (k + 1) : ℕ) : ℚ) := by exact_mod_cast h
  linear_combination h'

lemma a0 : (a 0 : ℚ) = 32 := by
  rw [a_cast, cnt0]
  norm_num

lemma a1 : (a 1 : ℚ) = 337 := by
  rw [a_cast, cnt1]
  norm_num

lemma a2 : (a 2 : ℚ) = 2058 := by
  rw [a_cast, cnt2]
  norm_num

lemma a3 : (a 3 : ℚ) = 9109 := by
  rw [a_cast, cnt3]
  norm_num

lemma a4 : (a 4 : ℚ) = 32636 := by
  rw [a_cast, cnt4]
  norm_num

lemma a5 : (a 5 : ℚ) = 100843 := by
  rw [a_cast, cnt5]
  norm_num

lemma a6 : (a 6 : ℚ) = 279718 := by
  rw [a_cast, cnt6]
  norm_num

lemma a7 : (a 7 : ℚ) = 715685 := by
  rw [a_cast, cnt7]
  norm_num

lemma a8 : (a 8 : ℚ) = 1722176 := by
  rw [a_cast, cnt8]
  norm_num

lemma a9 : (a 9 : ℚ) = 3954037 := by
  rw [a_cast, cnt9]
  norm_num

lemma a10 : (a 10 : ℚ) = 8757506 := by
  rw [a_cast, cnt10]
  norm_num

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) ^ 9 * (1 - 2 * X)) =
      X * (337 - 1649 * X + 4669 * X ^ 2 - 9003 * X ^ 3 + 11763 * X ^ 4 - 10549 * X ^ 5 +
      6447 * X ^ 6 - 2573 * X ^ 7 + 606 * X ^ 8 - 64 * X ^ 9) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 9 * (1 - 2 * X)) = A - C (11 : ℚ) * (A * X ^ 1) + C (54 : ℚ) * (A * X ^ 2) - C (156 : ℚ) * (A * X ^ 3) + C (294 : ℚ) * (A * X ^ 4) - C (378 : ℚ) * (A * X ^ 5) + C (336 : ℚ) * (A * X ^ 6) - C (204 : ℚ) * (A * X ^ 7) + C (81 : ℚ) * (A * X ^ 8) - C (19 : ℚ) * (A * X ^ 9) + C (2 : ℚ) * (A * X ^ 10) := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2, show (C (11 : ℚ) : ℚ⟦X⟧) = 11 from map_ofNat C 11, show (C (19 : ℚ) : ℚ⟦X⟧) = 19 from map_ofNat C 19, show (C (54 : ℚ) : ℚ⟦X⟧) = 54 from map_ofNat C 54, show (C (81 : ℚ) : ℚ⟦X⟧) = 81 from map_ofNat C 81, show (C (156 : ℚ) : ℚ⟦X⟧) = 156 from map_ofNat C 156, show (C (204 : ℚ) : ℚ⟦X⟧) = 204 from map_ofNat C 204, show (C (294 : ℚ) : ℚ⟦X⟧) = 294 from map_ofNat C 294, show (C (336 : ℚ) : ℚ⟦X⟧) = 336 from map_ofNat C 336, show (C (378 : ℚ) : ℚ⟦X⟧) = 378 from map_ofNat C 378]
    ring
  have e2 : (X * (337 - 1649 * X + 4669 * X ^ 2 - 9003 * X ^ 3 + 11763 * X ^ 4 - 10549 * X ^ 5 +
      6447 * X ^ 6 - 2573 * X ^ 7 + 606 * X ^ 8 - 64 * X ^ 9) : ℚ⟦X⟧) = C (337 : ℚ) * X ^ 1 - C (1649 : ℚ) * X ^ 2 + C (4669 : ℚ) * X ^ 3 - C (9003 : ℚ) * X ^ 4 + C (11763 : ℚ) * X ^ 5 - C (10549 : ℚ) * X ^ 6 + C (6447 : ℚ) * X ^ 7 - C (2573 : ℚ) * X ^ 8 + C (606 : ℚ) * X ^ 9 - C (64 : ℚ) * X ^ 10 := by
    rw [show (C (64 : ℚ) : ℚ⟦X⟧) = 64 from map_ofNat C 64, show (C (337 : ℚ) : ℚ⟦X⟧) = 337 from map_ofNat C 337, show (C (606 : ℚ) : ℚ⟦X⟧) = 606 from map_ofNat C 606, show (C (1649 : ℚ) : ℚ⟦X⟧) = 1649 from map_ofNat C 1649, show (C (2573 : ℚ) : ℚ⟦X⟧) = 2573 from map_ofNat C 2573, show (C (4669 : ℚ) : ℚ⟦X⟧) = 4669 from map_ofNat C 4669, show (C (6447 : ℚ) : ℚ⟦X⟧) = 6447 from map_ofNat C 6447, show (C (9003 : ℚ) : ℚ⟦X⟧) = 9003 from map_ofNat C 9003, show (C (10549 : ℚ) : ℚ⟦X⟧) = 10549 from map_ofNat C 10549, show (C (11763 : ℚ) : ℚ⟦X⟧) = 11763 from map_ofNat C 11763]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> norm_num only [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, if_true, if_false]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
    have h' := (show (a (k + 11) : ℚ) + 54 * (a (k + 9) : ℚ) + 294 * (a (k + 7) : ℚ) + 336 * (a (k + 5) : ℚ) + 81 * (a (k + 3) : ℚ) + 2 * (a (k + 1) : ℚ) = 11 * (a (k + 10) : ℚ) + 156 * (a (k + 8) : ℚ) + 378 * (a (k + 6) : ℚ) + 204 * (a (k + 4) : ℚ) + 19 * (a (k + 2) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (k + 1))
    simp only [show k + 11 - 1 = k + 10 by omega, show k + 11 - 2 = k + 9 by omega, show k + 11 - 3 = k + 8 by omega, show k + 11 - 4 = k + 7 by omega, show k + 11 - 5 = k + 6 by omega, show k + 11 - 6 = k + 5 by omega, show k + 11 - 7 = k + 4 by omega, show k + 11 - 8 = k + 3 by omega, show k + 11 - 9 = k + 2 by omega, show k + 11 - 10 = k + 1 by omega, show ¬ (k + 11 = 0) by omega, show ¬ (k + 10 = 0) by omega, show ¬ (k + 9 = 0) by omega, show ¬ (k + 8 = 0) by omega, show ¬ (k + 7 = 0) by omega, show ¬ (k + 6 = 0) by omega, show ¬ (k + 5 = 0) by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 3 = 0) by omega, show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega, show 1 ≤ k + 11 by omega, show 2 ≤ k + 11 by omega, show 3 ≤ k + 11 by omega, show 4 ≤ k + 11 by omega, show 5 ≤ k + 11 by omega, show 6 ≤ k + 11 by omega, show 7 ≤ k + 11 by omega, show 8 ≤ k + 11 by omega, show 9 ≤ k + 11 by omega, show 10 ≤ k + 11 by omega, show ¬ (k + 11 = 0) by omega, show ¬ (k + 11 = 1) by omega, show ¬ (k + 11 = 2) by omega, show ¬ (k + 11 = 3) by omega, show ¬ (k + 11 = 4) by omega, show ¬ (k + 11 = 5) by omega, show ¬ (k + 11 = 6) by omega, show ¬ (k + 11 = 7) by omega, show ¬ (k + 11 = 8) by omega, show ¬ (k + 11 = 9) by omega, show ¬ (k + 11 = 10) by omega, if_true, if_false]
    linear_combination h'

def closed_Q (n : ℕ) : ℚ := (20160 * (1369 * 2 ^ n - 1365) - 18907464 * n - 6363848 * n ^ 2 - 1352064 * n ^ 3 -
        190036 * n ^ 4 - 16401 * n ^ 5 - 637 * n ^ 6 + 9 * n ^ 7 + n ^ 8) / 2520

lemma closed_Q_rec (m : ℕ) : closed_Q (m + 10) - 11 * closed_Q (m + 9) + 54 * closed_Q (m + 8) - 156 * closed_Q (m + 7) + 294 * closed_Q (m + 6) - 378 * closed_Q (m + 5) + 336 * closed_Q (m + 4) - 204 * closed_Q (m + 3) + 81 * closed_Q (m + 2) - 19 * closed_Q (m + 1) + 2 * closed_Q (m + 0) = 0 := by
  unfold closed_Q
  push_cast
  ring

lemma closed_key (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = closed_Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 11 with h | h
    · interval_cases n
      · have hk : (a 1 : ℚ) = 337 := by exact_mod_cast a1
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 2 : ℚ) = 2058 := by exact_mod_cast a2
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 3 : ℚ) = 9109 := by exact_mod_cast a3
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 4 : ℚ) = 32636 := by exact_mod_cast a4
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 5 : ℚ) = 100843 := by exact_mod_cast a5
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 6 : ℚ) = 279718 := by exact_mod_cast a6
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 7 : ℚ) = 715685 := by exact_mod_cast a7
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 8 : ℚ) = 1722176 := by exact_mod_cast a8
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 9 : ℚ) = 3954037 := by exact_mod_cast a9
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 10 : ℚ) = 8757506 := by exact_mod_cast a10
        rw [hk]
        unfold closed_Q
        norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
      have hR := (show (a (m + 11) : ℚ) + 54 * (a (m + 9) : ℚ) + 294 * (a (m + 7) : ℚ) + 336 * (a (m + 5) : ℚ) + 81 * (a (m + 3) : ℚ) + 2 * (a (m + 1) : ℚ) = 11 * (a (m + 10) : ℚ) + 156 * (a (m + 8) : ℚ) + 378 * (a (m + 6) : ℚ) + 204 * (a (m + 4) : ℚ) + 19 * (a (m + 2) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (m + 1))
      have hR' : (a (m + 11) : ℚ) + 54 * (a (m + 9) : ℚ) + 294 * (a (m + 7) : ℚ) + 336 * (a (m + 5) : ℚ) + 81 * (a (m + 3) : ℚ) + 2 * (a (m + 1) : ℚ) = 11 * (a (m + 10) : ℚ) + 156 * (a (m + 8) : ℚ) + 378 * (a (m + 6) : ℚ) + 204 * (a (m + 4) : ℚ) + 19 * (a (m + 2) : ℚ) := by exact_mod_cast hR
      have h1 := ih (m + 10) (by omega) (by omega)
      have h2 := ih (m + 9) (by omega) (by omega)
      have h3 := ih (m + 8) (by omega) (by omega)
      have h4 := ih (m + 7) (by omega) (by omega)
      have h5 := ih (m + 6) (by omega) (by omega)
      have h6 := ih (m + 5) (by omega) (by omega)
      have h7 := ih (m + 4) (by omega) (by omega)
      have h8 := ih (m + 3) (by omega) (by omega)
      have h9 := ih (m + 2) (by omega) (by omega)
      have h10 := ih (m + 1) (by omega) (by omega)
      have hG := closed_Q_rec (m + 1)
      simp only [show m + 1 + 10 = m + 11 from rfl, show m + 1 + 9 = m + 10 from rfl, show m + 1 + 8 = m + 9 from rfl, show m + 1 + 7 = m + 8 from rfl, show m + 1 + 6 = m + 7 from rfl, show m + 1 + 5 = m + 6 from rfl, show m + 1 + 4 = m + 5 from rfl, show m + 1 + 3 = m + 4 from rfl, show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl, show m + 1 + 0 = m + 1 from rfl] at hG
      linear_combination hR' + (-(-11 : ℚ)) * h1 + (-(54 : ℚ)) * h2 + (-(-156 : ℚ)) * h3 + (-(294 : ℚ)) * h4 + (-(-378 : ℚ)) * h5 + (-(336 : ℚ)) * h6 + (-(-204 : ℚ)) * h7 + (-(81 : ℚ)) * h8 + (-(-19 : ℚ)) * h9 + (-(2 : ℚ)) * h10 + (-1 : ℚ) * hG

theorem closed : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
      (20160 * (1369 * 2 ^ n - 1365) - 18907464 * n - 6363848 * n ^ 2 - 1352064 * n ^ 3 -
        190036 * n ^ 4 - 16401 * n ^ 5 - 637 * n ^ 6 + 9 * n ^ 7 + n ^ 8) / 2520 := fun n hn => closed_key n hn

/-- Controls: the entry's data. -/
theorem controls : a 1 = 337 ∧ a 2 = 2058 ∧ a 3 = 9109 ∧ a 4 = 32636 ∧ a 5 = 100843 ∧ a 6 = 279718 ∧ a 7 = 715685 ∧ a 8 = 1722176 ∧ a 9 = 3954037 ∧ a 10 = 8757506 ∧ a 11 = 18871133 ∧ a 12 = 39828260 ∧ a 13 = 82762159 ∧ a 14 = 170015870 ∧ a 15 = 346360653 ∧ a 16 = 701430696 ∧ a 17 = 1414589161 ∧ a 18 = 2844655514 ∧ a 19 = 5709353797 ∧ a 20 = 11444200908 ∧ a 21 = 22920272755 ∧ a 22 = 45879723734 ∧ a 23 = 91806810133 := by
  have v11 : (a 11 : ℚ) = 18871133 := by
    have h := a_rec 1
    simp only [Nat.reduceAdd] at h
    rw [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] at h
    linarith
  have v12 : (a 12 : ℚ) = 39828260 := by
    have h := a_rec 2
    simp only [Nat.reduceAdd] at h
    rw [a2, a3, a4, a5, a6, a7, a8, a9, a10, v11] at h
    linarith
  have v13 : (a 13 : ℚ) = 82762159 := by
    have h := a_rec 3
    simp only [Nat.reduceAdd] at h
    rw [a3, a4, a5, a6, a7, a8, a9, a10, v11, v12] at h
    linarith
  have v14 : (a 14 : ℚ) = 170015870 := by
    have h := a_rec 4
    simp only [Nat.reduceAdd] at h
    rw [a4, a5, a6, a7, a8, a9, a10, v11, v12, v13] at h
    linarith
  have v15 : (a 15 : ℚ) = 346360653 := by
    have h := a_rec 5
    simp only [Nat.reduceAdd] at h
    rw [a5, a6, a7, a8, a9, a10, v11, v12, v13, v14] at h
    linarith
  have v16 : (a 16 : ℚ) = 701430696 := by
    have h := a_rec 6
    simp only [Nat.reduceAdd] at h
    rw [a6, a7, a8, a9, a10, v11, v12, v13, v14, v15] at h
    linarith
  have v17 : (a 17 : ℚ) = 1414589161 := by
    have h := a_rec 7
    simp only [Nat.reduceAdd] at h
    rw [a7, a8, a9, a10, v11, v12, v13, v14, v15, v16] at h
    linarith
  have v18 : (a 18 : ℚ) = 2844655514 := by
    have h := a_rec 8
    simp only [Nat.reduceAdd] at h
    rw [a8, a9, a10, v11, v12, v13, v14, v15, v16, v17] at h
    linarith
  have v19 : (a 19 : ℚ) = 5709353797 := by
    have h := a_rec 9
    simp only [Nat.reduceAdd] at h
    rw [a9, a10, v11, v12, v13, v14, v15, v16, v17, v18] at h
    linarith
  have v20 : (a 20 : ℚ) = 11444200908 := by
    have h := a_rec 10
    simp only [Nat.reduceAdd] at h
    rw [a10, v11, v12, v13, v14, v15, v16, v17, v18, v19] at h
    linarith
  have v21 : (a 21 : ℚ) = 22920272755 := by
    have h := a_rec 11
    simp only [Nat.reduceAdd] at h
    rw [v11, v12, v13, v14, v15, v16, v17, v18, v19, v20] at h
    linarith
  have v22 : (a 22 : ℚ) = 45879723734 := by
    have h := a_rec 12
    simp only [Nat.reduceAdd] at h
    rw [v12, v13, v14, v15, v16, v17, v18, v19, v20, v21] at h
    linarith
  have v23 : (a 23 : ℚ) = 91806810133 := by
    have h := a_rec 13
    simp only [Nat.reduceAdd] at h
    rw [v13, v14, v15, v16, v17, v18, v19, v20, v21, v22] at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast a1
  · exact_mod_cast a2
  · exact_mod_cast a3
  · exact_mod_cast a4
  · exact_mod_cast a5
  · exact_mod_cast a6
  · exact_mod_cast a7
  · exact_mod_cast a8
  · exact_mod_cast a9
  · exact_mod_cast a10
  · exact_mod_cast v11
  · exact_mod_cast v12
  · exact_mod_cast v13
  · exact_mod_cast v14
  · exact_mod_cast v15
  · exact_mod_cast v16
  · exact_mod_cast v17
  · exact_mod_cast v18
  · exact_mod_cast v19
  · exact_mod_cast v20
  · exact_mod_cast v21
  · exact_mod_cast v22
  · exact_mod_cast v23

/-- The conjunction stated as `main`. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 9 * (1 - 2 * X)) =
        X * (337 - 1649 * X + 4669 * X ^ 2 - 9003 * X ^ 3 + 11763 * X ^ 4 - 10549 * X ^ 5 +
          6447 * X ^ 6 - 2573 * X ^ 7 + 606 * X ^ 8 - 64 * X ^ 9) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
          (20160 * (1369 * 2 ^ n - 1365) - 18907464 * n - 6363848 * n ^ 2 - 1352064 * n ^ 3 -
            190036 * n ^ 4 - 16401 * n ^ 5 - 637 * n ^ 6 + 9 * n ^ 7 + n ^ 8) / 2520 :=
  ⟨gf, closed⟩

end OMA.S_oeis_a251271

theorem OMA.solution : type_of% @OMA.S_oeis_a251271.main :=
  OMA.S_oeis_a251271.conjecture
