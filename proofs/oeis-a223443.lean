import OMAStatements.S_oeis_a223443

namespace OMA.S_oeis_a223443

open PowerSeries Finset









/-- Rows valid and consecutive rows compatible. -/
def Valid {n : ℕ} (f : Fin n → Fin 15 × Fin 15) : Prop :=
  (∀ i, hrow (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 15 × Fin 15) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 15 × Fin 15)).filter (fun f => Valid f ∧ f 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 15 × Fin 15) (g : Fin (n + 1) → Fin 15 × Fin 15) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 15 × Fin 15) ↔
      hrow x ∧ ok x (g 0) ∧ Valid g := by
  constructor
  · rintro ⟨hr, h⟩
    refine ⟨by simpa using hr 0, ?_, fun i => by simpa using hr i.succ, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨hx, h0, hg, hgo⟩
    refine ⟨?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hx
      | succ i => simpa using hg i
    · intro i j hij
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
          exact hgo i j (by simp at hij; omega)

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 15 × Fin 15, W n r := by
  unfold a W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h4⟩
    exact ⟨⟨h1, h2⟩, h4⟩
  · rintro ⟨⟨h1, h2⟩, h4⟩
    exact ⟨⟨h1, h2⟩, h4⟩

lemma W_zero (r : Fin 15 × Fin 15) : W 0 r = if hrow r then 1 else 0 := by
  unfold W
  split_ifs with hr
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => r, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hf⟩
      funext i
      rw [Fin.fin_one_eq_zero i, hf]
    · rintro rfl
      refine ⟨⟨fun _ => hr, ?_⟩, rfl⟩
      intro i j hij
      have := j.isLt
      omega
  · rw [Finset.card_eq_zero]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨h1, _⟩, h0⟩
    exact hr (h0 ▸ h1 0)

/-- Prepending the row r to an array with n + 1 rows. -/
def consEmb (n : ℕ) (r : Fin 15 × Fin 15) :
    (Fin (n + 1) → Fin 15 × Fin 15) ↪ (Fin (n + 2) → Fin 15 × Fin 15) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 15 × Fin 15) (g : Fin (n + 1) → Fin 15 × Fin 15) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Fin 15 × Fin 15) :
    W (n + 1) r = ∑ s : Fin 15 × Fin 15, if hrow r ∧ ok r s then W n s else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 15 × Fin 15)).filter
      (fun f => Valid f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 15 × Fin 15)).filter
        (fun g => (hrow r ∧ ok r (g 0)) ∧ Valid g)).map (consEmb n r)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons r (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        exact ⟨⟨hv.1, hv.2.1⟩, hv.2.2⟩
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, ⟨⟨h1, h2⟩, hg⟩, rfl⟩
      exact ⟨(valid_cons r g).2 ⟨h1, h2, hg⟩, by simp⟩
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
      exact ⟨⟨⟨hrs.1, h0 ▸ hrs.2⟩, hg⟩, h0⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨⟨h1, h2⟩, _⟩, h0⟩
    exact hrs ⟨h1, h0 ▸ h2⟩

/-- The adjacency as one bit mask: y is adjacent to x when bit 15 x + y of `MASK` is set. -/
def MASK : ℕ := 1685048089498992972103682980619283765769290407244720116117864742918

/-- Fast adjacency. -/
def adjB (x y : Fin 15) : Bool := Nat.testBit MASK (15 * x.val + y.val)

set_option maxHeartbeats 4000000 in
lemma adj_iff : ∀ x y : Fin 15, adj x y ↔ adjB x y = true := by
  decide +kernel

/-- Fast row test. -/
def hrowB (r : Fin 15 × Fin 15) : Bool := adjB r.1 r.2

/-- Fast compatibility test. -/
def okB (r s : Fin 15 × Fin 15) : Bool :=
  adjB r.1 s.1 && (adjB r.2 s.2)

lemma hrow_iff (r : Fin 15 × Fin 15) : hrow r ↔ hrowB r = true := by
  simp only [hrow, hrowB, adj_iff, Bool.and_eq_true]

lemma ok_iff (r s : Fin 15 × Fin 15) : ok r s ↔ okB r s = true := by
  simp only [ok, okB, adj_iff, Bool.and_eq_true]

lemma W_invalid (n : ℕ) (r : Fin 15 × Fin 15) (h : hrowB r = false) : W n r = 0 := by
  unfold W
  rw [Finset.card_eq_zero]
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro ⟨⟨h1, _⟩, h0⟩
  have h2 := (hrow_iff r).1 (h0 ▸ h1 0)
  rw [h] at h2
  exact Bool.false_ne_true h2

lemma W_zeroB (r : Fin 15 × Fin 15) : W 0 r = if hrowB r = true then 1 else 0 := by
  rw [W_zero]
  by_cases hr : hrowB r = true
  · rw [if_pos hr, if_pos ((hrow_iff r).2 hr)]
  · rw [if_neg hr, if_neg (fun h => hr ((hrow_iff r).1 h))]

/-- The labels adjacent to c. -/
def N (c : Fin 15) : Finset (Fin 15) := univ.filter (fun y => adjB c y = true)

lemma sum_N (c : Fin 15) (F : Fin 15 → ℕ) :
    ∑ y ∈ N c, F y = ∑ y : Fin 15, if adjB c y = true then F y else 0 :=
  Finset.sum_filter _ _

lemma ite_and (b1 b2 : Bool) (X : ℕ) :
    (if b1 = true then (if b2 = true then X else 0) else 0) = if (b1 && b2) = true then X else 0 := by
  cases b1 <;> cases b2 <;> rfl

/-- The sum of g over the valid rows allowed below r, enumerated entry by entry: each entry runs
over the neighbors of one entry (of r or of the row being built), and the other conditions on it
are tested. -/
def succSum (r : Fin 15 × Fin 15) (g : Fin 15 × Fin 15 → ℕ) : ℕ :=
  ∑ x ∈ N r.1, ∑ y ∈ N x, (if adjB r.2 y = true then g (x, y) else 0)

lemma cond_split (r : Fin 15 × Fin 15) (x y : Fin 15) :
    (okB r (x, y) && hrowB (x, y)) = (adjB r.1 x && ((adjB x y && (adjB r.2 y)))) := by
  simp only [okB, hrowB]
  generalize adjB r.1 x = b0
  generalize adjB r.2 y = b1
  generalize adjB x y = b2
  revert b0 b1 b2
  decide

lemma succ_eq (r : Fin 15 × Fin 15) (hr : hrowB r = true) (g : Fin 15 × Fin 15 → ℕ)
    (hg : ∀ s, hrowB s = false → g s = 0) :
    (∑ s : Fin 15 × Fin 15, if hrow r ∧ ok r s then g s else 0) = succSum r g := by
  have e1 : ∀ s : Fin 15 × Fin 15, (if hrow r ∧ ok r s then g s else 0) =
      if (okB r s && hrowB s) = true then g s else 0 := by
    intro s
    by_cases hs : hrowB s = true
    · simp [hrow_iff, ok_iff, hr, hs]
    · have h0 : g s = 0 := hg s (by simpa using hs)
      simp [h0]
  rw [Finset.sum_congr rfl (fun s _ => e1 s)]
  simp only [Fintype.sum_prod_type]
  unfold succSum
  simp only [sum_N, ite_and]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h0 : adjB r.1 x = true
  · rw [if_pos h0]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h1 : (adjB x y && (adjB r.2 y)) = true
    · rw [if_pos h1]
      simp [cond_split, h0, h1]
    · rw [if_neg h1]
      simp [cond_split, h0, h1]
  · rw [if_neg h0]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    simp [cond_split, h0]

/-- W(1, r) as a table (0 for an invalid row). -/
def tab1 : Fin 15 → Fin 15 → ℕ :=
  ![![0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 0, 0, 0],
    ![0, 5, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 5, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0],
    ![0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0]]

/-- W(1, r). -/
def dtab1 (r : Fin 15 × Fin 15) : ℕ := if hrowB r = true then tab1 r.1 r.2 else 0

/-- W(2, r) as a table (0 for an invalid row). -/
def tab2 : Fin 15 → Fin 15 → ℕ :=
  ![![0, 18, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![18, 0, 0, 20, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![18, 0, 0, 0, 0, 0, 0, 0, 0, 20, 20, 0, 0, 0, 0],
    ![0, 20, 0, 0, 0, 11, 11, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 20, 0, 0, 0, 0, 0, 11, 11, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 11, 11, 0, 0],
    ![0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 11],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0]]

/-- W(2, r). -/
def dtab2 (r : Fin 15 × Fin 15) : ℕ := if hrowB r = true then tab2 r.1 r.2 else 0

set_option maxHeartbeats 4000000 in
lemma check1 : ∀ x y : Fin 15, adjB x y = true →
    succSum (x, y) (fun s => if hrowB s = true then 1 else 0) = dtab1 (x, y) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check2 : ∀ x y : Fin 15, adjB x y = true →
    succSum (x, y) dtab1 = dtab2 (x, y) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ x y : Fin 15, adjB x y = true →
    succSum (x, y) dtab2 + 8 * dtab1 (x, y) = 6 * dtab2 (x, y) := by
  decide +kernel

lemma W_zero_fun : W 0 = fun s => if hrowB s = true then 1 else 0 := funext W_zeroB

lemma W1 (r : Fin 15 × Fin 15) : W 1 r = dtab1 r := by
  by_cases hr : hrowB r = true
  · rw [W_succ, succ_eq r hr (W 0) (W_invalid 0), W_zero_fun]
    obtain ⟨x, y⟩ := r
    have h := hr
    simp only [hrowB, Bool.and_eq_true] at h
    exact check1 x y h
  · have hf : hrowB r = false := by simpa using hr
    rw [W_invalid 1 r hf]
    simp [dtab1, hf]

lemma W1_fun : W 1 = dtab1 := funext W1

lemma W2 (r : Fin 15 × Fin 15) : W 2 r = dtab2 r := by
  by_cases hr : hrowB r = true
  · rw [show W 2 r = W (1 + 1) r from rfl, W_succ, succ_eq r hr (W 1) (W_invalid 1), W1_fun]
    obtain ⟨x, y⟩ := r
    have h := hr
    simp only [hrowB, Bool.and_eq_true] at h
    exact check2 x y h
  · have hf : hrowB r = false := by simpa using hr
    rw [W_invalid 2 r hf]
    simp [dtab2, hf]

lemma W2_fun : W 2 = dtab2 := funext W2

lemma W_rec (n : ℕ) (r : Fin 15 × Fin 15) :
    W (n + 3) r + 8 * W (n + 1) r = 6 * W (n + 2) r := by
  induction n generalizing r with
  | zero =>
    by_cases hr : hrowB r = true
    · rw [show W (0 + 2) r = W 2 r from rfl,
        show W (0 + 1) r = W 1 r from rfl,
        show W (0 + 3) r = W (2 + 1) r from rfl,
        W_succ 2 r,
        succ_eq r hr (W 2) (W_invalid 2),
        W2_fun,
        W1_fun]
      obtain ⟨x, y⟩ := r
      have h := hr
      simp only [hrowB, Bool.and_eq_true] at h
      exact base_check x y h
    · have hf : hrowB r = false := by simpa using hr
      rw [W_invalid _ r hf, W_invalid _ r hf, W_invalid _ r hf]
  | succ n ih =>
    rw [W_succ (n + 3), W_succ (n + 1), W_succ (n + 2)]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hc : hrow r ∧ ok r s
    · simp only [if_pos hc]
      exact ih s
    · simp [hc]

lemma a_rec (n : ℕ) : a (n + 4) + 8 * a (n + 2) = 6 * a (n + 3) := by
  rw [a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => W_rec n r)

set_option maxHeartbeats 4000000 in
lemma a_one : a 1 = 28 := by
  rw [a_succ]
  simp only [W_zeroB]
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma a_two : a 2 = 104 := by
  rw [a_succ]
  simp only [W1]
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma a_three : a 3 = 408 := by
  rw [a_succ]
  simp only [W2]
  decide +kernel

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 4x(7 - 16x + 2x^2) / ((1 - 2x)(1 - 4x)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - 2 * X) * (1 - 4 * X)) = 4 * X * (7 - 16 * X + 2 * X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - 2 * X) * (1 - 4 * X)) = A - A * X ^ 1 * C 6 + A * X ^ 2 * C 8 := by
    rw [show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6,
      show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8]
    ring
  have e2 : (4 * X * (7 - 16 * X + 2 * X ^ 2) : ℚ⟦X⟧) = X ^ 1 * C 28 - X ^ 2 * C 64 + X ^ 3 * C 8 := by
    rw [show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8,
      show (C (28 : ℚ) : ℚ⟦X⟧) = 28 from map_ofNat C 28,
      show (C (64 : ℚ) : ℚ⟦X⟧) = 64 from map_ofNat C 64]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | n
  · simp
  · simp [a_one] <;> norm_num
  · simp [a_one, a_two] <;> norm_num
  · simp [a_one, a_two, a_three] <;> norm_num
  · have hq : ((a (n + 4) : ℕ) : ℚ) + 8 * a (n + 2) = 6 * a (n + 3) := by
      exact_mod_cast a_rec n
    simp only [if_false, if_true, show ¬ (n + 4 = 0) by omega,
      show 1 ≤ n + 4 by omega,
      show ¬ (n + 4 - 1 = 0) by omega,
      show n + 4 - 1 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show 2 ≤ n + 4 by omega,
      show ¬ (n + 4 - 2 = 0) by omega,
      show n + 4 - 2 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show ¬ (n + 4 = 1) by omega,
      show ¬ (n + 4 = 2) by omega,
      show ¬ (n + 4 = 3) by omega]
    linear_combination hq

/-- Barker's closed form a(n) = 2^(n-2) (4 + 25 2^n), for n > 1. -/
theorem closed_form : ∀ n : ℕ, 1 < n → a n = 2 ^ (n - 2) * (4 + 25 * 2 ^ n) := by
  have key : ∀ k, a (k + 2) = 2 ^ k * (4 + 25 * 2 ^ (k + 2)) ∧
      a (k + 3) = 2 ^ (k + 1) * (4 + 25 * 2 ^ (k + 3)) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [a_two] <;> norm_num
      · rw [a_three] <;> norm_num
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hz : ((a (k + 4) : ℕ) : ℤ) + 8 * a (k + 2) = 6 * a (k + 3) := by
        exact_mod_cast a_rec k
      have h1 : ((a (k + 2) : ℕ) : ℤ) = 2 ^ k * (4 + 25 * 2 ^ (k + 2)) := by exact_mod_cast ih.1
      have h2 : ((a (k + 3) : ℕ) : ℤ) = 2 ^ (k + 1) * (4 + 25 * 2 ^ (k + 3)) := by
        exact_mod_cast ih.2
      have h3 : ((a (k + 4) : ℕ) : ℤ) = 2 ^ (k + 2) * (4 + 25 * 2 ^ (k + 4)) := by
        linear_combination hz - 8 * h1 + 6 * h2
      show a (k + 4) = 2 ^ (k + 2) * (4 + 25 * 2 ^ (k + 4))
      exact_mod_cast h3
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 2 = k by omega]
  exact (key k).1

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - 2 * X) * (1 - 4 * X)) = 4 * X * (7 - 16 * X + 2 * X ^ 2) ∧
    ∀ n : ℕ, 1 < n → a n = 2 ^ (n - 2) * (4 + 25 * 2 ^ n) :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..15), from the recurrence and a(1), ..., a(3). -/
theorem controls :
    a 1 = 28 ∧ a 2 = 104 ∧ a 3 = 408 ∧ a 4 = 1616 ∧ a 5 = 6432 ∧ a 6 = 25664 ∧ a 7 = 102528 ∧ a 8 = 409856 ∧ a 9 = 1638912 ∧ a 10 = 6554624 ∧ a 11 = 26216448 ∧ a 12 = 104861696 ∧ a 13 = 419438592 ∧ a 14 = 1677737984 ∧ a 15 = 6710919168 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6; have r7 := a_rec 7; have r8 := a_rec 8; have r9 := a_rec 9; have r10 := a_rec 10; have r11 := a_rec 11
  have h1 := a_one; have h2 := a_two; have h3 := a_three
  norm_num at r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  omega

/-- Controls on the graph: 14 edges, and the number of neighbors of each label. -/
theorem graph_controls : edges.length = 14 ∧
    ∀ x : Fin 15, ((univ : Finset (Fin 15)).filter (adj x)).card =
      [2, 3, 3, 3, 3, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1].getD x.val 0 := by
  decide +kernel

end OMA.S_oeis_a223443

theorem OMA.solution : type_of% @OMA.S_oeis_a223443.main :=
  OMA.S_oeis_a223443.conjecture
