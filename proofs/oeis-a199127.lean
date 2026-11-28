import OMAStatements.S_oeis_a199127

-- Problem: A199127: Number of n X 2 0..2 arrays with values 0..2 introduced in row major order,
-- the number of instances of each value within one of each other, and no element equal to any
-- horizontal or vertical neighbor.
-- Credit: @EmadY (the owner of the agent is credited as the solver)
--
-- Proof idea. Every row holds two distinct values, so it misses exactly one value m_i. Given a
-- row, the next row is determined by the value it misses (the three possible successors of
-- (x, y), missing z, are (y, x), (y, z) and (z, x)). The order condition forces the first row
-- to be (0, 1), so it misses 2, and every later row is unconstrained by it. Hence the arrays
-- correspond exactly to the words m of length n over 0..2 with m 0 = 2, and value v occurs
-- n - #{i : m_i = v} times in the array, so the array is balanced exactly when m is. Counting
-- the balanced words with the multinomial coefficients gives
--   a(3t+3) = (3t+2)!/((t+1)!^2 t!) = a(3t+2),  a(3t+4) = (3t+4)!/((t+2)! (t+1)!^2),
-- so a(k+1)/a(k) is 3(3t+4)/(t+2), (3t+2)/(t+1) or 1 according as k = 3t+3, 3t+1 or 3t+2.
-- A208881(t+1) is a multinomial count with the same value as a(3t+2), and both recurrences
-- reduce to polynomial identities once these ratios are substituted.

namespace OMA.S_oeis_a199127

open Nat

/-! ## Rows and the value each row misses -/

/-- The value missing from a row `(x, y)` of two distinct values. -/
def miss (x y : Fin 3) : Fin 3 := -(x + y)

/-- The row that follows the row `(x, y)` and misses the value `m`. -/
def next (x y m : Fin 3) : Fin 3 × Fin 3 :=
  if m = miss x y then (y, x) else if m = x then (y, miss x y) else (miss x y, x)

lemma next_spec : ∀ x y m : Fin 3, x ≠ y →
    (next x y m).1 ≠ (next x y m).2 ∧ x ≠ (next x y m).1 ∧ y ≠ (next x y m).2 ∧
      miss (next x y m).1 (next x y m).2 = m := by decide

lemma next_unique : ∀ x y c d : Fin 3, x ≠ y → c ≠ d → x ≠ c → y ≠ d →
    next x y (miss c d) = (c, d) := by decide

lemma row_count : ∀ x y v : Fin 3, x ≠ y →
    ((if x = v then 1 else 0) + (if y = v then 1 else 0) + (if miss x y = v then 1 else 0) : ℕ)
      = 1 := by decide

/-- The rows built from a sequence of missing values, starting from the row `(0, 1)`. -/
def rows (m : ℕ → Fin 3) : ℕ → Fin 3 × Fin 3
  | 0 => (0, 1)
  | k + 1 => next (rows m k).1 (rows m k).2 (m (k + 1))

lemma rows_succ (m : ℕ → Fin 3) (k : ℕ) :
    rows m (k + 1) = next (rows m k).1 (rows m k).2 (m (k + 1)) := rfl

lemma rows_ne (m : ℕ → Fin 3) : ∀ k, (rows m k).1 ≠ (rows m k).2
  | 0 => by show (0 : Fin 3) ≠ 1; decide
  | k + 1 => by rw [rows_succ]; exact (next_spec _ _ (m (k + 1)) (rows_ne m k)).1

lemma rows_step (m : ℕ → Fin 3) (k : ℕ) :
    (rows m k).1 ≠ (rows m (k + 1)).1 ∧ (rows m k).2 ≠ (rows m (k + 1)).2 ∧
      miss (rows m (k + 1)).1 (rows m (k + 1)).2 = m (k + 1) := by
  rw [rows_succ]
  exact (next_spec _ _ (m (k + 1)) (rows_ne m k)).2

/-- A word of length `n`, extended by zeros to all of `ℕ`. -/
def ext {n : ℕ} (m : Fin n → Fin 3) (k : ℕ) : Fin 3 := if h : k < n then m ⟨k, h⟩ else 0

/-- The array whose rows are built from the missing values `m`. -/
def build {n : ℕ} (m : Fin n → Fin 3) (i : Fin n) (j : Fin 2) : Fin 3 :=
  if j = 0 then (rows (ext m) i).1 else (rows (ext m) i).2

/-- The missing value of each row of an array. -/
def toMiss {n : ℕ} (A : Fin n → Fin 2 → Fin 3) (i : Fin n) : Fin 3 := miss (A i 0) (A i 1)

lemma numOcc_add {n : ℕ} (A : Fin n → Fin 2 → Fin 3) (hA : ∀ i, A i 0 ≠ A i 1) (v : Fin 3) :
    numOcc A v + wordOcc (toMiss A) v = n := by
  unfold numOcc wordOcc toMiss
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  calc _ = ∑ _i : Fin n, 1 := Finset.sum_congr rfl (fun i _ => by
          rw [Fin.sum_univ_two]; exact row_count _ _ _ (hA i))
    _ = n := by simp

lemma bal_iff {n : ℕ} (A : Fin n → Fin 2 → Fin 3) (hA : ∀ i, A i 0 ≠ A i 1) :
    (∀ u v : Fin 3, numOcc A u ≤ numOcc A v + 1) ↔
      (∀ u v : Fin 3, wordOcc (toMiss A) u ≤ wordOcc (toMiss A) v + 1) := by
  constructor
  · intro h u v
    have := h v u
    have e1 := numOcc_add A hA u
    have e2 := numOcc_add A hA v
    omega
  · intro h u v
    have := h v u
    have e1 := numOcc_add A hA u
    have e2 := numOcc_add A hA v
    omega

lemma first_row {L : ℕ} (A : Fin (L + 1) → Fin 2 → Fin 3)
    (hR : ∀ i : Fin (L + 1), ∀ j : Fin 2, ∀ v : Fin 3, v < A i j →
      ∃ i' : Fin (L + 1), ∃ j' : Fin 2, (i' < i ∨ (i' = i ∧ j' < j)) ∧ A i' j' = v)
    (hH : ∀ i : Fin (L + 1), A i 0 ≠ A i 1) :
    A 0 0 = 0 ∧ A 0 1 = 1 := by
  have e0 : A 0 0 = 0 := by
    by_contra hne
    obtain ⟨i', j', hlt, -⟩ := hR 0 0 0 (by
      rcases Fin.pos_iff_ne_zero.mpr hne with h; exact h)
    rcases hlt with h | ⟨-, h⟩
    · exact absurd h (Fin.not_lt_zero _)
    · exact absurd h (Fin.not_lt_zero _)
  refine ⟨e0, ?_⟩
  have h1 : A 0 1 ≠ 0 := e0 ▸ (hH 0).symm
  by_contra hne
  have h2 : A 0 1 = 2 := by
    revert h1 hne; generalize A 0 1 = x; intro h1 hne; fin_cases x <;> simp_all
  obtain ⟨i', j', hlt, hv⟩ := hR 0 1 1 (by rw [h2]; decide)
  rcases hlt with h | ⟨rfl, h⟩
  · exact absurd h (Fin.not_lt_zero _)
  · have : j' = 0 := by
      revert h; generalize j' = y; intro h; fin_cases y <;> simp_all
    subst this
    rw [e0] at hv
    exact absurd hv (by decide)

lemma rows_toMiss {L : ℕ} (A : Fin (L + 1) → Fin 2 → Fin 3) (hf : A 0 0 = 0 ∧ A 0 1 = 1)
    (hH : ∀ i, A i 0 ≠ A i 1)
    (hV : ∀ i i' : Fin (L + 1), i.val + 1 = i'.val → ∀ j, A i j ≠ A i' j) :
    ∀ k (hk : k < L + 1), rows (ext (toMiss A)) k = (A ⟨k, hk⟩ 0, A ⟨k, hk⟩ 1)
  | 0, hk => by
    show ((0 : Fin 3), (1 : Fin 3)) = _
    rw [← hf.1, ← hf.2]; rfl
  | k + 1, hk => by
    rw [rows_succ, rows_toMiss A hf hH hV k (by omega)]
    simp only [ext, dif_pos hk, toMiss]
    exact next_unique _ _ _ _ (hH _) (hH _) (hV _ _ rfl 0) (hV _ _ rfl 1)

lemma build_toMiss {L : ℕ} (A : Fin (L + 1) → Fin 2 → Fin 3) (hf : A 0 0 = 0 ∧ A 0 1 = 1)
    (hH : ∀ i, A i 0 ≠ A i 1)
    (hV : ∀ i i' : Fin (L + 1), i.val + 1 = i'.val → ∀ j, A i j ≠ A i' j) :
    build (toMiss A) = A := by
  funext i j
  have := rows_toMiss A hf hH hV i.val i.isLt
  simp only [Fin.eta] at this
  unfold build
  rw [this]
  fin_cases j <;> rfl

lemma toMiss_build {L : ℕ} (m : Fin (L + 1) → Fin 3) (h0 : m 0 = 2) :
    toMiss (build m) = m := by
  funext i
  rcases i with ⟨_ | k, hk⟩
  · show miss (0 : Fin 3) 1 = m ⟨0, hk⟩
    rw [show (⟨0, hk⟩ : Fin (L + 1)) = 0 from rfl, h0]; decide
  · have := (rows_step (ext m) k).2.2
    simp only [ext, dif_pos hk] at this
    exact this

lemma build_valid {L : ℕ} (m : Fin (L + 1) → Fin 3) :
    (∀ i : Fin (L + 1), ∀ j : Fin 2, ∀ v : Fin 3, v < build m i j →
      ∃ i' : Fin (L + 1), ∃ j' : Fin 2, (i' < i ∨ (i' = i ∧ j' < j)) ∧ build m i' j' = v) ∧
    (∀ i : Fin (L + 1), build m i 0 ≠ build m i 1) ∧
    (∀ i i' : Fin (L + 1), i.val + 1 = i'.val → ∀ j : Fin 2, build m i j ≠ build m i' j) := by
  have b00 : build m 0 0 = 0 := rfl
  have b01 : build m 0 1 = 1 := rfl
  refine ⟨?_, fun i => rows_ne _ _, ?_⟩
  · intro i j v hv
    by_cases hi : i = 0
    · subst hi
      fin_cases j
      · simp [b00] at hv
      · refine ⟨0, 0, Or.inr ⟨rfl, by decide⟩, ?_⟩
        rw [b00]
        simp only [Fin.mk_one, b01] at hv
        revert hv; generalize v = x; intro hv; fin_cases x <;> simp_all
    · have hi' : (0 : Fin (L + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
      have hv2 : v ≠ 2 := by
        intro h; subst h
        exact absurd hv (not_lt.mpr (Fin.le_last _))
      revert hv hv2; generalize v = x; intro hv hv2
      fin_cases x
      · exact ⟨0, 0, Or.inl hi', b00⟩
      · exact ⟨0, 1, Or.inl hi', b01⟩
      · exact absurd rfl hv2
  · intro i i' hii' j
    have hs := rows_step (ext m) i.val
    have : (i'.val : ℕ) = i.val + 1 := hii'.symm
    unfold build
    rw [this]
    fin_cases j
    · exact hs.1
    · exact hs.2.1

/-- A199127(L+1) counts the words of missing values that start with 2 and are balanced. -/
lemma a_succ_eq (L : ℕ) : a (L + 1) =
    (Finset.univ.filter (fun m : Fin (L + 1) → Fin 3 =>
      m 0 = 2 ∧ ∀ u v : Fin 3, wordOcc m u ≤ wordOcc m v + 1)).card := by
  unfold a
  apply Finset.card_nbij' toMiss build
  · intro A hA
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hA ⊢
    obtain ⟨hR, hB, hH, hV⟩ := hA
    have hf := first_row A hR hH
    refine ⟨?_, (bal_iff A hH).1 hB⟩
    show miss (A 0 0) (A 0 1) = 2
    rw [hf.1, hf.2]; decide
  · intro m hm
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hm ⊢
    obtain ⟨hR, hH, hV⟩ := build_valid m
    refine ⟨hR, ?_, hH, hV⟩
    rw [bal_iff _ hH, toMiss_build m hm.1]
    exact hm.2
  · intro A hA
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hA
    obtain ⟨hR, hB, hH, hV⟩ := hA
    exact build_toMiss A (first_row A hR hH) hH hV
  · intro m hm
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hm
    exact toMiss_build m hm.1

/-! ## Words with given numbers of each letter -/

/-- The number of words of length `L` over 0..2 with `p` zeros, `q` ones and `r` twos. -/
def W (L p q r : ℕ) : ℕ :=
  ∑ w : Fin L → Fin 3, if wordOcc w 0 = p ∧ wordOcc w 1 = q ∧ wordOcc w 2 = r then 1 else 0

lemma wordOcc_cons {L : ℕ} (x : Fin 3) (w : Fin L → Fin 3) (v : Fin 3) :
    wordOcc (Fin.cons x w : Fin (L + 1) → Fin 3) v = wordOcc w v + if x = v then 1 else 0 := by
  unfold wordOcc
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

lemma sum_cons {L : ℕ} (f : (Fin (L + 1) → Fin 3) → ℕ) :
    ∑ w : Fin (L + 1) → Fin 3, f w = ∑ x : Fin 3, ∑ w : Fin L → Fin 3, f (Fin.cons x w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Fin 3)) _ _ (fun _ => rfl)).symm

lemma wordOcc_total {L : ℕ} (w : Fin L → Fin 3) :
    wordOcc w 0 + wordOcc w 1 + wordOcc w 2 = L := by
  unfold wordOcc
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  calc _ = ∑ _k : Fin L, 1 := Finset.sum_congr rfl (fun k _ => by
          generalize w k = x; fin_cases x <;> rfl)
    _ = L := by simp

lemma W_zero : W 0 0 0 0 = 1 := by
  simp [W, wordOcc]

lemma ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then 1 else 0 : ℕ) = if Q then 1 else 0 := by
  by_cases hQ : Q
  · rw [if_pos (h.2 hQ), if_pos hQ]
  · rw [if_neg (fun hP => hQ (h.1 hP)), if_neg hQ]

lemma W_succ (L p q r : ℕ) : W (L + 1) p q r =
    (if p = 0 then 0 else W L (p - 1) q r) + (if q = 0 then 0 else W L p (q - 1) r) +
      (if r = 0 then 0 else W L p q (r - 1)) := by
  unfold W
  rw [sum_cons, Fin.sum_univ_three]
  have h01 : ((0 : Fin 3) = 1) = False := eq_false (by decide)
  have h02 : ((0 : Fin 3) = 2) = False := eq_false (by decide)
  have h10 : ((1 : Fin 3) = 0) = False := eq_false (by decide)
  have h12 : ((1 : Fin 3) = 2) = False := eq_false (by decide)
  have h20 : ((2 : Fin 3) = 0) = False := eq_false (by decide)
  have h21 : ((2 : Fin 3) = 1) = False := eq_false (by decide)
  simp only [wordOcc_cons, h01, h02, h10, h12, h20, h21, if_true, if_false, add_zero]
  congr 1
  congr 1
  · split_ifs with hp
    · refine Finset.sum_eq_zero (fun w _ => if_neg ?_)
      omega
    · refine Finset.sum_congr rfl (fun w _ => ite_iff ?_)
      constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨by omega, h2, h3⟩
  · split_ifs with hq
    · refine Finset.sum_eq_zero (fun w _ => if_neg ?_)
      omega
    · refine Finset.sum_congr rfl (fun w _ => ite_iff ?_)
      constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, by omega, h3⟩
  · split_ifs with hr
    · refine Finset.sum_eq_zero (fun w _ => if_neg ?_)
      omega
    · refine Finset.sum_congr rfl (fun w _ => ite_iff ?_)
      constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, h2, by omega⟩

/-- The multinomial count. -/
lemma W_mul : ∀ L p q r : ℕ, p + q + r = L → W L p q r * (p ! * q ! * r !) = L !
  | 0, p, q, r, h => by
    obtain ⟨rfl, rfl, rfl⟩ : p = 0 ∧ q = 0 ∧ r = 0 := ⟨by omega, by omega, by omega⟩
    simp [W_zero]
  | L + 1, p, q, r, h => by
    have tp : (if p = 0 then 0 else W L (p - 1) q r) * (p ! * q ! * r !) = p * L ! := by
      rcases p with _ | p
      · simp
      · rw [if_neg (Nat.succ_ne_zero p), Nat.add_sub_cancel, Nat.factorial_succ,
          ← W_mul L p q r (by omega)]
        ring
    have tq : (if q = 0 then 0 else W L p (q - 1) r) * (p ! * q ! * r !) = q * L ! := by
      rcases q with _ | q
      · simp
      · rw [if_neg (Nat.succ_ne_zero q), Nat.add_sub_cancel, Nat.factorial_succ,
          ← W_mul L p q r (by omega)]
        ring
    have tr : (if r = 0 then 0 else W L p q (r - 1)) * (p ! * q ! * r !) = r * L ! := by
      rcases r with _ | r
      · simp
      · rw [if_neg (Nat.succ_ne_zero r), Nat.add_sub_cancel, Nat.factorial_succ,
          ← W_mul L p q r (by omega)]
        ring
    rw [W_succ, add_mul, add_mul, tp, tq, tr, Nat.factorial_succ, ← h]
    ring

/-! ## A199127 as a sum over words of missing values -/

lemma forall_fin3 (f : Fin 3 → ℕ) : (∀ u v : Fin 3, f u ≤ f v + 1) ↔
    (f 0 ≤ f 1 + 1 ∧ f 1 ≤ f 0 + 1 ∧ f 0 ≤ f 2 + 1 ∧ f 2 ≤ f 0 + 1 ∧
      f 1 ≤ f 2 + 1 ∧ f 2 ≤ f 1 + 1) := by
  constructor
  · intro h; exact ⟨h 0 1, h 1 0, h 0 2, h 2 0, h 1 2, h 2 1⟩
  · rintro ⟨h01, h10, h02, h20, h12, h21⟩ u v
    fin_cases u <;> fin_cases v <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      omega

/-- The balance condition on the counts `(p, q, r + 1)` of a word starting with 2. -/
def Bal2 (p q r : ℕ) : Prop :=
  p ≤ q + 1 ∧ q ≤ p + 1 ∧ p ≤ r + 1 + 1 ∧ r + 1 ≤ p + 1 ∧ q ≤ r + 1 + 1 ∧ r + 1 ≤ q + 1

instance (p q r : ℕ) : Decidable (Bal2 p q r) := by unfold Bal2; infer_instance

lemma a_succ_sum (L : ℕ) : a (L + 1) =
    ∑ w : Fin L → Fin 3, if Bal2 (wordOcc w 0) (wordOcc w 1) (wordOcc w 2) then 1 else 0 := by
  rw [a_succ_eq, Finset.card_filter, sum_cons, Fin.sum_univ_three]
  have z0 : ∀ w : Fin L → Fin 3, (if (Fin.cons 0 w : Fin (L + 1) → Fin 3) 0 = 2 ∧
      ∀ u v : Fin 3, wordOcc (Fin.cons 0 w : Fin (L + 1) → Fin 3) u ≤
        wordOcc (Fin.cons 0 w : Fin (L + 1) → Fin 3) v + 1 then 1 else 0 : ℕ) = 0 :=
    fun w => if_neg (by rw [Fin.cons_zero]; exact fun h => absurd h.1 (by decide))
  have z1 : ∀ w : Fin L → Fin 3, (if (Fin.cons 1 w : Fin (L + 1) → Fin 3) 0 = 2 ∧
      ∀ u v : Fin 3, wordOcc (Fin.cons 1 w : Fin (L + 1) → Fin 3) u ≤
        wordOcc (Fin.cons 1 w : Fin (L + 1) → Fin 3) v + 1 then 1 else 0 : ℕ) = 0 :=
    fun w => if_neg (by rw [Fin.cons_zero]; exact fun h => absurd h.1 (by decide))
  simp only [z0, z1, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl (fun w _ => ite_iff ?_)
  rw [Fin.cons_zero, forall_fin3]
  simp only [wordOcc_cons]
  have h20 : ((2 : Fin 3) = 0) = False := eq_false (by decide)
  have h21 : ((2 : Fin 3) = 1) = False := eq_false (by decide)
  simp only [h20, h21, if_true, if_false, add_zero, true_and, Bal2]

/-- Splitting the indicator of a set of three count vectors. -/
lemma sum_split3 {L : ℕ} (P : ℕ → ℕ → ℕ → Prop) [∀ p q r, Decidable (P p q r)]
    (p₁ q₁ r₁ p₂ q₂ r₂ p₃ q₃ r₃ : ℕ)
    (h : ∀ p q r, p + q + r = L → (if P p q r then 1 else 0 : ℕ) =
      (if p = p₁ ∧ q = q₁ ∧ r = r₁ then 1 else 0) + (if p = p₂ ∧ q = q₂ ∧ r = r₂ then 1 else 0) +
        (if p = p₃ ∧ q = q₃ ∧ r = r₃ then 1 else 0)) :
    (∑ w : Fin L → Fin 3, if P (wordOcc w 0) (wordOcc w 1) (wordOcc w 2) then 1 else 0) =
      W L p₁ q₁ r₁ + W L p₂ q₂ r₂ + W L p₃ q₃ r₃ := by
  unfold W
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w _ => h _ _ _ (wordOcc_total w))

lemma a_one : a 1 = 1 := by
  rw [a_succ_sum, ← W_zero]
  unfold W
  refine Finset.sum_congr rfl (fun w _ => ite_iff ?_)
  have := wordOcc_total w
  unfold Bal2; omega

lemma a_two : a 2 = 2 := by
  rw [a_succ_sum]
  have h := sum_split3 (L := 1) Bal2 1 0 0 0 1 0 5 5 5 (fun p q r hs => by
    by_cases h : Bal2 p q r
    · rw [if_pos h]; unfold Bal2 at h; split_ifs <;> omega
    · rw [if_neg h]; unfold Bal2 at h; split_ifs <;> omega)
  rw [h]
  have e1 := W_mul 1 1 0 0 rfl
  have e2 := W_mul 1 0 1 0 rfl
  have e3 : W 1 5 5 5 = 0 := by
    unfold W
    refine Finset.sum_eq_zero (fun w _ => if_neg ?_)
    have := wordOcc_total w
    omega
  simp at e1 e2
  rw [e1, e2, e3]

lemma a_3t3 (t : ℕ) : a (3 * t + 3) = W (3 * t + 2) (t + 1) (t + 1) t := by
  rw [show 3 * t + 3 = (3 * t + 2) + 1 from rfl, a_succ_sum]
  unfold W
  refine Finset.sum_congr rfl (fun w _ => ite_iff ?_)
  have := wordOcc_total w
  unfold Bal2; omega

lemma a_3t4 (t : ℕ) : a (3 * t + 4) = W (3 * t + 3) (t + 2) (t + 1) t +
    W (3 * t + 3) (t + 1) (t + 2) t + W (3 * t + 3) (t + 1) (t + 1) (t + 1) := by
  rw [show 3 * t + 4 = (3 * t + 3) + 1 from rfl, a_succ_sum]
  exact sum_split3 _ _ _ _ _ _ _ _ _ _ (fun p q r hs => by
    by_cases h : Bal2 p q r
    · rw [if_pos h]; unfold Bal2 at h; split_ifs <;> omega
    · rw [if_neg h]; unfold Bal2 at h; split_ifs <;> omega)

lemma a_3t5 (t : ℕ) : a (3 * t + 5) = W (3 * t + 4) (t + 2) (t + 2) t +
    W (3 * t + 4) (t + 2) (t + 1) (t + 1) + W (3 * t + 4) (t + 1) (t + 2) (t + 1) := by
  rw [show 3 * t + 5 = (3 * t + 4) + 1 from rfl, a_succ_sum]
  exact sum_split3 _ _ _ _ _ _ _ _ _ _ (fun p q r hs => by
    by_cases h : Bal2 p q r
    · rw [if_pos h]; unfold Bal2 at h; split_ifs <;> omega
    · rw [if_neg h]; unfold Bal2 at h; split_ifs <;> omega)

/-! ## Closed forms -/

lemma cf0 (t : ℕ) : a (3 * t + 3) * ((t + 1)! * (t + 1)! * t !) = (3 * t + 2)! := by
  rw [a_3t3]; exact W_mul _ _ _ _ (by ring)

lemma cf1 (t : ℕ) : a (3 * t + 4) * ((t + 2)! * (t + 1)! * (t + 1)!) = (3 * t + 4)! := by
  have e1 := W_mul (3 * t + 3) (t + 2) (t + 1) t (by ring)
  have e2 := W_mul (3 * t + 3) (t + 1) (t + 2) t (by ring)
  have e3 := W_mul (3 * t + 3) (t + 1) (t + 1) (t + 1) (by ring)
  have f2 : (t + 2)! = (t + 2) * (t + 1)! := Nat.factorial_succ (t + 1)
  have g : (3 * t + 4)! = (3 * t + 4) * (3 * t + 3)! := Nat.factorial_succ (3 * t + 3)
  rw [a_3t4, g]
  calc _ = (t + 1) * (W (3 * t + 3) (t + 2) (t + 1) t * ((t + 2)! * (t + 1)! * t !)) +
        (t + 1) * (W (3 * t + 3) (t + 1) (t + 2) t * ((t + 1)! * (t + 2)! * t !)) +
        (t + 2) * (W (3 * t + 3) (t + 1) (t + 1) (t + 1) * ((t + 1)! * (t + 1)! * (t + 1)!)) := by
          rw [f2, Nat.factorial_succ t]; ring
    _ = _ := by rw [e1, e2, e3]; ring

lemma cf2 (t : ℕ) : a (3 * t + 5) * ((t + 2)! * (t + 2)! * (t + 1)!) = (3 * t + 5)! := by
  have e1 := W_mul (3 * t + 4) (t + 2) (t + 2) t (by ring)
  have e2 := W_mul (3 * t + 4) (t + 2) (t + 1) (t + 1) (by ring)
  have e3 := W_mul (3 * t + 4) (t + 1) (t + 2) (t + 1) (by ring)
  have f2 : (t + 2)! = (t + 2) * (t + 1)! := Nat.factorial_succ (t + 1)
  have g : (3 * t + 5)! = (3 * t + 5) * (3 * t + 4)! := Nat.factorial_succ (3 * t + 4)
  rw [a_3t5, g]
  calc _ = (t + 1) * (W (3 * t + 4) (t + 2) (t + 2) t * ((t + 2)! * (t + 2)! * t !)) +
        (t + 2) * (W (3 * t + 4) (t + 2) (t + 1) (t + 1) * ((t + 2)! * (t + 1)! * (t + 1)!)) +
        (t + 2) * (W (3 * t + 4) (t + 1) (t + 2) (t + 1) * ((t + 1)! * (t + 2)! * (t + 1)!)) := by
          rw [f2, Nat.factorial_succ t]; ring
    _ = _ := by rw [e1, e2, e3]; ring

/-- a(3t+2) has the same closed form as a(3t+3). -/
lemma cf2' (t : ℕ) : a (3 * t + 2) * ((t + 1)! * (t + 1)! * t !) = (3 * t + 2)! := by
  rcases t with _ | s
  · rw [a_two]; rfl
  · have := cf2 s
    rw [show 3 * (s + 1) + 2 = 3 * s + 5 by ring]
    exact this

/-! ## Ratios of consecutive terms -/

lemma ratio0 (t : ℕ) : a (3 * t + 3) = a (3 * t + 2) := by
  have h1 := cf0 t
  have h2 := cf2' t
  have hP : 0 < (t + 1)! * (t + 1)! * t ! := by positivity
  exact Nat.eq_of_mul_eq_mul_right hP (h1.trans h2.symm)

lemma ratio1 (t : ℕ) : a (3 * t + 4) * (t + 2) = 3 * (3 * t + 4) * a (3 * t + 3) := by
  have h1 := cf1 t
  have h0 := cf0 t
  have f1 : (t + 1)! = (t + 1) * t ! := Nat.factorial_succ t
  have f2 : (t + 2)! = (t + 2) * (t + 1)! := Nat.factorial_succ (t + 1)
  have g : (3 * t + 4)! = (3 * t + 4) * ((3 * t + 3) * (3 * t + 2)!) := by
    rw [show (3 * t + 4)! = (3 * t + 4) * (3 * t + 3)! from Nat.factorial_succ (3 * t + 3),
      show (3 * t + 3)! = (3 * t + 3) * (3 * t + 2)! from Nat.factorial_succ (3 * t + 2)]
  have hP : 0 < (t + 1) * ((t + 1)! * (t + 1)! * t !) := by positivity
  apply Nat.eq_of_mul_eq_mul_right hP
  calc a (3 * t + 4) * (t + 2) * ((t + 1) * ((t + 1)! * (t + 1)! * t !))
      = a (3 * t + 4) * ((t + 2)! * (t + 1)! * (t + 1)!) := by rw [f2, f1]; ring
    _ = (3 * t + 4) * ((3 * t + 3) * (a (3 * t + 3) * ((t + 1)! * (t + 1)! * t !))) := by
        rw [h1, g, h0]
    _ = 3 * (3 * t + 4) * a (3 * t + 3) * ((t + 1) * ((t + 1)! * (t + 1)! * t !)) := by ring

lemma ratio2 (t : ℕ) : a (3 * t + 2) * (t + 1) = (3 * t + 2) * a (3 * t + 1) := by
  rcases t with _ | s
  · rw [a_two, a_one]
  · have h2 := cf2 s
    have h1 := cf1 s
    have f2 : (s + 2)! = (s + 2) * (s + 1)! := Nat.factorial_succ (s + 1)
    have g : (3 * s + 5)! = (3 * s + 5) * (3 * s + 4)! := Nat.factorial_succ (3 * s + 4)
    rw [show 3 * (s + 1) + 2 = 3 * s + 5 by ring, show 3 * (s + 1) + 1 = 3 * s + 4 by ring]
    have hP : 0 < (s + 2)! * (s + 1)! * (s + 1)! := by positivity
    apply Nat.eq_of_mul_eq_mul_right hP
    calc a (3 * s + 5) * (s + 1 + 1) * ((s + 2)! * (s + 1)! * (s + 1)!)
        = a (3 * s + 5) * ((s + 2)! * (s + 2)! * (s + 1)!) := by rw [f2]; ring
      _ = (3 * s + 5) * (a (3 * s + 4) * ((s + 2)! * (s + 1)! * (s + 1)!)) := by
          rw [h2, g, h1]
      _ = (3 * (s + 1) + 2) * a (3 * s + 4) * ((s + 2)! * (s + 1)! * (s + 1)!) := by ring

lemma q0 (t k k' : ℕ) (hk : k = 3 * t + 2) (hk' : k' = 3 * t + 3) :
    (a k' : ℚ) = a k := by
  subst hk hk'; exact_mod_cast ratio0 t

lemma q1 (t k k' : ℕ) (hk : k = 3 * t + 3) (hk' : k' = 3 * t + 4) :
    (a k' : ℚ) = 3 * (3 * t + 4) / (t + 2) * a k := by
  subst hk hk'
  have h : ((a (3 * t + 4) : ℕ) : ℚ) * ((t : ℚ) + 2) = 3 * (3 * t + 4) * a (3 * t + 3) := by
    exact_mod_cast ratio1 t
  have ht : (t : ℚ) + 2 ≠ 0 := by positivity
  field_simp
  linarith

lemma q2 (t k k' : ℕ) (hk : k = 3 * t + 1) (hk' : k' = 3 * t + 2) :
    (a k' : ℚ) = (3 * t + 2) / (t + 1) * a k := by
  subst hk hk'
  have h : ((a (3 * t + 2) : ℕ) : ℚ) * ((t : ℚ) + 1) = (3 * t + 2) * a (3 * t + 1) := by
    exact_mod_cast ratio2 t
  have ht : (t : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  linarith

/-! ## A208881 -/

lemma A208881_filter (N L s : ℕ) (hN : N = L + 1) :
    (Finset.univ.filter (fun w : Fin N → Fin 3 =>
      (∀ v : Fin 3, wordOcc w v = s + 1) ∧ ∀ h : 0 < N, w ⟨0, h⟩ = 0)).card =
      W L s (s + 1) (s + 1) := by
  subst hN
  rw [Finset.card_filter, sum_cons, Fin.sum_univ_three]
  have h01 : ((0 : Fin 3) = 1) = False := eq_false (by decide)
  have h02 : ((0 : Fin 3) = 2) = False := eq_false (by decide)
  have h10 : ((1 : Fin 3) = 0) = False := eq_false (by decide)
  have h20 : ((2 : Fin 3) = 0) = False := eq_false (by decide)
  have hc : ∀ (x : Fin 3) (w : Fin L → Fin 3),
      ((∀ h : 0 < L + 1, (Fin.cons x w : Fin (L + 1) → Fin 3) ⟨0, h⟩ = 0) ↔ x = 0) :=
    fun x w => ⟨fun h => h (Nat.succ_pos L), fun h _ => h⟩
  simp only [hc, h10, h20, and_false, if_false, Finset.sum_const_zero, add_zero, and_true]
  unfold W
  refine Finset.sum_congr rfl (fun w _ => ite_iff ?_)
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [wordOcc_cons, h01, h02, if_true, if_false, add_zero] at h0 h1 h2
    exact ⟨by omega, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩ v
    rw [wordOcc_cons]
    fin_cases v
    · simp only [Fin.zero_eta, if_true, h0]
    · simp only [Fin.mk_one, h01, if_false, add_zero, h1]
    · simp only [Fin.reduceFinMk, h02, if_false, add_zero, h2]

lemma A208881_succ (s : ℕ) : A208881 (s + 1) = W (3 * s + 2) s (s + 1) (s + 1) :=
  A208881_filter _ _ _ (by ring)

/-! ## The three conjectures -/

lemma conj1 (n : ℕ) : a (3 * n + 2) = A208881 (n + 1) ∧ a (3 * n + 3) = A208881 (n + 1) := by
  have hW := W_mul (3 * n + 2) n (n + 1) (n + 1) (by ring)
  rw [← A208881_succ] at hW
  have hP : 0 < (n + 1)! * (n + 1)! * n ! := by positivity
  have hW' : A208881 (n + 1) * ((n + 1)! * (n + 1)! * n !) = (3 * n + 2)! := by
    rw [← hW]; ring
  exact ⟨Nat.eq_of_mul_eq_mul_right hP ((cf2' n).trans hW'.symm),
    Nat.eq_of_mul_eq_mul_right hP ((cf0 n).trans hW'.symm)⟩

lemma rec1_q (n : ℕ) (hn : 5 ≤ n) :
    -(458 * (n : ℚ) - 1205) * ((n : ℚ) + 2) * ((n : ℚ) + 1) * (a n : ℚ)
      + (-208 * (n : ℚ) ^ 3 + 2578 * (n : ℚ) ^ 2 - 4613 * (n : ℚ) - 2410) * (a (n - 1) : ℚ)
      + 9 * (-339 * (n : ℚ) - 638) * (a (n - 2) : ℚ)
      + 27 * ((n : ℚ) - 2) * (458 * (n : ℚ) ^ 2 - 289 * (n : ℚ) - 1146) * (a (n - 3) : ℚ)
      + 54 * ((n : ℚ) - 2) * ((n : ℚ) - 3) * (104 * (n : ℚ) - 1081) * (a (n - 4) : ℚ) = 0 := by
  obtain ⟨t, rfl | rfl | rfl⟩ : ∃ t, n = 3 * t + 5 ∨ n = 3 * t + 6 ∨ n = 3 * t + 7 :=
    ⟨(n - 5) / 3, by omega⟩
  · have e5 := q2 (t + 1) (3 * t + 4) (3 * t + 5) (by ring) (by ring)
    have e4 := q1 t (3 * t + 3) (3 * t + 4) rfl rfl
    have e3 := q0 t (3 * t + 2) (3 * t + 3) rfl rfl
    have e2 := q2 t (3 * t + 1) (3 * t + 2) rfl rfl
    simp only [show 3 * t + 5 - 1 = 3 * t + 4 by omega, show 3 * t + 5 - 2 = 3 * t + 3 by omega,
      show 3 * t + 5 - 3 = 3 * t + 2 by omega, show 3 * t + 5 - 4 = 3 * t + 1 by omega]
    rw [e5, e4, e3, e2]
    have h1 : (t : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (t : ℚ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · have e6 := q0 (t + 1) (3 * t + 5) (3 * t + 6) (by ring) (by ring)
    have e5 := q2 (t + 1) (3 * t + 4) (3 * t + 5) (by ring) (by ring)
    have e4 := q1 t (3 * t + 3) (3 * t + 4) rfl rfl
    have e3 := q0 t (3 * t + 2) (3 * t + 3) rfl rfl
    simp only [show 3 * t + 6 - 1 = 3 * t + 5 by omega, show 3 * t + 6 - 2 = 3 * t + 4 by omega,
      show 3 * t + 6 - 3 = 3 * t + 3 by omega, show 3 * t + 6 - 4 = 3 * t + 2 by omega]
    rw [e6, e5, e4, e3]
    have h1 : (t : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (t : ℚ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · have e7 := q1 (t + 1) (3 * t + 6) (3 * t + 7) (by ring) (by ring)
    have e6 := q0 (t + 1) (3 * t + 5) (3 * t + 6) (by ring) (by ring)
    have e5 := q2 (t + 1) (3 * t + 4) (3 * t + 5) (by ring) (by ring)
    have e4 := q1 t (3 * t + 3) (3 * t + 4) rfl rfl
    simp only [show 3 * t + 7 - 1 = 3 * t + 6 by omega, show 3 * t + 7 - 2 = 3 * t + 5 by omega,
      show 3 * t + 7 - 3 = 3 * t + 4 by omega, show 3 * t + 7 - 4 = 3 * t + 3 by omega]
    rw [e7, e6, e5, e4]
    have h1 : (t : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (t : ℚ) + 2 ≠ 0 := by positivity
    have h3 : (t : ℚ) + 3 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma rec2_q (n : ℕ) (hn : 7 ≤ n) :
    ((n : ℚ) + 2) * ((n : ℚ) + 1) * (a n : ℚ)
      + (5 * (n : ℚ) ^ 2 - 2) * (a (n - 1) : ℚ)
      + 3 * (5 * (n : ℚ) ^ 2 - 15 * (n : ℚ) + 3) * (a (n - 2) : ℚ)
      + 3 * ((n : ℚ) ^ 2 - 60 * (n : ℚ) + 81) * (a (n - 3) : ℚ)
      + 135 * (-(n : ℚ) ^ 2 + 3 * (n : ℚ) - 1) * (a (n - 4) : ℚ)
      - 405 * ((n : ℚ) - 2) * ((n : ℚ) - 4) * (a (n - 5) : ℚ)
      - 810 * ((n : ℚ) - 4) * ((n : ℚ) - 5) * (a (n - 6) : ℚ) = 0 := by
  obtain ⟨t, rfl | rfl | rfl⟩ : ∃ t, n = 3 * t + 7 ∨ n = 3 * t + 8 ∨ n = 3 * t + 9 :=
    ⟨(n - 7) / 3, by omega⟩
  · have e7 := q1 (t + 1) (3 * t + 6) (3 * t + 7) (by ring) (by ring)
    have e6 := q0 (t + 1) (3 * t + 5) (3 * t + 6) (by ring) (by ring)
    have e5 := q2 (t + 1) (3 * t + 4) (3 * t + 5) (by ring) (by ring)
    have e4 := q1 t (3 * t + 3) (3 * t + 4) rfl rfl
    have e3 := q0 t (3 * t + 2) (3 * t + 3) rfl rfl
    have e2 := q2 t (3 * t + 1) (3 * t + 2) rfl rfl
    simp only [show 3 * t + 7 - 1 = 3 * t + 6 by omega, show 3 * t + 7 - 2 = 3 * t + 5 by omega,
      show 3 * t + 7 - 3 = 3 * t + 4 by omega, show 3 * t + 7 - 4 = 3 * t + 3 by omega,
      show 3 * t + 7 - 5 = 3 * t + 2 by omega, show 3 * t + 7 - 6 = 3 * t + 1 by omega]
    rw [e7, e6, e5, e4, e3, e2]
    have h1 : (t : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (t : ℚ) + 2 ≠ 0 := by positivity
    have h3 : (t : ℚ) + 3 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · have e8 := q2 (t + 2) (3 * t + 7) (3 * t + 8) (by ring) (by ring)
    have e7 := q1 (t + 1) (3 * t + 6) (3 * t + 7) (by ring) (by ring)
    have e6 := q0 (t + 1) (3 * t + 5) (3 * t + 6) (by ring) (by ring)
    have e5 := q2 (t + 1) (3 * t + 4) (3 * t + 5) (by ring) (by ring)
    have e4 := q1 t (3 * t + 3) (3 * t + 4) rfl rfl
    have e3 := q0 t (3 * t + 2) (3 * t + 3) rfl rfl
    simp only [show 3 * t + 8 - 1 = 3 * t + 7 by omega, show 3 * t + 8 - 2 = 3 * t + 6 by omega,
      show 3 * t + 8 - 3 = 3 * t + 5 by omega, show 3 * t + 8 - 4 = 3 * t + 4 by omega,
      show 3 * t + 8 - 5 = 3 * t + 3 by omega, show 3 * t + 8 - 6 = 3 * t + 2 by omega]
    rw [e8, e7, e6, e5, e4, e3]
    have h1 : (t : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (t : ℚ) + 2 ≠ 0 := by positivity
    have h3 : (t : ℚ) + 3 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · have e9 := q0 (t + 2) (3 * t + 8) (3 * t + 9) (by ring) (by ring)
    have e8 := q2 (t + 2) (3 * t + 7) (3 * t + 8) (by ring) (by ring)
    have e7 := q1 (t + 1) (3 * t + 6) (3 * t + 7) (by ring) (by ring)
    have e6 := q0 (t + 1) (3 * t + 5) (3 * t + 6) (by ring) (by ring)
    have e5 := q2 (t + 1) (3 * t + 4) (3 * t + 5) (by ring) (by ring)
    have e4 := q1 t (3 * t + 3) (3 * t + 4) rfl rfl
    simp only [show 3 * t + 9 - 1 = 3 * t + 8 by omega, show 3 * t + 9 - 2 = 3 * t + 7 by omega,
      show 3 * t + 9 - 3 = 3 * t + 6 by omega, show 3 * t + 9 - 4 = 3 * t + 5 by omega,
      show 3 * t + 9 - 5 = 3 * t + 4 by omega, show 3 * t + 9 - 6 = 3 * t + 3 by omega]
    rw [e9, e8, e7, e6, e5, e4]
    have h1 : (t : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (t : ℚ) + 2 ≠ 0 := by positivity
    have h3 : (t : ℚ) + 3 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem main_proof :
    (∀ n : ℕ, a (3 * n + 2) = A208881 (n + 1) ∧ a (3 * n + 3) = A208881 (n + 1)) ∧
    (∀ n : ℕ, 5 ≤ n →
      -(458 * (n : ℤ) - 1205) * ((n : ℤ) + 2) * ((n : ℤ) + 1) * (a n : ℤ)
        + (-208 * (n : ℤ) ^ 3 + 2578 * (n : ℤ) ^ 2 - 4613 * (n : ℤ) - 2410) * (a (n - 1) : ℤ)
        + 9 * (-339 * (n : ℤ) - 638) * (a (n - 2) : ℤ)
        + 27 * ((n : ℤ) - 2) * (458 * (n : ℤ) ^ 2 - 289 * (n : ℤ) - 1146) * (a (n - 3) : ℤ)
        + 54 * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (104 * (n : ℤ) - 1081) * (a (n - 4) : ℤ) = 0) ∧
    (∀ n : ℕ, 7 ≤ n →
      ((n : ℤ) + 2) * ((n : ℤ) + 1) * (a n : ℤ)
        + (5 * (n : ℤ) ^ 2 - 2) * (a (n - 1) : ℤ)
        + 3 * (5 * (n : ℤ) ^ 2 - 15 * (n : ℤ) + 3) * (a (n - 2) : ℤ)
        + 3 * ((n : ℤ) ^ 2 - 60 * (n : ℤ) + 81) * (a (n - 3) : ℤ)
        + 135 * (-(n : ℤ) ^ 2 + 3 * (n : ℤ) - 1) * (a (n - 4) : ℤ)
        - 405 * ((n : ℤ) - 2) * ((n : ℤ) - 4) * (a (n - 5) : ℤ)
        - 810 * ((n : ℤ) - 4) * ((n : ℤ) - 5) * (a (n - 6) : ℤ) = 0) := by
  refine ⟨conj1, fun n hn => ?_, fun n hn => ?_⟩
  · have h := rec1_q n hn
    exact_mod_cast h
  · have h := rec2_q n hn
    exact_mod_cast h

end OMA.S_oeis_a199127

theorem OMA.solution : type_of% @OMA.S_oeis_a199127.main :=
  OMA.S_oeis_a199127.main_proof
