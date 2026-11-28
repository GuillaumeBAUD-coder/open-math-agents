import OMAStatements.S_oeis_a269876

namespace OMA.S_oeis_a269876

open PowerSeries




/-- Rule 43 on explicit neighbor values: an ON cell stays ON iff at most two neighbors are ON, an
OFF cell turns ON iff no neighbor is ON. -/
def r43 : Bool → Bool → Bool → Bool → Bool → Bool
  | true, b1, b2, b3, b4 =>
    !(b1 && b2 && b3) && !(b1 && b2 && b4) && !(b1 && b3 && b4) && !(b2 && b3 && b4)
  | false, b1, b2, b3, b4 => !b1 && !b2 && !b3 && !b4

lemma rule43 (s b1 b2 b3 b4 : Bool) :
    rule 43 s (b1.toNat + b2.toNat + b3.toNat + b4.toNat) = r43 s b1 b2 b3 b4 := by
  cases s <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

/-- Stage 2m: ON exactly on the even cells of [-m, m]^2. -/
def Ev (m : ℕ) (i j : ℤ) : Bool :=
  decide (-(m : ℤ) ≤ i ∧ i ≤ m ∧ -(m : ℤ) ≤ j ∧ j ≤ m ∧ (i + j) % 2 = 0)

/-- Stage 2m+1: OFF exactly on the odd cells of [-(m+1), m+1]^2. -/
def Od (m : ℕ) (i j : ℤ) : Bool :=
  !decide (-(m : ℤ) - 1 ≤ i ∧ i ≤ m + 1 ∧ -(m : ℤ) - 1 ≤ j ∧ j ≤ m + 1 ∧ (i + j) % 2 = 1)

/-- The box [-M, M]^2. -/
abbrev box (M i j : ℤ) : Prop := -M ≤ i ∧ i ≤ M ∧ -M ≤ j ∧ j ≤ M

lemma Ev_eq (m : ℕ) (i j : ℤ) : Ev m i j = decide (box m i j ∧ (i + j) % 2 = 0) := by
  simp only [Ev, box, and_assoc]

lemma Od_eq (m : ℕ) (i j : ℤ) : Od m i j = !decide (box ((m : ℤ) + 1) i j ∧ (i + j) % 2 = 1) := by
  simp only [Od, box, and_assoc, neg_add']

lemma step_even (m : ℕ) (i j : ℤ) :
    rule 43 (Ev m i j) ((Ev m (i - 1) j).toNat + (Ev m (i + 1) j).toNat + (Ev m i (j - 1)).toNat +
      (Ev m i (j + 1)).toNat) = Od m i j := by
  rw [rule43]
  symm
  cases h0 : Ev m i j <;> cases h1 : Ev m (i - 1) j <;> cases h2 : Ev m (i + 1) j <;>
    cases h3 : Ev m i (j - 1) <;> cases h4 : Ev m i (j + 1) <;>
    simp only [Ev, decide_eq_true_eq, decide_eq_false_iff_not] at h0 h1 h2 h3 h4 <;>
    simp only [r43, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.true_and,
      Bool.false_and, Bool.and_self] <;>
    simp only [Od, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq,
      decide_eq_false_iff_not] <;>
    omega

lemma step_odd (m : ℕ) (i j : ℤ) :
    rule 43 (Od m i j) ((Od m (i - 1) j).toNat + (Od m (i + 1) j).toNat + (Od m i (j - 1)).toNat +
      (Od m i (j + 1)).toNat) = Ev (m + 1) i j := by
  rw [rule43]
  symm
  cases h0 : Od m i j <;> cases h1 : Od m (i - 1) j <;> cases h2 : Od m (i + 1) j <;>
    cases h3 : Od m i (j - 1) <;> cases h4 : Od m i (j + 1) <;>
    simp only [Od, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq,
      decide_eq_false_iff_not] at h0 h1 h2 h3 h4 <;>
    simp only [r43, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.true_and,
      Bool.false_and, Bool.and_self] <;>
    simp only [Ev, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    push_cast <;>
    omega

/-- The explicit stage n. -/
def E (n : ℕ) : ℤ → ℤ → Bool := if n % 2 = 0 then Ev (n / 2) else Od (n / 2)

lemma pattern (n : ℕ) (i j : ℤ) : grid 43 n i j = E n i j := by
  induction n generalizing i j with
  | zero =>
    simp only [grid, E, Nat.zero_mod, Nat.zero_div, if_true, Ev, CharP.cast_eq_zero, neg_zero]
    by_cases h : i = 0 ∧ j = 0
    · rw [decide_eq_true h, decide_eq_true (by omega)]
    · rw [decide_eq_false h, decide_eq_false (by omega)]
  | succ n ih =>
    show rule 43 (grid 43 n i j) ((grid 43 n (i - 1) j).toNat + (grid 43 n (i + 1) j).toNat +
      (grid 43 n i (j - 1)).toNat + (grid 43 n i (j + 1)).toNat) = E (n + 1) i j
    rw [ih, ih, ih, ih, ih]
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have e1 : E (2 * m) = Ev m := by
        simp only [E, show 2 * m % 2 = 0 by omega, if_true, show 2 * m / 2 = m by omega]
      have e2 : E (2 * m + 1) = Od m := by
        simp only [E, show (2 * m + 1) % 2 = 1 by omega, show ¬ (1 = 0) from by omega, if_false,
          show (2 * m + 1) / 2 = m by omega]
      rw [e1, e2, step_even]
    · have e1 : E (2 * m + 1) = Od m := by
        simp only [E, show (2 * m + 1) % 2 = 1 by omega, show ¬ (1 = 0) from by omega, if_false,
          show (2 * m + 1) / 2 = m by omega]
      have e2 : E (2 * m + 1 + 1) = Ev (m + 1) := by
        simp only [E, show (2 * m + 1 + 1) % 2 = 0 by omega, if_true,
          show (2 * m + 1 + 1) / 2 = m + 1 by omega]
      rw [e1, e2, step_odd]

/-! Counting. -/

lemma row_even (x r : ℕ) :
    ((Finset.range (2 * r + 1)).filter (fun y => (x + y) % 2 = 0)).card =
      if x % 2 = 0 then r + 1 else r := by
  induction r with
  | zero =>
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [Finset.filter_singleton, h]
  | succ r ih =>
    rw [show 2 * (r + 1) + 1 = 2 * r + 1 + 1 + 1 by ring, Finset.range_add_one,
      Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · rw [if_pos (show (x + (2 * r + 1 + 1)) % 2 = 0 by omega),
        if_neg (show ¬ (x + (2 * r + 1)) % 2 = 0 by omega),
        Finset.card_insert_of_notMem (by simp), ih, if_pos h, if_pos h]
    · rw [if_neg (show ¬ (x + (2 * r + 1 + 1)) % 2 = 0 by omega),
        if_pos (show (x + (2 * r + 1)) % 2 = 0 by omega),
        Finset.card_insert_of_notMem (by simp), ih, if_neg (by omega), if_neg (by omega)]

lemma sq_even (r : ℕ) :
    ((Finset.range (2 * r + 1) ×ˢ Finset.range (2 * r + 1)).filter
      (fun p : ℕ × ℕ => (p.1 + p.2) % 2 = 0)).card = 2 * r ^ 2 + 2 * r + 1 := by
  rw [Finset.card_filter, Finset.sum_product]
  simp only [← Finset.card_filter]
  simp only [row_even]
  have hsplit : ∀ x : ℕ, (if x % 2 = 0 then r + 1 else r) = r + (if x % 2 = 0 then 1 else 0) := by
    intro x; split_ifs <;> ring
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [← Finset.card_filter]
  have h0 := row_even 0 r
  simp only [zero_add, Nat.zero_mod, if_true] at h0
  rw [h0]
  ring

lemma sq_odd (r : ℕ) :
    ((Finset.range (2 * r + 1) ×ˢ Finset.range (2 * r + 1)).filter
      (fun p : ℕ × ℕ => (p.1 + p.2) % 2 = 1)).card = 2 * r ^ 2 + 2 * r := by
  have htot := Finset.card_filter_add_card_filter_not
    (s := Finset.range (2 * r + 1) ×ˢ Finset.range (2 * r + 1)) (fun p : ℕ × ℕ => (p.1 + p.2) % 2 = 0)
  rw [sq_even, Finset.card_product, Finset.card_range] at htot
  have hc : (Finset.range (2 * r + 1) ×ˢ Finset.range (2 * r + 1)).filter
      (fun p : ℕ × ℕ => ¬ (p.1 + p.2) % 2 = 0) =
      (Finset.range (2 * r + 1) ×ˢ Finset.range (2 * r + 1)).filter
      (fun p : ℕ × ℕ => (p.1 + p.2) % 2 = 1) := by
    apply Finset.filter_congr; intro p _; omega
  rw [hc] at htot
  have : (2 * r + 1) * (2 * r + 1) = 2 * r ^ 2 + 2 * r + 1 + (2 * r ^ 2 + 2 * r) := by ring
  omega

/-- A shifted square of side 2r+1 inside [0, 2n]^2: cells (x + s, y + s). -/
lemma shift_card (n s r : ℕ) (hs : s + 2 * r ≤ 2 * n) (q : ℕ) (hq : q < 2)
    (P : ℕ × ℕ → Prop) [DecidablePred P]
    (hP : ∀ p : ℕ × ℕ, p.1 < 2 * n + 1 → p.2 < 2 * n + 1 →
      (P p ↔ (s ≤ p.1 ∧ p.1 ≤ s + 2 * r ∧ s ≤ p.2 ∧ p.2 ≤ s + 2 * r ∧ (p.1 + p.2) % 2 = q))) :
    ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter P).card =
      ((Finset.range (2 * r + 1) ×ˢ Finset.range (2 * r + 1)).filter
        (fun p : ℕ × ℕ => (p.1 + p.2) % 2 = q)).card := by
  apply Finset.card_nbij' (fun p : ℕ × ℕ => (p.1 - s, p.2 - s)) (fun p : ℕ × ℕ => (p.1 + s, p.2 + s))
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_range] at hp ⊢
    have := (hP p hp.1.1 hp.1.2).1 hp.2
    refine ⟨⟨by omega, by omega⟩, by omega⟩
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_range] at hp ⊢
    refine ⟨⟨by omega, by omega⟩, (hP _ (by omega) (by omega)).2 ⟨by omega, by omega, by omega,
      by omega, by omega⟩⟩
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_range] at hp
    have := (hP p hp.1.1 hp.1.2).1 hp.2
    simp only [Prod.ext_iff]; omega
  · intro p _
    simp only [Prod.ext_iff]; omega

lemma a_even (m : ℕ) : a (2 * m) = 2 * m ^ 2 + 2 * m + 1 := by
  rw [a, ← sq_even m]
  apply shift_card (2 * m) m m (by omega) 0 (by norm_num)
  intro p h1 h2
  rw [pattern, E, if_pos (by omega), show 2 * m / 2 = m by omega, Ev, decide_eq_true_eq]
  push_cast
  omega

lemma a_odd (m : ℕ) : a (2 * m + 1) = (4 * m + 3) ^ 2 - (2 * m ^ 2 + 6 * m + 4) := by
  have htot := Finset.card_filter_add_card_filter_not
    (s := Finset.range (2 * (2 * m + 1) + 1) ×ˢ Finset.range (2 * (2 * m + 1) + 1))
    (fun p : ℕ × ℕ => grid 43 (2 * m + 1) ((p.1 : ℤ) - ↑(2 * m + 1)) ((p.2 : ℤ) - ↑(2 * m + 1)) = true)
  rw [Finset.card_product, Finset.card_range] at htot
  have hoff : ((Finset.range (2 * (2 * m + 1) + 1) ×ˢ Finset.range (2 * (2 * m + 1) + 1)).filter
      (fun p : ℕ × ℕ => ¬ grid 43 (2 * m + 1) ((p.1 : ℤ) - ↑(2 * m + 1))
        ((p.2 : ℤ) - ↑(2 * m + 1)) = true)).card = 2 * m ^ 2 + 6 * m + 4 := by
    rw [show 2 * m ^ 2 + 6 * m + 4 = 2 * (m + 1) ^ 2 + 2 * (m + 1) by ring, ← sq_odd (m + 1)]
    apply shift_card (2 * m + 1) m (m + 1) (by omega) 1 (by norm_num)
    intro p h1 h2
    rw [pattern, E, if_neg (by omega), show (2 * m + 1) / 2 = m by omega, Od]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_not]
    push_cast
    omega
  rw [a]
  have : (2 * (2 * m + 1) + 1) * (2 * (2 * m + 1) + 1) = (4 * m + 3) ^ 2 := by ring
  omega

/-- Barker's closed forms (every n). -/
theorem closed (n : ℕ) :
    (a n : ℤ) = (1 + 3 * (-1) ^ n - 2 * (-3 + (-1) ^ n) * n + (8 - 6 * (-1) ^ n) * n ^ 2) / 4 ∧
      (n % 2 = 0 → (a n : ℤ) = (n ^ 2 + 2 * n + 2) / 2) ∧
      (n % 2 = 1 → (a n : ℤ) = (7 * n ^ 2 + 4 * n - 1) / 2) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [a_even, (even_two_mul m).neg_one_pow]
    refine ⟨?_, fun _ => ?_, fun h => absurd h (by omega)⟩
    · push_cast; ring_nf; omega
    · push_cast; ring_nf; omega
  · rw [a_odd, (odd_two_mul_add_one m).neg_one_pow]
    have hle : 2 * m ^ 2 + 6 * m + 4 ≤ (4 * m + 3) ^ 2 := by nlinarith
    refine ⟨?_, fun h => absurd h (by omega), fun _ => ?_⟩
    · push_cast [hle]; ring_nf; omega
    · push_cast [hle]; ring_nf; omega

lemma closed_int (n : ℕ) :
    2 * (a n : ℤ) = if n % 2 = 0 then (n : ℤ) ^ 2 + 2 * n + 2 else 7 * (n : ℤ) ^ 2 + 4 * n - 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [if_pos (by omega), a_even]; push_cast; ring
  · rw [if_neg (by omega), a_odd]
    have hle : 2 * m ^ 2 + 6 * m + 4 ≤ (4 * m + 3) ^ 2 := by nlinarith
    push_cast [hle]; ring

/-- Barker's recurrence a(n) = 3a(n-2) - 3a(n-4) + a(n-6), n > 5. -/
theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  rw [show k + 6 - 2 = k + 4 by omega, show k + 6 - 4 = k + 2 by omega, show k + 6 - 6 = k by omega]
  have e0 := closed_int (k + 6)
  have e1 := closed_int (k + 4)
  have e2 := closed_int (k + 2)
  have e3 := closed_int k
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [if_pos (by omega)] at e0 e1 e2 e3
    push_cast at e0 e1 e2 e3
    have : 2 * (a (k + 6) : ℤ) = 2 * (3 * a (k + 4) - 3 * a (k + 2) + a k) := by
      linear_combination e0 - 3 * e1 + 3 * e2 - e3
    exact Int.eq_of_mul_eq_mul_left (by norm_num) this
  · rw [if_neg (by omega)] at e0 e1 e2 e3
    push_cast at e0 e1 e2 e3
    have : 2 * (a (k + 6) : ℤ) = 2 * (3 * a (k + 4) - 3 * a (k + 2) + a k) := by
      linear_combination e0 - 3 * e1 + 3 * e2 - e3
    exact Int.eq_of_mul_eq_mul_left (by norm_num) this

/-- Barker's generating function, as an identity of formal power series. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 3) =
    1 + 5 * X + 2 * X ^ 2 + 22 * X ^ 3 + X ^ 4 + X ^ 5 := by
  have hD : ((1 - X) ^ 3 * (1 + X) ^ 3 : ℤ⟦X⟧) =
      C 1 * X ^ 0 - C 3 * X ^ 2 + C 3 * X ^ 4 - C 1 * X ^ 6 := by
    simp only [map_one, map_ofNat, pow_zero, mul_one, one_mul]; ring
  have hN : (1 + 5 * X + 2 * X ^ 2 + 22 * X ^ 3 + X ^ 4 + X ^ 5 : ℤ⟦X⟧) =
      C 1 * X ^ 0 + C 5 * X ^ 1 + C 2 * X ^ 2 + C 22 * X ^ 3 + C 1 * X ^ 4 + C 1 * X ^ 5 := by
    simp only [map_one, map_ofNat, pow_zero, pow_one, mul_one, one_mul]
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [mul_sub, mul_add, ← mul_assoc, map_sub, map_add, coeff_mul_X_pow', coeff_mul_C,
    coeff_mk]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · have v0 : a 0 = 1 := by rw [show (0 : ℕ) = 2 * 0 by rfl, a_even]; norm_num
    have v1 : a 1 = 5 := by rw [show (1 : ℕ) = 2 * 0 + 1 by rfl, a_odd]; norm_num
    have v2 : a 2 = 5 := by rw [show (2 : ℕ) = 2 * 1 by rfl, a_even]; norm_num
    have v3 : a 3 = 37 := by rw [show (3 : ℕ) = 2 * 1 + 1 by rfl, a_odd]; norm_num
    have v4 : a 4 = 13 := by rw [show (4 : ℕ) = 2 * 2 by rfl, a_even]; norm_num
    have v5 : a 5 = 97 := by rw [show (5 : ℕ) = 2 * 2 + 1 by rfl, a_odd]; norm_num
    interval_cases n <;> simp [v0, v1, v2, v3, v4, v5]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    have := recurrence (k + 6) (by omega)
    rw [show k + 6 - 2 = k + 4 by omega, show k + 6 - 4 = k + 2 by omega,
      show k + 6 - 6 = k by omega] at this
    rw [if_pos (show 0 ≤ k + 6 by omega), if_pos (show 2 ≤ k + 6 by omega),
      if_pos (show 4 ≤ k + 6 by omega), if_pos (show 6 ≤ k + 6 by omega),
      show k + 6 - 0 = k + 6 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 4 = k + 2 by omega, show k + 6 - 6 = k by omega]
    rw [if_neg (show ¬ (k + 6 = 0) by omega), if_neg (show ¬ (k + 6 = 1) by omega),
      if_neg (show ¬ (k + 6 = 2) by omega), if_neg (show ¬ (k + 6 = 3) by omega),
      if_neg (show ¬ (k + 6 = 4) by omega), if_neg (show ¬ (k + 6 = 5) by omega)]
    linarith

end OMA.S_oeis_a269876

theorem OMA.solution : type_of% @OMA.S_oeis_a269876.main :=
  ⟨fun n => (OMA.S_oeis_a269876.closed n).1, fun n => (OMA.S_oeis_a269876.closed n).2.1,
    fun n => (OMA.S_oeis_a269876.closed n).2.2, OMA.S_oeis_a269876.recurrence,
    OMA.S_oeis_a269876.gf⟩
