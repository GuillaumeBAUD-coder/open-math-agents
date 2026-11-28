import OMAStatements.S_oeis_a212838

namespace OMA.S_oeis_a212838

open PowerSeries Finset


instance (n : ℕ) : DecidableRel (zn n) := fun x y => by unfold zn; infer_instance


/-! ## Arrays by their first entry -/

/-- No two consecutive positions hold 0 and n. -/
def Valid {n L : ℕ} (f : Fin L → Fin (n + 1)) : Prop :=
  ∀ i j : Fin L, j.val = i.val + 1 → ¬ zn n (f i) (f j)

instance {n L : ℕ} : DecidablePred (@Valid n L) := fun f => by unfold Valid; infer_instance

/-- S(L, v): valid arrays of length L + 1 whose first entry is v. -/
def S (n L : ℕ) (v : Fin (n + 1)) : ℕ :=
  ((univ : Finset (Fin (L + 1) → Fin (n + 1))).filter (fun f => Valid f ∧ f 0 = v)).card

lemma valid_cons {n L : ℕ} (x : Fin (n + 1)) (g : Fin (L + 1) → Fin (n + 1)) :
    Valid (Fin.cons x g : Fin (L + 2) → Fin (n + 1)) ↔ ¬ zn n x (g 0) ∧ Valid g := by
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

lemma S_zero (n : ℕ) (v : Fin (n + 1)) : S n 0 v = 1 := by
  unfold S
  rw [Finset.card_eq_one]
  refine ⟨fun _ => v, ?_⟩
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

/-- Prepending v to an array of length L + 1. -/
def consEmb (n L : ℕ) (v : Fin (n + 1)) :
    (Fin (L + 1) → Fin (n + 1)) ↪ (Fin (L + 2) → Fin (n + 1)) where
  toFun g := Fin.cons v g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n L : ℕ) (v : Fin (n + 1)) (g : Fin (L + 1) → Fin (n + 1)) :
    consEmb n L v g = Fin.cons v g := rfl

lemma S_succ (n L : ℕ) (v : Fin (n + 1)) :
    S n (L + 1) v = ∑ u : Fin (n + 1), if ¬ zn n v u then S n L u else 0 := by
  have e : ((univ : Finset (Fin (L + 2) → Fin (n + 1))).filter (fun f => Valid f ∧ f 0 = v)) =
      (((univ : Finset (Fin (L + 1) → Fin (n + 1))).filter
        (fun g => ¬ zn n v (g 0) ∧ Valid g)).map (consEmb n L v)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons v (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        exact hv
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(valid_cons v g).2 hg, by simp⟩
  unfold S
  rw [e, Finset.card_map]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  by_cases hvu : ¬ zn n v u
  · rw [if_pos hvu]
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hg⟩, h0⟩
      exact ⟨hg, h0⟩
    · rintro ⟨hg, h0⟩
      exact ⟨⟨h0 ▸ hvu, hg⟩, h0⟩
  · rw [if_neg hvu, Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hz, _⟩, h0⟩
    exact hvu (h0 ▸ hz)

/-! ## Three classes of values -/

/-- P(L) and Q(L): the counts S(L, v) for v in {0, n} and for a middle value v. -/
def PQ (n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | L + 1 => ((PQ n L).1 + (n - 1) * (PQ n L).2, 2 * (PQ n L).1 + (n - 1) * (PQ n L).2)

/-- A function of the value class sums to A + B + (n - 1) C. -/
lemma sum_cls (n : ℕ) (hn : 1 ≤ n) (A B C : ℕ) :
    (∑ u : Fin (n + 1), if u.val = 0 then A else if u.val = n then B else C) =
      A + B + (n - 1) * C := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, if_true, Fin.val_succ, Fin.coe_castSucc, Fin.val_last,
    Nat.add_sub_cancel]
  have h1 : ∀ i : Fin m, ¬ ((i : ℕ) + 1 = 0) := fun i => by omega
  have h2 : ∀ i : Fin m, ¬ ((i : ℕ) + 1 = m + 1) := fun i => by have := i.isLt; omega
  simp only [h1, h2, if_false, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, show ¬ (m + 1 = 0) by omega, if_true]
  ring

lemma S_cls (n : ℕ) (hn : 1 ≤ n) (L : ℕ) (v : Fin (n + 1)) :
    S n L v = if v.val = 0 ∨ v.val = n then (PQ n L).1 else (PQ n L).2 := by
  induction L generalizing v with
  | zero => simp [S_zero, PQ]
  | succ L ih =>
    rw [S_succ]
    simp only [ih]
    by_cases h0 : v.val = 0
    · have e : ∀ u : Fin (n + 1), (if ¬ zn n v u then
          (if u.val = 0 ∨ u.val = n then (PQ n L).1 else (PQ n L).2) else 0) =
          (if u.val = 0 then (PQ n L).1 else if u.val = n then 0 else (PQ n L).2) := by
        intro u
        have hn0 : n ≠ 0 := by omega
        by_cases hu0 : u.val = 0
        · simp [zn, h0, hu0, hn0, Ne.symm hn0]
        · by_cases hun : u.val = n
          · simp [zn, h0, hun, hn0]
          · simp [zn, h0, hu0, hun]
      rw [Finset.sum_congr rfl (fun u _ => e u), sum_cls n hn]
      simp [h0, PQ]
    · by_cases hvn : v.val = n
      · have e : ∀ u : Fin (n + 1), (if ¬ zn n v u then
            (if u.val = 0 ∨ u.val = n then (PQ n L).1 else (PQ n L).2) else 0) =
            (if u.val = 0 then 0 else if u.val = n then (PQ n L).1 else (PQ n L).2) := by
          intro u
          by_cases hu0 : u.val = 0
          · simp [zn, hvn, hu0]
          · by_cases hun : u.val = n
            · simp [zn, hvn, hu0, hun]
            · simp [zn, hvn, hu0, hun]
        rw [Finset.sum_congr rfl (fun u _ => e u), sum_cls n hn]
        simp [hvn, PQ]
      · have e : ∀ u : Fin (n + 1), (if ¬ zn n v u then
            (if u.val = 0 ∨ u.val = n then (PQ n L).1 else (PQ n L).2) else 0) =
            (if u.val = 0 then (PQ n L).1 else if u.val = n then (PQ n L).1 else (PQ n L).2) := by
          intro u
          by_cases hu0 : u.val = 0
          · simp [zn, h0, hvn, hu0]
          · by_cases hun : u.val = n
            · simp [zn, h0, hvn, hu0, hun]
            · simp [zn, h0, hvn, hu0, hun]
        rw [Finset.sum_congr rfl (fun u _ => e u), sum_cls n hn]
        simp only [h0, hvn, or_self, if_false, PQ]
        ring

lemma count (n : ℕ) (hn : 1 ≤ n) (L : ℕ) :
    ((univ : Finset (Fin (L + 1) → Fin (n + 1))).filter Valid).card =
      2 * (PQ n L).1 + (n - 1) * (PQ n L).2 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  have e : ∀ v : Fin (n + 1),
      (((univ : Finset (Fin (L + 1) → Fin (n + 1))).filter Valid).filter (fun g => g 0 = v)).card
        = if v.val = 0 then (PQ n L).1 else if v.val = n then (PQ n L).1 else (PQ n L).2 := by
    intro v
    rw [Finset.filter_filter]
    rw [show ((univ : Finset (Fin (L + 1) → Fin (n + 1))).filter (fun g => Valid g ∧ g 0 = v)).card
      = S n L v from rfl, S_cls n hn]
    by_cases h0 : v.val = 0
    · simp [h0]
    · by_cases hvn : v.val = n
      · simp [h0, hvn]
      · simp [h0, hvn]
  rw [Finset.sum_congr rfl (fun v _ => e v), sum_cls n hn]
  ring

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : a n = 2 * (PQ n 4).1 + (n - 1) * (PQ n 4).2 :=
  count n hn 4

/-- a(m + 1) as a polynomial in m. -/
lemma a_poly (m : ℕ) : (a (m + 1) : ℤ) =
    2 + 16 * (m : ℤ) + 38 * (m : ℤ) ^ 2 + 32 * (m : ℤ) ^ 3 + 10 * (m : ℤ) ^ 4 + (m : ℤ) ^ 5 := by
  rw [a_eq (m + 1) (by omega)]
  simp only [PQ, Nat.add_sub_cancel]
  push_cast
  ring

/-! ## Barker's conjectures -/

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x*(2 + 87*x + 70*x^2 - 50*x^3 + 12*x^4 - x^5) / (1 - x)^6. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
    X * (2 + 87 * X + 70 * X ^ 2 - 50 * X ^ 3 + 12 * X ^ 4 - X ^ 5) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hq : ∀ m : ℕ, ((a (m + 1) : ℕ) : ℚ) =
      2 + 16 * (m : ℚ) + 38 * (m : ℚ) ^ 2 + 32 * (m : ℚ) ^ 3 + 10 * (m : ℚ) ^ 4 + (m : ℚ) ^ 5 := by
    intro m
    have h := a_poly m
    exact_mod_cast h
  have e1 : A * (1 - X) ^ 6 = A - A * X ^ 1 * C 6 + A * X ^ 2 * C 15 - A * X ^ 3 * C 20 + A * X ^ 4 * C 15 - A * X ^ 5 * C 6 + A * X ^ 6 := by
    rw [show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6,
      show (C (15 : ℚ) : ℚ⟦X⟧) = 15 from map_ofNat C 15,
      show (C (20 : ℚ) : ℚ⟦X⟧) = 20 from map_ofNat C 20]
    ring
  have e2 : (X : ℚ⟦X⟧) * (2 + 87 * X + 70 * X ^ 2 - 50 * X ^ 3 + 12 * X ^ 4 - X ^ 5) =
      X ^ 1 * C 2 + X ^ 2 * C 87 + X ^ 3 * C 70 - X ^ 4 * C 50 + X ^ 5 * C 12 - X ^ 6 * C 1 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C,
      show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2,
      show (C (12 : ℚ) : ℚ⟦X⟧) = 12 from map_ofNat C 12,
      show (C (50 : ℚ) : ℚ⟦X⟧) = 50 from map_ofNat C 50,
      show (C (70 : ℚ) : ℚ⟦X⟧) = 70 from map_ofNat C 70,
      show (C (87 : ℚ) : ℚ⟦X⟧) = 87 from map_ofNat C 87]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | m
  · simp
  · simp [hq 0] <;> norm_num
  · simp [hq 0, hq 1] <;> norm_num
  · simp [hq 0, hq 1, hq 2] <;> norm_num
  · simp [hq 0, hq 1, hq 2, hq 3] <;> norm_num
  · simp [hq 0, hq 1, hq 2, hq 3, hq 4] <;> norm_num
  · simp [hq 0, hq 1, hq 2, hq 3, hq 4, hq 5] <;> norm_num
  · simp only [show ¬ (m + 7 = 0) by omega,
      show 1 ≤ m + 7 by omega,
      show 2 ≤ m + 7 by omega,
      show 3 ≤ m + 7 by omega,
      show 4 ≤ m + 7 by omega,
      show 5 ≤ m + 7 by omega,
      show 6 ≤ m + 7 by omega,
      if_true,
      if_false,
      show m + 7 - 1 = (m + 5) + 1 by omega,
      show m + 7 - 2 = (m + 4) + 1 by omega,
      show m + 7 - 3 = (m + 3) + 1 by omega,
      show m + 7 - 4 = (m + 2) + 1 by omega,
      show m + 7 - 5 = (m + 1) + 1 by omega,
      show m + 7 - 6 = m + 1 by omega,
      show ¬ (m + 7 = 1) by omega,
      show ¬ (m + 7 = 2) by omega,
      show ¬ (m + 7 = 3) by omega,
      show ¬ (m + 7 = 4) by omega,
      show ¬ (m + 7 = 5) by omega,
      show ¬ (m + 7 = 6) by omega,
      show ¬ ((m + 5) + 1 = 0) by omega,
      show ¬ ((m + 4) + 1 = 0) by omega,
      show ¬ ((m + 3) + 1 = 0) by omega,
      show ¬ ((m + 2) + 1 = 0) by omega,
      show ¬ ((m + 1) + 1 = 0) by omega,
      show ¬ (m + 1 = 0) by omega,
      show m + 7 = (m + 6) + 1 by omega]
    rw [hq (m + 6), hq (m + 5), hq (m + 4), hq (m + 3), hq (m + 2), hq (m + 1), hq m]
    push_cast
    ring

/-- Barker's recurrence, for n > 6. -/
theorem recurrence : ∀ n : ℕ, 6 < n → (a n : ℤ) =
    6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = (m + 5) + 1 by omega,
    show m + 7 - 2 = (m + 4) + 1 by omega,
    show m + 7 - 3 = (m + 3) + 1 by omega,
    show m + 7 - 4 = (m + 2) + 1 by omega,
    show m + 7 - 5 = (m + 1) + 1 by omega,
    show m + 7 - 6 = m + 1 by omega,
    show m + 7 = (m + 6) + 1 by omega]
  rw [a_poly (m + 6), a_poly (m + 5), a_poly (m + 4), a_poly (m + 3), a_poly (m + 2), a_poly (m + 1), a_poly m]
  push_cast
  ring

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (2 + 87 * X + 70 * X ^ 2 - 50 * X ^ 3 + 12 * X ^ 4 - X ^ 5) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) =
      6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) :=
  ⟨gf, recurrence⟩

/-- Controls: the entry's terms a(1..10) from the polynomial, and a(1), a(2) by enumeration. -/
theorem controls : a 1 = 2 ∧ a 2 = 99 ∧ a 3 = 634 ∧ a 4 = 2309 ∧ a 5 = 6306 ∧ a 6 = 14407 ∧ a 7 = 29114 ∧ a 8 = 53769 ∧ a 9 = 92674 ∧ a 10 = 151211 := by
  have h : ∀ m : ℕ, a (m + 1) = 2 + 16 * m + 38 * m ^ 2 + 32 * m ^ 3 + 10 * m ^ 4 + m ^ 5 := by
    intro m
    have := a_poly m
    exact_mod_cast this
  exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9⟩

theorem controls_direct : a 1 = 2 ∧ a 2 = 99 := by
  unfold a
  constructor <;> decide +kernel

end OMA.S_oeis_a212838

theorem OMA.solution : type_of% @OMA.S_oeis_a212838.main :=
  OMA.S_oeis_a212838.conjecture
