import OMAStatements.S_oeis_a239171

namespace OMA.S_oeis_a239171

open PowerSeries Finset




instance {m : ℕ} : DecidableRel (@vnb m) := fun i i' => by unfold vnb; infer_instance


instance {m : ℕ} : DecidablePred (@good m) := fun x => by unfold good; infer_instance


/-! ## Rows are constant -/

/-- Element i of the column c is equal to all its vertical neighbors. -/
def bad {m : ℕ} (c : Fin m → Fin 3) (i : Fin m) : Prop := ∀ i', vnb i i' → c i' = c i

instance {m : ℕ} (c : Fin m → Fin 3) : DecidablePred (bad c) := fun i => by
  unfold bad; infer_instance

/-- No element of the column is equal to all its vertical neighbors. -/
def colGood {m : ℕ} (c : Fin m → Fin 3) : Prop := ∀ i, ¬ bad c i

instance {m : ℕ} : DecidablePred (@colGood m) := fun c => by unfold colGood; infer_instance

lemma row_iff : ∀ v : Fin 2 → Fin 3, (∀ j, ¬ (∀ j', hnb j j' → v j' < v j)) ↔ v 0 = v 1 := by
  decide

lemma good_iff {m : ℕ} (x : Fin m → Fin 2 → Fin 3) :
    good x ↔ (∀ i, x i 0 = x i 1) ∧ colGood (fun i => x i 0) := by
  unfold good colGood bad
  constructor
  · intro h
    have hr : ∀ i, x i 0 = x i 1 := fun i => (row_iff (x i)).1 (fun j => (h i j).1)
    exact ⟨hr, fun i => (h i 0).2⟩
  · rintro ⟨hr, hc⟩ i j
    refine ⟨(row_iff (x i)).2 (hr i) j, ?_⟩
    have hj : ∀ k, x k j = x k 0 := by
      intro k
      fin_cases j
      · rfl
      · exact (hr k).symm
    simp only [hj]
    exact hc i

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin (n + 1) → Fin 3)).filter colGood).card := by
  unfold a
  refine Finset.card_bij' (fun x _ => fun i => x i 0) (fun c _ => fun i _ => c i) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ((good_iff x).1 hx).2
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact (good_iff _).2 ⟨fun _ => rfl, hc⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hr := ((good_iff x).1 hx).1
    funext i j
    fin_cases j
    · rfl
    · exact hr i
  · intro c _
    rfl

/-! ## Prepending an element to a column -/

/-- All elements but the first are not equal to all their vertical neighbors. -/
def Tail {m : ℕ} (c : Fin m → Fin 3) : Prop := ∀ i : Fin m, i.val ≠ 0 → ¬ bad c i

instance {m : ℕ} : DecidablePred (@Tail m) := fun c => by unfold Tail; infer_instance

lemma bad_cons_zero {k : ℕ} (p : Fin 3) (c : Fin (k + 2) → Fin 3) :
    bad (Fin.cons p c : Fin (k + 3) → Fin 3) 0 ↔ c 0 = p := by
  unfold bad
  constructor
  · intro h
    have := h (Fin.succ 0) (by simp [vnb])
    simpa using this
  · intro h i' hi'
    induction i' using Fin.cases with
    | zero => simp [vnb] at hi'
    | succ j =>
      have hj : j = 0 := by
        apply Fin.ext
        simp [vnb] at hi'
        omega
      subst hj
      simpa using h

lemma bad_cons_one {k : ℕ} (p : Fin 3) (c : Fin (k + 2) → Fin 3) :
    bad (Fin.cons p c : Fin (k + 3) → Fin 3) (Fin.succ 0) ↔ p = c 0 ∧ c 1 = c 0 := by
  unfold bad
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 (by simp [vnb])
      simpa using this
    · have hv : vnb (Fin.succ (0 : Fin (k + 2))) (Fin.succ (1 : Fin (k + 2))) := by
        unfold vnb
        left
        rw [Fin.val_succ, Fin.val_succ, Fin.val_zero, Fin.val_one]
      have := h (Fin.succ 1) hv
      simp only [Fin.cons_succ] at this
      exact this
  · rintro ⟨h1, h2⟩ i' hi'
    induction i' using Fin.cases with
    | zero => simpa using h1
    | succ j =>
      have hj : j = 1 := by
        apply Fin.ext
        simp only [vnb, Fin.val_succ, Fin.val_zero] at hi'
        rw [Fin.val_one]
        omega
      subst hj
      simp only [Fin.cons_succ]
      exact h2

lemma bad_cons_succ {k : ℕ} (p : Fin 3) (c : Fin (k + 2) → Fin 3) (i : Fin (k + 2))
    (hi : i.val ≠ 0) : bad (Fin.cons p c : Fin (k + 3) → Fin 3) i.succ ↔ bad c i := by
  unfold bad
  constructor
  · intro h i' hi'
    have := h i'.succ (by simp only [vnb, Fin.val_succ] at hi' ⊢; omega)
    simpa using this
  · intro h i' hi'
    induction i' using Fin.cases with
    | zero =>
      exfalso
      simp only [vnb, Fin.val_succ, Fin.val_zero] at hi'
      omega
    | succ j =>
      have := h j (by simp only [vnb, Fin.val_succ] at hi' ⊢; omega)
      simpa using this

lemma tail_cons {k : ℕ} (p : Fin 3) (c : Fin (k + 2) → Fin 3) :
    Tail (Fin.cons p c : Fin (k + 3) → Fin 3) ↔ ¬ (p = c 0 ∧ c 1 = c 0) ∧ Tail c := by
  unfold Tail
  constructor
  · intro h
    refine ⟨fun hb => h (Fin.succ 0) (by simp) ((bad_cons_one p c).2 hb), ?_⟩
    intro j hj hb
    exact h j.succ (by simp) ((bad_cons_succ p c j hj).2 hb)
  · rintro ⟨h1, h2⟩ i hi
    induction i using Fin.cases with
    | zero => exact absurd rfl hi
    | succ j =>
      by_cases hj : j.val = 0
      · have : j = 0 := Fin.ext hj
        subst this
        exact fun hb => h1 ((bad_cons_one p c).1 hb)
      · exact fun hb => h2 j hj ((bad_cons_succ p c j hj).1 hb)

lemma colGood_cons {k : ℕ} (p : Fin 3) (c : Fin (k + 2) → Fin 3) :
    colGood (Fin.cons p c : Fin (k + 3) → Fin 3) ↔ ¬ (c 0 = p) ∧ Tail c := by
  have e : colGood (Fin.cons p c : Fin (k + 3) → Fin 3) ↔
      ¬ bad (Fin.cons p c : Fin (k + 3) → Fin 3) 0 ∧ Tail (Fin.cons p c : Fin (k + 3) → Fin 3) := by
    unfold colGood Tail
    constructor
    · intro h
      exact ⟨h 0, fun i _ => h i⟩
    · rintro ⟨h0, h⟩ i
      by_cases hi : i.val = 0
      · have : i = 0 := Fin.ext hi
        subst this
        exact h0
      · exact h i hi
  rw [e, bad_cons_zero, tail_cons]
  constructor
  · rintro ⟨h0, _, h⟩
    exact ⟨h0, h⟩
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun hb => h0 hb.1.symm, h⟩

/-! ## Counting columns by their first two elements -/

/-- T(k, q, r): columns of length k + 2 starting with q, r whose elements other than the first are
good. -/
def T (k : ℕ) (q r : Fin 3) : ℕ :=
  ((univ : Finset (Fin (k + 2) → Fin 3)).filter (fun c => c 0 = q ∧ c 1 = r ∧ Tail c)).card

/-- Prepending p to a column of length k + 2. -/
def consEmb (k : ℕ) (p : Fin 3) : (Fin (k + 2) → Fin 3) ↪ (Fin (k + 3) → Fin 3) where
  toFun c := Fin.cons p c
  inj' c c' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (k : ℕ) (p : Fin 3) (c : Fin (k + 2) → Fin 3) :
    consEmb k p c = Fin.cons p c := rfl

lemma T_succ (k : ℕ) (p q : Fin 3) :
    T (k + 1) p q = ∑ r : Fin 3, if ¬ (p = q ∧ r = q) then T k q r else 0 := by
  have e : ((univ : Finset (Fin (k + 3) → Fin 3)).filter
      (fun c => c 0 = p ∧ c 1 = q ∧ Tail c)) =
      (((univ : Finset (Fin (k + 2) → Fin 3)).filter
        (fun c => c 0 = q ∧ ¬ (p = q ∧ c 1 = q) ∧ Tail c)).map (consEmb k p)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨h0, h1, ht⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons p (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, tail_cons] at ht
        have h1' : Fin.tail f 0 = q := by simpa [Fin.tail] using h1
        refine ⟨h1', ?_, ht.2⟩
        rintro ⟨hpq, hq⟩
        exact ht.1 ⟨hpq.trans h1'.symm, hq.trans h1'.symm⟩
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, ⟨hg0, hg1, hgt⟩, rfl⟩
      refine ⟨by simp, by simpa using hg0, (tail_cons p g).2 ⟨?_, hgt⟩⟩
      rintro ⟨hp, h1⟩
      exact hg1 ⟨hp.trans hg0, h1.trans hg0⟩
  unfold T
  rw [e, Finset.card_map]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 1) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases hr : ¬ (p = q ∧ r = q)
  · rw [if_pos hr]
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h0, _, ht⟩, h1⟩
      exact ⟨h0, h1, ht⟩
    · rintro ⟨h0, h1, ht⟩
      exact ⟨⟨h0, by rw [h1]; exact hr, ht⟩, h1⟩
  · rw [if_neg hr, Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨_, h, _⟩, h1⟩
    exact hr (h1 ▸ h)

lemma T_zero : ∀ q r : Fin 3, T 0 q r = if q ≠ r then 1 else 0 := by
  decide +kernel

/-- Columns of length k + 3 with all elements good, by their first element. -/
lemma G_eq (k : ℕ) : ((univ : Finset (Fin (k + 3) → Fin 3)).filter colGood).card =
    ∑ p : Fin 3, ∑ q : Fin 3, ∑ r : Fin 3, if q ≠ p then T k q r else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have e : ((univ : Finset (Fin (k + 3) → Fin 3)).filter colGood).filter (fun g => g 0 = p) =
      (((univ : Finset (Fin (k + 2) → Fin 3)).filter (fun c => ¬ (c 0 = p) ∧ Tail c)).map
        (consEmb k p)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hg, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons p (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, colGood_cons] at hg
        exact hg
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(colGood_cons p g).2 hg, by simp⟩
  rw [e, Finset.card_map]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 1) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases hqp : q ≠ p
  · rw [if_pos hqp]
    unfold T
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨_, ht⟩, h0⟩, h1⟩
      exact ⟨h0, h1, ht⟩
    · rintro ⟨h0, h1, ht⟩
      exact ⟨⟨⟨by rw [h0]; exact hqp, ht⟩, h0⟩, h1⟩
  · rw [if_neg hqp, Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨⟨h, _⟩, h0⟩, _⟩
    exact hqp (fun hq => h (h0.trans hq))

/-! ## The recurrence -/

lemma T_one : ∀ q r : Fin 3, T 1 q r =
    ∑ s : Fin 3, if ¬ (q = r ∧ s = r) then (if r ≠ s then 1 else 0) else 0 := by
  intro q r
  rw [T_succ]
  simp only [T_zero]

lemma T_base : ∀ q r : Fin 3, T 2 q r = 2 * (T 1 q r + T 0 q r) := by
  intro q r
  rw [T_succ 1]
  simp only [T_one, T_zero]
  revert q r
  decide +kernel

lemma T_rec (k : ℕ) (q r : Fin 3) : T (k + 2) q r = 2 * (T (k + 1) q r + T k q r) := by
  induction k generalizing q r with
  | zero => exact T_base q r
  | succ k ih =>
    rw [T_succ (k + 2), T_succ (k + 1), T_succ k, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hc : ¬ (q = r ∧ s = r)
    · simp only [if_pos hc]
      exact ih r s
    · simp only [if_neg hc]
      rfl

lemma a_rec (k : ℕ) : a (k + 4) = 2 * (a (k + 3) + a (k + 2)) := by
  rw [a_eq, a_eq, a_eq, show k + 4 + 1 = (k + 2) + 3 from rfl, show k + 3 + 1 = (k + 1) + 3 from rfl,
    show k + 2 + 1 = k + 3 from rfl, G_eq, G_eq, G_eq]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases hc : q ≠ p
  · simp only [if_pos hc]
    exact T_rec k q r
  · simp only [if_neg hc]
    rfl

lemma a_one : a 1 = 6 := by
  rw [a_eq]
  decide +kernel

lemma a_two : a 2 = 12 := by
  rw [a_eq, show (2 + 1) = 0 + 3 from rfl, G_eq]
  simp only [T_zero]
  decide +kernel

lemma a_three : a 3 = 36 := by
  rw [a_eq, show (3 + 1) = 1 + 3 from rfl, G_eq]
  simp only [T_one]
  decide +kernel

lemma a_rec' (n : ℕ) : a (n + 3) = 2 * a (n + 2) + 2 * a (n + 1) := by
  rcases n with _ | k
  · simp only [Nat.zero_add]
    calc a 3 = 36 := a_three
      _ = 2 * 12 + 2 * 6 := by norm_num
      _ = 2 * a 2 + 2 * a 1 := by rw [← a_two, ← a_one]
  · rw [show k + 1 + 3 = k + 4 from rfl, a_rec]
    ring

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 6x/(1 - 2x - 2x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 2 * X - 2 * X ^ 2) = 6 * X := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 2 * X - 2 * X ^ 2) = A - A * X ^ 1 * C 2 - A * X ^ 2 * C 2 := by
    rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm]
    ring
  have e2 : (6 : ℚ⟦X⟧) * X = X ^ 1 * C 6 := by
    rw [show (6 : ℚ⟦X⟧) = C 6 from (map_ofNat C 6).symm]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | n
  · simp
  · simp [a_one]
  · simp [a_one, a_two] <;> norm_num
  · have h := a_rec' n
    have hq : ((a (n + 3) : ℕ) : ℚ) = 2 * a (n + 2) + 2 * a (n + 1) := by exact_mod_cast h
    simp only [show ¬ (n + 3 = 0) by omega, show ¬ (n + 3 - 1 = 0) by omega, if_false,
      show 1 ≤ n + 3 by omega, show 2 ≤ n + 3 by omega, if_true, show ¬ (n + 3 = 1) by omega,
      show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega,
      show ¬ (n + 2 = 0) by omega, show ¬ (n + 1 = 0) by omega]
    linear_combination hq

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
    Real.sqrt 3 * ((1 + Real.sqrt 3) ^ n - (1 - Real.sqrt 3) ^ n) := by
  have s2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set F : ℕ → ℝ := fun n => Real.sqrt 3 * ((1 + Real.sqrt 3) ^ n - (1 - Real.sqrt 3) ^ n) with hF
  have Frec : ∀ n, F (n + 2) = 2 * F (n + 1) + 2 * F n := by
    intro n
    simp only [hF]
    have h1 : (1 + Real.sqrt 3) ^ 2 = 2 * (1 + Real.sqrt 3) + 2 := by linear_combination s2
    have h2 : (1 - Real.sqrt 3) ^ 2 = 2 * (1 - Real.sqrt 3) + 2 := by linear_combination s2
    rw [show (1 + Real.sqrt 3) ^ (n + 2) = (1 + Real.sqrt 3) ^ n * (1 + Real.sqrt 3) ^ 2 by ring,
      show (1 - Real.sqrt 3) ^ (n + 2) = (1 - Real.sqrt 3) ^ n * (1 - Real.sqrt 3) ^ 2 by ring,
      h1, h2]
    ring
  have F1 : F 1 = 6 := by
    simp only [hF]
    linear_combination 2 * s2
  have F2 : F 2 = 12 := by
    simp only [hF]
    linear_combination 4 * s2
  have key : ∀ k, (a (k + 1) : ℝ) = F (k + 1) ∧ (a (k + 2) : ℝ) = F (k + 2) := by
    intro k
    induction k with
    | zero => exact ⟨by rw [a_one, F1]; norm_num, by rw [a_two, F2]; norm_num⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 2 = k + 3 from rfl, a_rec', show k + 3 = (k + 1) + 2 from rfl, Frec]
      push_cast
      rw [ih.1, ih.2]
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (key k).1

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 2 * X - 2 * X ^ 2) = 6 * X ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      Real.sqrt 3 * ((1 + Real.sqrt 3) ^ n - (1 - Real.sqrt 3) ^ n) :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..12). -/
theorem controls : a 1 = 6 ∧ a 2 = 12 ∧ a 3 = 36 ∧ a 4 = 96 ∧ a 5 = 264 ∧ a 6 = 720 ∧
    a 7 = 1968 ∧ a 8 = 5376 ∧ a 9 = 14688 ∧ a 10 = 40128 ∧ a 11 = 109632 ∧ a 12 = 299520 := by
  have r0 := a_rec' 0; have r1 := a_rec' 1; have r2 := a_rec' 2; have r3 := a_rec' 3
  have r4 := a_rec' 4; have r5 := a_rec' 5; have r6 := a_rec' 6; have r7 := a_rec' 7
  have r8 := a_rec' 8; have r9 := a_rec' 9
  have h1 := a_one; have h2 := a_two
  norm_num at r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  omega

/-- Control by direct enumeration of all 729 arrays with three rows: a(2) = 12. -/
theorem control_direct : ((univ : Finset (Fin 3 → Fin 2 → Fin 3)).filter good).card = 12 := by
  decide +kernel

end OMA.S_oeis_a239171

theorem OMA.solution : type_of% @OMA.S_oeis_a239171.main :=
  OMA.S_oeis_a239171.conjecture
